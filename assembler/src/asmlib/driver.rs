mod output;

#[cfg(test)]
mod tests;

use std::cmp::max;
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fmt::Display;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read};
#[cfg(test)]
use std::ops::Range;
use std::path::Path;

use base::subword::split_halves;
use chumsky::error::Rich;
use tracing::{event, span, Level};

use super::ast::*;
use super::eval::{BadSymbolDefinition, Evaluate, HereValue, SymbolDefinition};
use super::parser::parse_source_file;
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::symtab::{
    FinalSymbolDefinition, FinalSymbolTable, FinalSymbolType, LookupOperation, SymbolTable,
};
use super::types::*;
use base::prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit};

#[cfg(test)]
use base::charset::Script;
#[cfg(test)]
use base::u36;

const EMPTY: &str = "";

/// Represents the meta commands which are still relevant in the
/// directive.  Excludes things like the PUNCH meta command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectiveMetaCommand {
    Invalid, // e.g."☛☛BOGUS"
    BaseChange(NumeralMode),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct OutputOptions {
    // TODO: implement arguments of the LIST, PLIST, TYPE
    // metacommands.
    pub list: bool,
}

impl OutputOptions {
    fn merge(self, other: OutputOptions) -> OutputOptions {
        OutputOptions {
            list: self.list || other.list,
        }
    }
}

fn convert_source_file_to_blocks(
    source_file: &SourceFile,
    symtab: &mut SymbolTable,
) -> Result<(BTreeMap<BlockIdentifier, Block>, Option<Address>), AssemblerFailure> {
    let mut entry_point: Option<Address> = None;
    let mut blocks = BTreeMap::new();
    let mut block_default_location: Address = Origin::default_address();

    for (block_id, mblock) in source_file.blocks.iter() {
        // We still include zero-word blocks in the directive output
        // so that we don't change the block numbering.
        let len = mblock.instruction_count();
        let location: Option<Address> = match mblock.origin.as_ref() {
            None => {
                event!(
                    Level::DEBUG,
                    "Locating directive {block_id} having {len} words at default origin {block_default_location:o}",
                );
                Some(block_default_location)
            }
            Some(Origin::Literal(_, address)) => {
                event!(
                    Level::DEBUG,
                    "Locating directive {block_id} having {len} words at origin {address:o}",
                );
                Some(*address)
            }
            Some(Origin::Symbolic(span, name)) => {
                event!(
                    Level::DEBUG,
                    "Locating directive {block_id} having {len} words at symbolic location {name}, which we now known to be {block_default_location}",
                );
                if !symtab.is_defined(name) {
                    if let Err(e) = symtab.define(
                        *span,
                        name.clone(),
                        SymbolDefinition::Origin(block_default_location),
                    ) {
                        return Err(inconsistent_origin_definition(*span, name.clone(), e));
                    }
                    Some(block_default_location)
                } else {
                    None
                }
            }
        };
        blocks.insert(
            *block_id,
            Block {
                origin: mblock.origin.clone(),
                location,
                items: mblock.statements.clone(),
            },
        );
        if let Some(loc) = location {
            // Some programs could use equates or explicit origin
            // specifications to generate blocks that overlap.  From
            // my understanding of the User Handbook, such programs
            // are not rejected.  The tape loader will happily load
            // such programs.  But we don't have clear tests for such
            // cases.  We can add these if we come across programs
            // that seem to do this.
            let block_end: Address = loc.index_by(len);
            block_default_location = max(block_default_location, block_end);
        }
    }

    match source_file.punch {
        Some(PunchCommand(Some(address))) => {
            event!(
                Level::INFO,
                "program entry point was specified as {address:o}"
            );
            entry_point = Some(address);
        }
        Some(PunchCommand(None)) => {
            event!(Level::INFO, "program entry point was not specified");
        }
        None => {
            event!(
                Level::WARN,
                "No PUNCH directive was given, program has no start address"
            );
        }
    }
    // Because the PUNCH instruction causes the assembler
    // output to be punched to tape, this effectively
    // marks the end of the input.  On the real M4
    // assembler it is likely possible for there to be
    // more manuscript after the PUNCH metacommand, and
    // for this to generate a fresh reader leader and so
    // on.  But this is not supported here.  The reason we
    // don't support it is that we'd need to know the
    // answers to a lot of quesrtions we don't have
    // answers for right now.  For example, should the
    // existing program be cleared?  Should the symbol
    // table be cleared?

    Ok((blocks, entry_point))
}

/// Pass 1 converts the program source into an abstract syntax representation.
fn assemble_pass1<'a>(
    source_file_body: &'a str,
    errors: &mut Vec<Rich<'a, char>>,
) -> Result<(Option<SourceFile>, OutputOptions), AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 1");
    let _enter = span.enter();
    let options = OutputOptions { list: false };

    fn setup(state: &mut NumeralMode) {
        // Octal is actually the default numeral mode, we just call
        // set_numeral_mode here to keep Clippy happy until we
        // implement ☛☛DECIMAL and ☛☛OCTAL.
        state.set_numeral_mode(NumeralMode::Decimal); // appease Clippy
        state.set_numeral_mode(NumeralMode::Octal);
    }

    let (sf, mut new_errors) = parse_source_file(source_file_body, setup);
    errors.append(&mut new_errors);
    Ok((sf, options))
}

/// This test helper is defined here so that we don't have to expose
/// assemble_pass1, assemble_pass2.
#[cfg(test)]
pub(crate) fn assemble_nonempty_valid_input(input: &str) -> (Directive, SymbolTable) {
    let mut errors: Vec<Rich<'_, char>> = Vec::new();
    let result: Result<(Option<SourceFile>, OutputOptions), AssemblerFailure> =
        assemble_pass1(input, &mut errors);
    if !errors.is_empty() {
        panic!("assemble_nonempty_valid_input: errors were reported: {errors:?}");
    }
    match result {
        Ok((None, _)) => unreachable!("parser should generate output if there are no errors"),
        Ok((Some(source_file), _options)) => {
            let p2output = assemble_pass2(&source_file, input)
                .expect("test program should not extend beyong physical memory");
            if !p2output.errors.is_empty() {
                panic!("input should be valid: {:?}", &p2output.errors);
            }
            match p2output.directive {
                Some(directive) => (directive, p2output.symbols),
                None => {
                    panic!("assembly pass 2 generated no errors but also no output");
                }
            }
        }
        Err(e) => {
            panic!("input should be valid: {}", e);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct BinaryChunk {
    pub(crate) address: Address,
    pub(crate) words: Vec<Unsigned36Bit>,
}

impl BinaryChunk {
    fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    fn count_words(&self) -> usize {
        self.words.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct Binary {
    entry_point: Option<Address>,
    chunks: Vec<BinaryChunk>,
}

impl Binary {
    fn count_words(&self) -> usize {
        self.chunks().iter().map(|chunk| chunk.count_words()).sum()
    }

    fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }

    fn set_entry_point(&mut self, address: Address) {
        self.entry_point = Some(address)
    }

    fn add_chunk(&mut self, chunk: BinaryChunk) {
        self.chunks.push(chunk)
    }

    fn chunks(&self) -> &[BinaryChunk] {
        &self.chunks
    }

    fn is_empty(&self) -> bool {
        self.chunks.is_empty()
    }
}

struct Pass2Output<'a> {
    directive: Option<Directive>,
    origins: BTreeMap<BlockIdentifier, Option<Origin>>,
    symbols: SymbolTable,
    errors: Vec<Rich<'a, char>>,
}

fn initial_symbol_table<'a>(source_file: &SourceFile) -> Result<SymbolTable, Vec<Rich<'a, char>>> {
    let mut errors = Vec::new();
    let mut symtab = SymbolTable::new(source_file.blocks.values().map(|block| {
        let span: Span = block.origin_span();
        (span, block.origin.clone(), block.instruction_count())
    }));
    for (symbol, span, context) in source_file.global_symbol_references() {
        symtab.record_usage_context(symbol.clone(), span, context)
    }
    for (symbol, span, definition) in source_file.global_symbol_definitions() {
        match symtab.define(span, symbol.clone(), definition.clone()) {
            Ok(_) => (),
            Err(e) => {
                errors.push(Rich::custom(
                    span,
                    format!("bad symbol definition for {symbol}: {e}"),
                ));
            }
        }
    }
    if errors.is_empty() {
        Ok(symtab)
    } else {
        Err(errors)
    }
}

/// Pass 2 converts the abstract syntax representation into a
/// `Directive`, which is closer to binary code.
///
/// The source_file input is essentially an abstract syntax
/// representation.  The output is a symbol table and a "directive"
/// which is a sequence of blocks of code of known size (but not, at
/// this stage, necessarily of known position).
fn assemble_pass2<'a>(
    source_file: &SourceFile,
    source_file_body: &'a str,
) -> Result<Pass2Output<'a>, AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 2");
    let _enter = span.enter();

    let mut symtab = match initial_symbol_table(source_file) {
        Ok(syms) => syms,
        Err(errors) => {
            return Err(fail_with_diagnostics(source_file_body, errors));
        }
    };

    let (blocks, maybe_entry_point) = convert_source_file_to_blocks(source_file, &mut symtab)?;

    match blocks.values().try_fold(Unsigned18Bit::ZERO, |acc, b| {
        acc.checked_add(b.emitted_instruction_count())
    }) {
        None => {
            return Err(AssemblerFailure::MachineLimitExceeded(
                MachineLimitExceededFailure::ProgramTooBig,
            ));
        }
        Some(count) => {
            event!(
                Level::INFO,
                "assembly pass 2 generated {count} instructions"
            );
        }
    }

    // Deduce the address of every block.
    let (directive, origins): (Directive, BTreeMap<BlockIdentifier, Option<Origin>>) =
        assign_block_positions(blocks, maybe_entry_point, &mut symtab)?;

    Ok(Pass2Output {
        directive: Some(directive),
        origins,
        symbols: symtab,
        errors: Vec::new(),
    })
}

fn extract_span<'a>(body: &'a str, span: &Span) -> &'a str {
    &body[span.start..span.end]
}

#[derive(Debug)]
enum ListingLine {
    Origin(Origin),
    Instruction {
        address: Address,
        instruction: TaggedProgramInstruction,
        binary: Unsigned36Bit,
    },
}

struct ListingLineWithBody<'a> {
    line: &'a ListingLine,
    body: &'a str,
}

impl Display for ListingLineWithBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.line {
            ListingLine::Origin(origin) => {
                write!(f, "{origin}|")
            }
            ListingLine::Instruction {
                address,
                instruction,
                binary,
            } => {
                let displayed_tag: Option<&str> = instruction
                    .tag
                    .as_ref()
                    .map(|t| extract_span(self.body, &t.span));
                match displayed_tag {
                    Some(t) => {
                        write!(f, "{t:10}->")?;
                    }
                    None => {
                        write!(f, "{EMPTY:12}")?;
                    }
                }
                let displayed_instruction: &str =
                    extract_span(self.body, &instruction.instruction.span).trim();
                let (left, right) = split_halves(*binary);
                write!(f, "{displayed_instruction:30}  |{left:06} {right:06}| ")?;

                let addr_value: Unsigned18Bit = (*address).into();
                if addr_value & 0o7 == 0 {
                    write!(f, "{addr_value:>06o}")
                } else {
                    write!(f, "   {:>03o}", addr_value & 0o777)
                }
            }
        }
    }
}

#[derive(Debug, Default)]
struct Listing {
    final_symbols: FinalSymbolTable,
    output: Vec<ListingLine>,
}

impl Listing {
    fn set_final_symbols(&mut self, final_symbols: FinalSymbolTable) {
        self.final_symbols = final_symbols;
    }

    fn push_line(&mut self, line: ListingLine) {
        self.output.push(line)
    }

    fn format_symbol_table(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.final_symbols)
    }
}

struct ListingWithBody<'a> {
    listing: &'a Listing,
    body: &'a str,
}

impl Display for ListingWithBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Symbol Table:")?;
        self.listing.format_symbol_table(f)?;
        writeln!(f)?;

        writeln!(f, "Directive:")?;
        for line in self.listing.output.iter() {
            writeln!(
                f,
                "{}",
                &ListingLineWithBody {
                    line,
                    body: self.body,
                }
            )?;
        }
        Ok(())
    }
}

fn inconsistent_origin_definition(
    span: Span,
    name: SymbolName,
    e: BadSymbolDefinition,
) -> AssemblerFailure {
    AssemblerFailure::InvalidProgram {
        span,
        msg: format!("inconsistent definitions of origin {name}: {e}"),
    }
}

fn assign_block_positions(
    blocks: BTreeMap<BlockIdentifier, Block>,
    maybe_entry_point: Option<Address>,
    symtab: &mut SymbolTable,
) -> Result<(Directive, BTreeMap<BlockIdentifier, Option<Origin>>), AssemblerFailure> {
    let mut output_blocks: BTreeMap<BlockIdentifier, LocatedBlock> = BTreeMap::new();

    let mut origins: BTreeMap<BlockIdentifier, Option<Origin>> = BTreeMap::new();

    for (block_id, directive_block) in blocks.into_iter() {
        let mut op = LookupOperation::default();
        let address: Address = match symtab.finalise_origin(block_id, Some(&mut op)) {
            Ok(a) => a,
            Err(_) => {
                return Err(AssemblerFailure::InternalError(format!(
                    "starting address for {block_id} was not calculated"
                )));
            }
        };

        origins.insert(block_id, directive_block.origin.clone());

        if let Some(Origin::Symbolic(span, symbol_name)) = directive_block.origin.as_ref() {
            if !symtab.is_defined(symbol_name) {
                if let Err(e) = symtab.define(
                    *span,
                    symbol_name.clone(),
                    SymbolDefinition::Origin(address),
                ) {
                    // Inconsistent definition.
                    return Err(inconsistent_origin_definition(
                        *span,
                        symbol_name.clone(),
                        e,
                    ));
                }
            }
        }
        output_blocks.insert(
            block_id,
            LocatedBlock {
                location: address,
                items: directive_block.items,
            },
        );
    }

    Ok((Directive::new(output_blocks, maybe_entry_point), origins))
}

fn build_binary_block(
    directive_block: &LocatedBlock,
    block_id: BlockIdentifier,
    symtab: &mut SymbolTable,
    final_symbols: &mut FinalSymbolTable,
    body: &str,
    listing: &mut Listing,
) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
    let mut words: Vec<Unsigned36Bit> = Vec::with_capacity(directive_block.items.len());
    for (offset, statement) in directive_block.items.iter().enumerate() {
        let bad_offset = || {
            AssemblerFailure::MachineLimitExceeded(MachineLimitExceededFailure::BlockTooLarge {
                block_id,
                block_origin: directive_block.location,
                offset,
            })
        };
        let here: Address = if let Ok(h) = Unsigned18Bit::try_from(offset)
            .map_err(|_| ())
            .and_then(|n| offset_from_origin(&directive_block.location, n).map_err(|_| ()))
        {
            h
        } else {
            return Err(bad_offset());
        };

        match statement {
            Statement::Assignment(span, symbol, definition) => {
                let mut op = Default::default();
                let value = definition
                    .evaluate(&HereValue::Address(here), symtab, &mut op)
                    .expect("lookup on FinalSymbolTable is infallible");
                final_symbols.define(
                    symbol.clone(),
                    FinalSymbolDefinition::new(
                        value,
                        FinalSymbolType::Equality,
                        extract_span(body, span).trim().to_string(),
                    ),
                );
            }
            Statement::Instruction(inst) => {
                if let Some(tag) = inst.tag.as_ref() {
                    final_symbols.define(
                        tag.name.clone(),
                        FinalSymbolDefinition::new(
                            here.into(),
                            FinalSymbolType::Tag,
                            extract_span(body, &tag.span).trim().to_string(),
                        ),
                    );
                }

                let mut op = Default::default();
                let word = inst
                    .evaluate(&HereValue::Address(here), symtab, &mut op)
                    .expect("lookup on FinalSymbolTable is infallible");

                listing.push_line(ListingLine::Instruction {
                    address: here,
                    instruction: inst.clone(),
                    binary: word,
                });
                words.push(word);
            }
        }
    }
    Ok(words)
}

/// Pass 3 generates binary code.
fn assemble_pass3(
    directive: Directive,
    origins: BTreeMap<BlockIdentifier, Option<Origin>>,
    symtab: &mut SymbolTable,
    body: &str,
    listing: &mut Listing,
) -> Result<(Binary, FinalSymbolTable), AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 3");
    let _enter = span.enter();

    let mut binary = Binary::default();
    if let Some(address) = directive.entry_point() {
        binary.set_entry_point(address);
    }

    let mut final_symbols = FinalSymbolTable::default();

    for (block_id, block) in directive.blocks() {
        if let Some(Some(Origin::Symbolic(span, symbol_name))) = origins.get(block_id) {
            assert!(symtab.is_defined(symbol_name));

            final_symbols.define_if_undefined(
                symbol_name.clone(),
                FinalSymbolDefinition::new(
                    block.location.into(),
                    FinalSymbolType::Tag, // actually origin
                    extract_span(body, span).trim().to_string(),
                ),
            );
        }
    }

    // Emit the binary code.
    for (block_id, directive_block) in directive.blocks() {
        event!(
            Level::DEBUG,
            "{block_id} in output has address {0:#o} and length {1:#o}",
            directive_block.location,
            directive_block.items.len(),
        );

        if let Some(Some(origin)) = origins.get(block_id) {
            // This is an origin (Users Handbook section 6-2.5)
            // not a tag (6-2.2).
            listing.push_line(ListingLine::Origin(origin.clone()));
        }

        let words = build_binary_block(
            directive_block,
            *block_id,
            symtab,
            &mut final_symbols,
            body,
            listing,
        )?;
        if words.is_empty() {
            event!(
                Level::DEBUG,
                "{block_id} will not be included in the output because it is empty"
            );
        } else {
            binary.add_chunk(BinaryChunk {
                address: directive_block.location,
                words,
            });
        };
    }

    final_symbols.check_all_defined(&*symtab);

    Ok((binary, final_symbols))
}

fn pos_line_column(s: &str, pos: usize) -> Result<(usize, usize), ()> {
    let mut line = 1;
    let mut column = 1;
    for (i, ch) in s.chars().enumerate() {
        if i == pos {
            return Ok((line, column));
        }
        match ch {
            '\n' => {
                column = 1;
                line += 1;
            }
            _ => {
                column += 1;
            }
        }
    }
    Err(())
}

fn fail_with_diagnostics(source_file_body: &str, errors: Vec<Rich<char>>) -> AssemblerFailure {
    match errors.as_slice() {
        [first, ..] => {
            for e in errors.iter() {
                eprintln!("{}", e);
            }
            let (line, column) = pos_line_column(source_file_body, first.span().start)
                .expect("span for error message should be inside the file");
            AssemblerFailure::SyntaxError {
                line: line as u32,
                column: Some(column),
                msg: first.to_string(),
            }
        }
        [] => {
            unreachable!("should not be called if errors is empty")
        }
    }
}

pub(crate) fn assemble_source(
    source_file_body: &str,
    mut options: OutputOptions,
) -> Result<Binary, AssemblerFailure> {
    let mut errors = Vec::new();
    let (source_file, source_options) = assemble_pass1(source_file_body, &mut errors)?;
    if !errors.is_empty() {
        return Err(fail_with_diagnostics(source_file_body, errors));
    }
    options = options.merge(source_options);

    let source_file =
        source_file.expect("assembly pass1 generated no errors, an AST should have been returned");

    // Now we do pass 2.
    let Pass2Output {
        directive,
        origins,
        mut symbols,
        errors,
    } = assemble_pass2(&source_file, source_file_body)?;
    if !errors.is_empty() {
        return Err(fail_with_diagnostics(source_file_body, errors));
    }
    let directive = match directive {
        None => {
            return Err(AssemblerFailure::InternalError(
                "assembly pass 2 generated no errors, so it should have generated ouptut code (even if empty)".to_string()
            ));
        }
        Some(d) => d,
    };

    // Now we do pass 3, which generates the binary output
    let binary = {
        let mut listing = Listing::default();
        let (binary, final_symbols) = assemble_pass3(
            directive,
            origins,
            &mut symbols,
            source_file_body,
            &mut listing,
        )?;

        listing.set_final_symbols(final_symbols);
        if options.list {
            println!(
                "{0}",
                ListingWithBody {
                    listing: &listing,
                    body: source_file_body,
                }
            );
        }
        binary
    };

    event!(
        Level::INFO,
        "assembly pass 3 generated {} words of binary output (not counting the reader leader)",
        binary.count_words()
    );
    Ok(binary)
}

#[cfg(test)]
fn span(range: Range<usize>) -> Span {
    Span::from(range)
}

#[cfg(test)]
fn atom_to_fragment(atom: Atom) -> InstructionFragment {
    InstructionFragment::Arithmetic(ArithmeticExpression::from(atom))
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let expected_directive_entry_point = Some(Address::new(Unsigned18Bit::from(0o26_u8)));
    let expected_block = ManuscriptBlock {
        origin: None,
        statements: vec![Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instruction: UntaggedProgramInstruction {
                span: span(0..2),
                holdbit: HoldBit::Unspecified,
                parts: vec![atom_to_fragment(Atom::Literal(LiteralValue::from((
                    span(0..2),
                    Script::Normal,
                    u36!(0o14),
                ))))],
            },
        })],
    };

    let mut errors = Vec::new();
    assert_eq!(
        assemble_pass1(input, &mut errors).expect("assembly should succeed"),
        (
            Some(SourceFile {
                punch: Some(PunchCommand(expected_directive_entry_point)),
                blocks: {
                    let mut m = BTreeMap::new();
                    m.insert(BlockIdentifier::Number(0), expected_block);
                    m
                },
                macros: Vec::new(),
            }),
            OutputOptions { list: false }
        )
    );
    assert!(errors.is_empty());
}

pub fn assemble_file(
    input_file_name: &OsStr,
    output_file_name: &Path,
    options: OutputOptions,
) -> Result<(), AssemblerFailure> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnInput {
            filename: input_file_name.to_owned(),
            error: e,
            line_number: None,
        })?;

    let source_file_body: String = {
        let mut body = String::new();
        match BufReader::new(input_file).read_to_string(&mut body) {
            Err(e) => {
                return Err(AssemblerFailure::IoErrorOnInput {
                    filename: input_file_name.to_owned(),
                    error: e,
                    line_number: None,
                })
            }
            Ok(_) => body,
        }
    };

    let user_program: Binary = assemble_source(&source_file_body, options)?;

    // The Users Guide explains on page 6-23 how the punched binary
    // is created (and read back in).
    let output_file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(output_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnOutput {
            filename: output_file_name.to_owned(),
            error: e,
        })?;
    let mut writer = BufWriter::new(output_file);
    output::write_user_program(&user_program, &mut writer, output_file_name)
}
