mod output;

#[cfg(test)]
mod tests;

use std::cmp::max;
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read};
use std::path::Path;

use chumsky::error::Rich;
use tracing::{event, span, Level};

use super::ast::*;
use super::eval::extract_final_equalities;
use super::eval::RcBlock;
use super::lexer;
use super::listing::*;
use super::parser::parse_source_file;
use super::span::*;
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::symtab::{
    assign_default_rc_word_tags, BadSymbolDefinition, FinalSymbolDefinition, FinalSymbolTable,
    FinalSymbolType, LookupOperation, SymbolDefinition, SymbolTable,
};
use super::types::*;
use base::prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit};
pub use output::write_user_program;

#[cfg(test)]
use base::charset::Script;
#[cfg(test)]
use base::u36;

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

impl SourceFile {
    fn into_directive(self, symtab: &mut SymbolTable) -> Result<Directive, AssemblerFailure> {
        type MemoryMap = BTreeMap<BlockIdentifier, (Option<Origin>, LocatedBlock)>;

        fn assign_block_positions(
            blocks: BTreeMap<BlockIdentifier, Block>,
            symtab: &mut SymbolTable,
        ) -> Result<MemoryMap, AssemblerFailure> {
            let mut no_rc_block = NoRcBlock {};
            let mut memory_map: BTreeMap<BlockIdentifier, (Option<Origin>, LocatedBlock)> =
                BTreeMap::new();

            for (block_id, directive_block) in blocks.into_iter() {
                let mut op = LookupOperation::default();
                let address: Address =
                    match symtab.finalise_origin(block_id, &mut no_rc_block, Some(&mut op)) {
                        Ok(a) => a,
                        Err(_) => {
                            return Err(AssemblerFailure::InternalError(format!(
                                "starting address for {block_id} was not calculated"
                            )));
                        }
                    };

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

                memory_map.insert(
                    block_id,
                    (
                        directive_block.origin.clone(),
                        LocatedBlock {
                            location: address,
                            statements: directive_block.statements,
                        },
                    ),
                );
            }

            Ok(memory_map)
        }

        let SourceFile {
            punch,
            blocks: input_blocks,
            equalities,
            macros: _,
        } = self;
        let mut output_blocks = BTreeMap::new();
        let mut block_default_location: Address = Origin::default_address();

        for (block_id, mblock) in input_blocks
            .iter()
            .enumerate()
            .map(|(id, b)| (BlockIdentifier::from(id), b))
        {
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
            output_blocks.insert(
                block_id,
                Block {
                    origin: mblock.origin.clone(),
                    location,
                    statements: mblock.statements.clone(),
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

        let entry_point: Option<Address> = match punch {
            Some(PunchCommand(Some(address))) => {
                event!(
                    Level::INFO,
                    "program entry point was specified as {address:o}"
                );
                Some(address)
            }
            Some(PunchCommand(None)) => {
                event!(Level::INFO, "program entry point was not specified");
                None
            }
            None => {
                event!(
                    Level::WARN,
                    "No PUNCH directive was given, program has no start address"
                );
                None
            }
        };

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
        let directive: Directive = Directive::new(
            assign_block_positions(output_blocks, symtab)?,
            equalities,
            entry_point,
        );
        Ok(directive)
    }
}

/// Pass 1 converts the program source into an abstract syntax representation.
fn assemble_pass1<'a>(
    source_file_body: &'a str,
    errors: &mut Vec<Rich<'a, lexer::Token>>,
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
    let mut errors: Vec<Rich<'_, lexer::Token>> = Vec::new();
    let result: Result<(Option<SourceFile>, OutputOptions), AssemblerFailure> =
        assemble_pass1(input, &mut errors);
    if !errors.is_empty() {
        panic!(
            "assemble_nonempty_valid_input: for input\n{input}\nerrors were reported: {errors:?}"
        );
    }
    match result {
        Ok((None, _)) => unreachable!("parser should generate output if there are no errors"),
        Ok((Some(source_file), _options)) => {
            let p2output = assemble_pass2(source_file, input)
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
pub struct BinaryChunk {
    pub address: Address,
    pub words: Vec<Unsigned36Bit>,
}

impl BinaryChunk {
    pub fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    fn count_words(&self) -> usize {
        self.words.len()
    }

    pub fn push(&mut self, w: Unsigned36Bit) {
        self.words.push(w);
    }
}

impl From<RcBlock> for BinaryChunk {
    fn from(block: RcBlock) -> Self {
        BinaryChunk {
            address: block.address,
            words: block
                .words
                .into_iter()
                .map(|(_source, word)| word)
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Binary {
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

    pub fn add_chunk(&mut self, chunk: BinaryChunk) {
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
    symbols: SymbolTable,
    errors: Vec<Rich<'a, lexer::Token>>,
}

fn initial_symbol_table<'a>(
    source_file: &SourceFile,
) -> Result<SymbolTable, Vec<Rich<'a, lexer::Token>>> {
    let mut errors = Vec::new();
    let mut symtab = SymbolTable::new(source_file.blocks.iter().map(|block| {
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
fn assemble_pass2(
    source_file: SourceFile,
    source_file_body: &str,
) -> Result<Pass2Output<'_>, AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 2");
    let _enter = span.enter();

    let mut symtab = match initial_symbol_table(&source_file) {
        Ok(syms) => syms,
        Err(errors) => {
            return Err(fail_with_diagnostics(source_file_body, errors));
        }
    };

    let directive = source_file.into_directive(&mut symtab)?;
    if let Some(instruction_count) = directive
        .memory_map
        .values()
        .try_fold(Unsigned18Bit::ZERO, |acc, (_, b)| {
            acc.checked_add(b.emitted_word_count())
        })
    {
        event!(
            Level::INFO,
            "assembly pass 2 generated {instruction_count} instructions"
        );
    } else {
        return Err(AssemblerFailure::MachineLimitExceeded(
            MachineLimitExceededFailure::ProgramTooBig,
        ));
    }
    Ok(Pass2Output {
        directive: Some(directive),
        symbols: symtab,
        errors: Vec::new(),
    })
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

struct NoRcBlock {}

impl RcAllocator for NoRcBlock {
    fn allocate(
        &mut self,
        _source: RcWordSource,
        _value: Unsigned36Bit,
    ) -> Result<Address, MachineLimitExceededFailure> {
        panic!("Cannot allocate an RC-word before we know the address of the RC block");
    }
}

impl RcUpdater for NoRcBlock {
    fn update(&mut self, _address: Address, _value: Unsigned36Bit) {
        panic!("Cannot update an RC-word in an RC-block which cannot allocate words");
    }
}

/// Pass 3 generates binary code.
fn assemble_pass3(
    mut directive: Directive,
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

    let mut rcblock = RcBlock {
        address: directive.position_rc_block(),
        words: Vec::new(),
    };

    let Directive {
        mut memory_map,
        equalities,
        entry_point: _,
    } = directive;

    let mut final_symbols = FinalSymbolTable::default();

    // TODO: consider moving this into pass 2.
    for (maybe_origin, block) in memory_map.values() {
        if let Some(Origin::Symbolic(span, symbol_name)) = maybe_origin.as_ref() {
            assert!(symtab.is_defined(symbol_name));

            final_symbols.define_if_undefined(
                symbol_name.clone(),
                FinalSymbolType::Tag, // actually origin
                extract_span(body, span).trim().to_string(),
                FinalSymbolDefinition::PositionIndependent(block.location.into()),
            );
        }
    }

    extract_final_equalities(
        equalities.as_slice(),
        body,
        symtab,
        &mut rcblock,
        &mut final_symbols,
    )?;

    for (_, directive_block) in memory_map.values_mut() {
        if let Err(e) = directive_block.assign_rc_words(symtab, &mut rcblock) {
            return Err(AssemblerFailure::MachineLimitExceeded(e));
        }
    }

    if let Err(e) = assign_default_rc_word_tags(symtab, &mut rcblock, &mut final_symbols) {
        return Err(AssemblerFailure::MachineLimitExceeded(e));
    }

    // Emit the binary code.
    for (block_id, (maybe_origin, directive_block)) in memory_map.into_iter() {
        event!(
            Level::DEBUG,
            "{block_id} in output has address {0:#o} and length {1:#o}",
            directive_block.location,
            directive_block.emitted_word_count(),
        );

        if let Some(origin) = maybe_origin {
            // This is an origin (Users Handbook section 6-2.5) not a
            // tag (6-2.2).
            let span = *origin.span();
            listing.push_line(ListingLine {
                origin: Some(origin),
                span: Some(span),
                rc_source: None,
                content: None,
            });
        }

        let words = directive_block.build_binary_block(
            directive_block.location,
            symtab,
            &mut rcblock,
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

    // If the RC-word block is non-empty, emit it.
    if !rcblock.words.is_empty() {
        for (i, (rc_source, word)) in rcblock.words.iter().enumerate() {
            let address = rcblock.address.index_by(
                Unsigned18Bit::try_from(i)
                    .expect("RC block size should be limite to physical address space"),
            );

            listing.push_rc_line(ListingLine {
                origin: None,
                span: None,
                rc_source: Some(rc_source.clone()),
                content: Some((address, *word)),
            });
        }
    }
    let chunk: BinaryChunk = rcblock.into();
    if chunk.is_empty() {
        event!(
            Level::DEBUG,
            "The RC-word block is empty, and so it will not be emitted.",
        );
    } else {
        event!(
            Level::DEBUG,
            "Emitting RC-word block of length {:#o} words at address {:#o}.",
            chunk.words.len(),
            &chunk.address,
        );
        binary.add_chunk(chunk);
    }

    Ok((binary, final_symbols))
}

fn cleanup_control_chars(input: String) -> String {
    let mut output: String = String::with_capacity(input.len());
    for ch in input.chars() {
        match ch {
            '\'' | '"' => {
                output.push(ch);
            }
            ch if ch.is_control() => output.extend(ch.escape_default()),
            ch => {
                output.push(ch);
            }
        }
    }
    output
}

fn fail_with_diagnostics(
    source_file_body: &str,
    errors: Vec<Rich<lexer::Token>>,
) -> AssemblerFailure {
    match errors.as_slice() {
        [first, ..] => {
            //for e in errors.iter() {
            //    eprintln!("error: {e:?}");
            //}
            AssemblerFailure::SyntaxError {
                location: LineAndColumn::from((source_file_body, first.span())),
                msg: cleanup_control_chars(first.to_string()),
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
    let mut errors: Vec<Rich<'_, lexer::Token>> = Vec::new();
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
        mut symbols,
        errors,
    } = assemble_pass2(source_file, source_file_body)?;
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
        let (binary, final_symbols) =
            assemble_pass3(directive, &mut symbols, source_file_body, &mut listing)?;

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
fn atom_to_fragment(atom: Atom) -> InstructionFragment {
    InstructionFragment::Arithmetic(ArithmeticExpression::from(atom))
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let expected_directive_entry_point = Some(Address::new(Unsigned18Bit::from(0o26_u8)));
    let expected_block = ManuscriptBlock {
        origin: None,
        statements: vec![(
            span(0..2),
            TaggedProgramInstruction {
                tag: None,
                instructions: vec![CommaDelimitedInstruction {
                    leading_commas: None,
                    holdbit: HoldBit::Unspecified,
                    span: span(0..2),
                    instruction: UntaggedProgramInstruction {
                        fragment: atom_to_fragment(Atom::from(LiteralValue::from((
                            span(0..2),
                            Script::Normal,
                            u36!(0o14),
                        )))),
                    },
                    trailing_commas: None,
                }],
            },
        )],
    };

    let mut errors = Vec::new();
    assert_eq!(
        assemble_pass1(input, &mut errors).expect("assembly should succeed"),
        (
            Some(SourceFile {
                punch: Some(PunchCommand(expected_directive_entry_point)),
                blocks: vec![expected_block],
                equalities: Default::default(), // no equalities
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
        })?;

    let source_file_body: String = {
        let mut body = String::new();
        match BufReader::new(input_file).read_to_string(&mut body) {
            Err(e) => {
                return Err(AssemblerFailure::IoErrorOnInput {
                    filename: input_file_name.to_owned(),
                    error: e,
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
    write_user_program(&user_program, &mut writer, output_file_name)
}
