mod output;

#[cfg(test)]
mod tests;

use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read};
use std::path::{Path, PathBuf};

use chumsky::error::Rich;
use tracing::{event, span, Level};

use super::ast::*;
use super::eval::extract_final_equalities;
use super::eval::Evaluate;
use super::eval::HereValue;
use super::eval::{EvaluationContext, RcBlock};
use super::lexer;
use super::listing::*;
use super::parser::parse_source_file;
use super::span::*;
use super::state::{NumeralMode, State};
use super::symbol::SymbolName;
use super::symtab::{
    assign_default_rc_word_tags, BadSymbolDefinition, BlockPosition, FinalSymbolDefinition,
    FinalSymbolTable, FinalSymbolType, IndexRegisterAssigner, MemoryMap, SymbolTable,
};
use super::types::*;
use base::prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit};
use base::subword;
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
    fn into_directive(self, mem_map: &MemoryMap) -> Result<Directive, AssemblerFailure> {
        let SourceFile {
            punch,
            blocks: input_blocks,
            equalities,
            macros: _,
        } = self;
        let output_blocks: BTreeMap<BlockIdentifier, LocatedBlock> = input_blocks
            .into_iter()
            .enumerate()
            .map(|(id, mblock)| (BlockIdentifier::from(id), mblock))
            .map(|(block_id, mblock)| {
                let location: Address = match mem_map.get(&block_id).map(|pos| pos.block_address) {
                    Some(Some(addr)) => addr,
                    None => unreachable!("unknown block {block_id} in input_blocks"),
                    Some(None) => unreachable!(
                        "block location for {block_id} should already have been determined"
                    ),
                };
                (
                    block_id,
                    LocatedBlock {
                        origin: mblock.origin,
                        location,
                        statements: mblock.statements,
                    },
                )
            })
            .collect();

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
        // answers to a lot of questions we don't have
        // answers for right now.  For example, should the
        // existing program be cleared?  Should the symbol
        // table be cleared?
        Ok(Directive::new(output_blocks, equalities, entry_point))
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

    fn setup(state: &mut State) {
        // Octal is actually the default numeral mode, we just call
        // set_numeral_mode here to keep Clippy happy until we
        // implement ☛☛DECIMAL and ☛☛OCTAL.
        state.numeral_mode.set_numeral_mode(NumeralMode::Decimal); // appease Clippy
        state.numeral_mode.set_numeral_mode(NumeralMode::Octal);
    }

    let (sf, mut new_errors) = parse_source_file(source_file_body, setup);
    errors.append(&mut new_errors);
    Ok((sf, options))
}

/// This test helper is defined here so that we don't have to expose
/// assemble_pass1, assemble_pass2.
#[cfg(test)]
pub(crate) fn assemble_nonempty_valid_input(
    input: &str,
) -> (Directive, SymbolTable, MemoryMap, IndexRegisterAssigner) {
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
                Some(directive) => (
                    directive,
                    p2output.symbols,
                    p2output.memory_map,
                    p2output.index_register_assigner,
                ),
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
    memory_map: MemoryMap,
    index_register_assigner: IndexRegisterAssigner,
    errors: Vec<Rich<'a, lexer::Token>>,
}

fn initial_symbol_table<'a>(
    source_file: &SourceFile,
) -> Result<SymbolTable, Vec<Rich<'a, lexer::Token>>> {
    let mut errors = Vec::new();
    let mut symtab = SymbolTable::new();
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

    let mut memory_map = MemoryMap::new(source_file.blocks.iter().map(|block| {
        let span: Span = block.origin_span();
        (span, block.origin.clone(), block.instruction_count())
    }));
    let mut symtab = match initial_symbol_table(&source_file) {
        Ok(syms) => syms,
        Err(errors) => {
            return Err(AssemblerFailure::BadProgram(fail_with_diagnostics(
                source_file_body,
                errors,
            )));
        }
    };
    let mut index_register_assigner: IndexRegisterAssigner = IndexRegisterAssigner::default();
    let mut no_rc_allocation = NoRcBlock {
        why_blocked: "we don't expect origin computation to require RC-word allocation",
    };
    let mut assigned_block_addresses: BTreeMap<BlockIdentifier, Address> = Default::default();
    let tmp_blocks: Vec<(BlockIdentifier, BlockPosition)> = memory_map
        .iter()
        .map(|(block_identifier, block_position)| (*block_identifier, block_position.clone()))
        .collect();

    for (block_identifier, block_position) in tmp_blocks.into_iter() {
        let mut ctx = EvaluationContext {
            symtab: &mut symtab,
            memory_map: &memory_map,
            here: HereValue::NotAllowed,
            index_register_assigner: &mut index_register_assigner,
            rc_updater: &mut no_rc_allocation,
            lookup_operation: Default::default(),
        };
        match (&block_identifier, &block_position).evaluate(&mut ctx) {
            Ok(value) => {
                if !ctx.index_register_assigner.is_empty() {
                    return Err(AssemblerFailure::InternalError(
                        format!(
                            "While determining the addresses of {block_identifier}, we assigned an index register.  Block origins should not depend on index registers")));
                }

                let address: Address = subword::right_half(value).into();
                assigned_block_addresses.insert(block_identifier, address);
            }
            Err(e) => {
                let prog_error: ProgramError = e.into_program_error();
                return Err(prog_error.into_assembler_failure(source_file_body));
            }
        }
    }

    for (block_id, address) in assigned_block_addresses.into_iter() {
        memory_map.set_block_position(block_id, address);
    }

    let directive = source_file.into_directive(&memory_map)?;
    if let Some(instruction_count) = directive
        .blocks
        .values()
        .try_fold(Unsigned18Bit::ZERO, |acc, b| {
            acc.checked_add(b.emitted_word_count())
        })
    {
        event!(
            Level::INFO,
            "assembly pass 2 generated {instruction_count} instructions"
        );
    }
    Ok(Pass2Output {
        directive: Some(directive),
        symbols: symtab,
        memory_map,
        index_register_assigner,
        errors: Vec::new(),
    })
}

struct NoRcBlock {
    why_blocked: &'static str,
}

impl RcAllocator for NoRcBlock {
    fn allocate(
        &mut self,
        _source: RcWordSource,
        _value: Unsigned36Bit,
    ) -> Result<Address, RcWordAllocationFailure> {
        panic!(
            "Cannot allocate an RC-word before we know the address of the RC block: {}",
            self.why_blocked
        );
    }
}

impl RcUpdater for NoRcBlock {
    fn update(&mut self, _address: Address, _value: Unsigned36Bit) {
        panic!(
            "Cannot update an RC-word in an RC-block which cannot allocate words: {}",
            self.why_blocked
        );
    }
}

/// Pass 3 generates binary code.
fn assemble_pass3(
    mut directive: Directive,
    symtab: &mut SymbolTable,
    memory_map: &mut MemoryMap,
    index_register_assigner: &mut IndexRegisterAssigner,
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
        mut blocks,
        equalities,
        entry_point: _,
    } = directive;

    let mut final_symbols = FinalSymbolTable::default();
    let mut undefined_symbols: BTreeMap<SymbolName, Span> = Default::default();
    // TODO: consider moving this into pass 2.
    for block in blocks.values() {
        if let Some(Origin::Symbolic(span, symbol_name)) = block.origin.as_ref() {
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
        memory_map,
        index_register_assigner,
        &mut rcblock,
        &mut final_symbols,
        &mut undefined_symbols,
    )?;

    let convert_rc_failure = |e: RcWordAllocationFailure| -> AssemblerFailure {
        match e {
            RcWordAllocationFailure::RcBlockTooBig { source, .. } => {
                let span: Span = source.span();
                let location: LineAndColumn = LineAndColumn::from((body, &span));
                AssemblerFailure::BadProgram(vec![WithLocation {
                    location,
                    inner: ProgramError::RcBlockTooLong {
                        rc_word_source: source,
                        rc_word_span: span,
                    },
                }])
            }
            RcWordAllocationFailure::InconsistentTag(
                ref e @ BadSymbolDefinition::Incompatible(ref name, span, _, _),
            ) => {
                let location: LineAndColumn = LineAndColumn::from((body, &span));
                AssemblerFailure::BadProgram(vec![WithLocation {
                    location,
                    inner: ProgramError::InconsistentTag {
                        name: name.clone(),
                        span,
                        msg: e.to_string(),
                    },
                }])
            }
        }
    };

    for directive_block in blocks.values_mut() {
        if let Err(e) = directive_block.assign_rc_words(symtab, &mut rcblock) {
            return Err(convert_rc_failure(e));
        }
    }

    if let Err(e) = assign_default_rc_word_tags(symtab, &mut rcblock, &mut final_symbols) {
        return Err(convert_rc_failure(e));
    }

    // Emit the binary code.
    for (block_id, directive_block) in blocks.into_iter() {
        event!(
            Level::DEBUG,
            "{block_id} in output has address {0:#o} and length {1:#o}",
            directive_block.location,
            directive_block.emitted_word_count(),
        );
        if let Some(origin) = directive_block.origin.clone() {
            // This is an origin (Users Handbook section 6-2.5) not a
            // tag (6-2.2).
            let span = origin.span();
            listing.push_line(ListingLine {
                span: Some(span),
                rc_source: None,
                content: None,
            });
        }

        let words = directive_block.build_binary_block(
            directive_block.location,
            symtab,
            memory_map,
            index_register_assigner,
            &mut rcblock,
            &mut final_symbols,
            body,
            listing,
            &mut undefined_symbols,
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

    if !undefined_symbols.is_empty() {
        return Err(AssemblerFailure::BadProgram(
            undefined_symbols
                .into_iter()
                .map(|(name, span)| {
                    let e = ProgramError::UnexpectedlyUndefinedSymbol { name, span };
                    (body, e).into()
                })
                .collect(),
        ));
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
) -> Vec<WithLocation<ProgramError>> {
    errors
        .into_iter()
        .map(|e| {
            let syntax_error = ProgramError::SyntaxError {
                span: *e.span(),
                msg: cleanup_control_chars(e.to_string()),
            };
            (source_file_body, syntax_error).into()
        })
        .collect()
}

pub(crate) fn assemble_source(
    source_file_body: &str,
    mut options: OutputOptions,
) -> Result<Binary, AssemblerFailure> {
    let mut errors: Vec<Rich<'_, lexer::Token>> = Vec::new();
    let (source_file, source_options) = assemble_pass1(source_file_body, &mut errors)?;
    if !errors.is_empty() {
        return Err(AssemblerFailure::BadProgram(fail_with_diagnostics(
            source_file_body,
            errors,
        )));
    }
    options = options.merge(source_options);

    let source_file =
        source_file.expect("assembly pass1 generated no errors, an AST should have been returned");

    // Now we do pass 2.
    let Pass2Output {
        directive,
        mut symbols,
        mut memory_map,
        mut index_register_assigner,
        errors,
    } = assemble_pass2(source_file, source_file_body)?;
    if !errors.is_empty() {
        return Err(AssemblerFailure::BadProgram(fail_with_diagnostics(
            source_file_body,
            errors,
        )));
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
            &mut symbols,
            &mut memory_map,
            &mut index_register_assigner,
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
fn atom_to_fragment(atom: Atom) -> InstructionFragment {
    InstructionFragment::Arithmetic(ArithmeticExpression::from(atom))
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let expected_directive_entry_point = Some(Address::new(Unsigned18Bit::from(0o26_u8)));
    let expected_block = ManuscriptBlock {
        origin: None,
        statements: vec![TaggedProgramInstruction {
            span: span(0..2),
            tags: Vec::new(),
            instruction: UntaggedProgramInstruction::from(vec![CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(0..2),
                fragment: atom_to_fragment(Atom::from(LiteralValue::from((
                    span(0..2),
                    Script::Normal,
                    u36!(0o14),
                )))),
                trailing_commas: None,
            }]),
        }]
        .into(),
    };

    let mut errors = Vec::new();
    assert_eq!(
        assemble_pass1(input, &mut errors).expect("assembly should succeed"),
        (
            Some(SourceFile {
                punch: Some(PunchCommand(expected_directive_entry_point)),
                blocks: vec![expected_block],
                equalities: Default::default(), // no equalities
                macros: Default::default(),
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
        .map_err(|e| {
            AssemblerFailure::Io(IoFailed {
                action: IoAction::Read,
                target: IoTarget::File(PathBuf::from(input_file_name)),
                error: e,
            })
        })?;

    let source_file_body: String = {
        let mut body = String::new();
        match BufReader::new(input_file).read_to_string(&mut body) {
            Err(e) => {
                return Err(AssemblerFailure::Io(IoFailed {
                    action: IoAction::Read,
                    target: IoTarget::File(PathBuf::from(input_file_name)),
                    error: e,
                }));
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
        .map_err(|e| {
            AssemblerFailure::Io(IoFailed {
                action: IoAction::Write,
                target: IoTarget::File(PathBuf::from(output_file_name)),
                error: e,
            })
        })?;
    let mut writer = BufWriter::new(output_file);
    write_user_program(&user_program, &mut writer, output_file_name)
}
