mod output;

#[cfg(test)]
mod tests;

use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read};
use std::path::{Path, PathBuf};

use chumsky::error::Rich;
use tracing::{Level, event, span};

use super::ast::*;
use super::collections::OneOrMore;
use super::directive::Directive;
use super::eval::Evaluate;
use super::eval::HereValue;
use super::eval::{EvaluationContext, RcBlock, extract_final_equalities};
use super::lexer;
use super::listing::*;
#[cfg(test)]
use super::manuscript::ManuscriptBlock;
#[cfg(test)]
use super::manuscript::PunchCommand;
use super::manuscript::SourceFile;
use super::memorymap::{
    BlockPosition, MemoryMap, RcAllocator, RcWordAllocationFailure, RcWordSource,
};
use super::parser::parse_source_file;
use super::source::Source;
use super::source::{LineAndColumn, WithLocation};
use super::span::*;
use super::state::{NumeralMode, State};
use super::symbol::SymbolName;
use super::symtab::{
    ExplicitSymbolTable, FinalSymbolDefinition, FinalSymbolTable, FinalSymbolType,
    ImplicitSymbolTable, IndexRegisterAssigner, assign_default_rc_word_tags,
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

/// Pass 1 converts the program source into an abstract syntax representation.
fn assemble_pass1<'a, 'b: 'a>(
    source_file_body: &'b Source<'a>,
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

    let (mut sf, mut new_errors) = parse_source_file(source_file_body.as_str(), setup);
    errors.append(&mut new_errors);

    if let Some(source_file) = sf.as_mut()
        && let Err(tag_errors) = source_file.build_local_symbol_tables()
    {
        errors.extend(
            tag_errors
                .into_iter()
                .map(|tag_err| Rich::custom(tag_err.span(), tag_err.to_string())),
        );
    }
    Ok((sf, options))
}

#[derive(Debug, PartialEq, Eq)]
enum AssemblerPass1Or2Output<'a> {
    Pass1Failed(Result<OneOrMore<Rich<'a, lexer::Token>>, AssemblerFailure>),
    Pass2Failed(AssemblerFailure),
    Success(Vec<Rich<'a, lexer::Token>>, OutputOptions, Pass2Output<'a>),
}

fn assemble_nonempty_input<'a, 'b: 'a>(input: &'b Source<'a>) -> AssemblerPass1Or2Output<'a> {
    let mut errors: Vec<Rich<'_, lexer::Token>> = Vec::new();
    match assemble_pass1(input, &mut errors) {
        Err(e) => AssemblerPass1Or2Output::Pass1Failed(Err(e)),
        Ok((None, _output_options)) => match OneOrMore::try_from_vec(errors) {
            Ok(errors) => AssemblerPass1Or2Output::Pass1Failed(Ok(errors)),
            Err(_) => {
                unreachable!(
                    "assemble_pass1 returned no SourceFile instance but there were no output errors either"
                );
            }
        },
        Ok((Some(source_file), output_options)) => match assemble_pass2(source_file, input) {
            Err(e) => AssemblerPass1Or2Output::Pass2Failed(e),
            Ok(p2output) => AssemblerPass1Or2Output::Success(errors, output_options, p2output),
        },
    }
}

/// This test helper is defined here so that we don't have to expose
/// assemble_pass1, assemble_pass2.
#[cfg(test)]
pub(crate) fn assemble_nonempty_valid_input(
    input: &str,
) -> (
    Directive,
    ExplicitSymbolTable,
    ImplicitSymbolTable,
    MemoryMap,
    IndexRegisterAssigner,
) {
    let input_source = Source::new(input);
    match assemble_nonempty_input(&input_source) {
        AssemblerPass1Or2Output::Pass1Failed(Err(e)) => {
            panic!("pass 1 failed with an error result: {e}");
        }
        AssemblerPass1Or2Output::Pass1Failed(Ok(errors)) => {
            panic!("pass 1 failed with diagnostics: {errors:?}");
        }
        AssemblerPass1Or2Output::Pass2Failed(e) => {
            panic!("pass 1 failed with an error result: {e}");
        }
        AssemblerPass1Or2Output::Success(errors, _output_options, p2output) => {
            if errors.is_empty() {
                match p2output {
                    Pass2Output {
                        directive: None, ..
                    } => {
                        panic!("directive is None but no errors were reported");
                    }
                    Pass2Output {
                        directive: Some(directive),
                        explicit_symbols,
                        implicit_symbols,
                        memory_map,
                        index_register_assigner,
                        errors,
                    } => {
                        if !errors.is_empty() {
                            panic!("input should be valid: {:?}", &errors);
                        } else {
                            (
                                directive,
                                explicit_symbols,
                                implicit_symbols,
                                memory_map,
                                index_register_assigner,
                            )
                        }
                    }
                }
            } else {
                panic!("pass 2 failed with diagnostics: {errors:?}");
            }
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

#[derive(Debug, PartialEq, Eq)]
struct Pass2Output<'a> {
    directive: Option<Directive>,
    explicit_symbols: ExplicitSymbolTable,
    implicit_symbols: ImplicitSymbolTable,
    memory_map: MemoryMap,
    index_register_assigner: IndexRegisterAssigner, // not cloneable
    errors: Vec<Rich<'a, lexer::Token>>,
}

fn initial_symbol_table<'a>(
    source_file: &SourceFile,
) -> Result<(ExplicitSymbolTable, ImplicitSymbolTable), OneOrMore<Rich<'a, lexer::Token>>> {
    let mut errors = Vec::new();
    // TODO: split these out into separate functions.
    let mut explicit_symbols = ExplicitSymbolTable::new();
    // All explicit definitions in the program take effect either
    // locally (for the bodies of macro expansions) or globally (for
    // everything else).  So, before we can enumerate all global
    // symbol references, we need to identidy which symbol references
    // are references to something defined in a local scope.  And so
    // we need to enumerate definitions before references.
    for r in source_file.global_symbol_definitions() {
        match r {
            Ok((symbol, span, definition)) => {
                match explicit_symbols.define(symbol.clone(), definition.clone()) {
                    Ok(_) => (),
                    Err(e) => {
                        errors.push(Rich::custom(
                            span,
                            format!("bad symbol definition for {symbol}: {e}"),
                        ));
                    }
                }
            }
            Err(e) => {
                let span: Span = e.span();
                errors.push(Rich::custom(span, e.to_string()));
            }
        }
    }
    let mut implicit_symbols = ImplicitSymbolTable::default();
    for r in source_file.global_symbol_references() {
        match r {
            Ok((symbol, span, context)) => {
                if !explicit_symbols.is_defined(&symbol)
                    && let Err(e) = implicit_symbols.record_usage_context(symbol.clone(), context)
                {
                    errors.push(Rich::custom(span, e.to_string()));
                }
            }
            Err(e) => {
                let span: Span = e.span();
                errors.push(Rich::custom(span, e.to_string()));
            }
        }
    }
    match OneOrMore::try_from_vec(errors) {
        Ok(errors) => Err(errors),
        Err(_) => Ok((explicit_symbols, implicit_symbols)),
    }
}

/// Pass 2 converts the abstract syntax representation into a
/// `Directive`, which is closer to binary code.
///
/// The source_file input is essentially an abstract syntax
/// representation.  The output is a symbol table and a "directive"
/// which is a sequence of blocks of code of known position and size
/// (but the contents of which are not yet populated).
fn assemble_pass2<'s>(
    source_file: SourceFile,
    source_file_body: &Source<'s>,
) -> Result<Pass2Output<'s>, AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 2");
    let _enter = span.enter();

    let mut memory_map = MemoryMap::new(source_file.blocks.iter().map(|block| {
        let span: Span = block.origin_span();
        (span, block.origin.clone(), block.instruction_count())
    }));

    let (mut explicit_symbols, mut implicit_symbols) = match initial_symbol_table(&source_file) {
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
    let tmp_blocks: Vec<BlockPosition> = memory_map.iter().cloned().collect();
    for block_position in tmp_blocks.into_iter() {
        let mut ctx = EvaluationContext {
            explicit_symtab: &mut explicit_symbols,
            implicit_symtab: &mut implicit_symbols,
            memory_map: &memory_map,
            here: HereValue::NotAllowed,
            index_register_assigner: &mut index_register_assigner,
            rc_updater: &mut no_rc_allocation,
            lookup_operation: Default::default(),
        };
        match block_position.evaluate(&mut ctx) {
            Ok(value) => {
                if !ctx.index_register_assigner.is_empty() {
                    return Err(AssemblerFailure::InternalError(format!(
                        "While determining the addresses of {0}, we assigned an index register.  Block origins should not depend on index registers",
                        &block_position.block_identifier
                    )));
                }

                let address: Address = subword::right_half(value).into();
                memory_map.set_block_position(block_position.block_identifier, address);
            }
            Err(e) => {
                let prog_error: ProgramError = e.into_program_error();
                return Err(prog_error.into_assembler_failure(source_file_body));
            }
        }
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
        explicit_symbols,
        implicit_symbols,
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
    explicit_symtab: &mut ExplicitSymbolTable,
    implicit_symtab: &mut ImplicitSymbolTable,
    memory_map: &mut MemoryMap,
    index_register_assigner: &mut IndexRegisterAssigner,
    body: &Source,
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

    // TODO: we should be able to convert implicit_symtab into
    // final_symbols (and drop implicit_symtab).
    let mut final_symbols = FinalSymbolTable::default();
    let mut bad_symbol_definitions: BTreeMap<SymbolName, ProgramError> = Default::default();
    // TODO: consider moving this into pass 2.
    for block in blocks.values() {
        if let Some(Origin::Symbolic(span, symbol_name)) = block.origin.as_ref()
            && !explicit_symtab.is_defined(symbol_name)
        {
            final_symbols.define_if_undefined(
                symbol_name.clone(),
                FinalSymbolType::Tag, // actually origin
                body.extract(span.start..span.end).to_string(),
                FinalSymbolDefinition::PositionIndependent(block.location.into()),
            );
        }
    }

    // We call extract_final_equalities here is to ensure that we
    // diagnose all looping definitions of equalities and get the data
    // we need for the listing, if there will be one.  It isn't
    // actually needed to generate the output binary.
    extract_final_equalities(
        equalities.as_slice(),
        body,
        explicit_symtab,
        implicit_symtab,
        memory_map,
        index_register_assigner,
        &mut rcblock,
        &mut final_symbols,
        &mut bad_symbol_definitions,
    )?;

    let convert_rc_failure = |e: RcWordAllocationFailure| -> AssemblerFailure {
        match e {
            RcWordAllocationFailure::RcBlockTooBig { source, .. } => {
                let span: Span = source.span();
                let location: LineAndColumn = body.location_of(span.start);
                AssemblerFailure::BadProgram(OneOrMore::new(WithLocation {
                    location,
                    inner: ProgramError::RcBlockTooLong(source),
                }))
            }
            ref e @ RcWordAllocationFailure::InconsistentTag {
                ref tag_name,
                span,
                explanation: _,
            } => {
                let location: LineAndColumn = body.location_of(span.start);
                AssemblerFailure::BadProgram(OneOrMore::new(WithLocation {
                    location,
                    inner: ProgramError::InconsistentTag {
                        name: tag_name.clone(),
                        span,
                        msg: e.to_string(),
                    },
                }))
            }
        }
    };

    for directive_block in blocks.values_mut() {
        if let Err(e) =
            directive_block.allocate_rc_words(explicit_symtab, implicit_symtab, &mut rcblock)
        {
            return Err(convert_rc_failure(e));
        }
    }

    // Now that RC-word allocation is complete, we no longer need to
    // mutate the explicit symbol table.
    let explicit_symtab: &ExplicitSymbolTable = &*explicit_symtab;

    for name in implicit_symtab.symbols() {
        match (implicit_symtab.get(name), explicit_symtab.get(name)) {
            (Some(implicit), Some(explicit)) => {
                panic!(
                    "symbol {name} appears in both the implicit ({implicit:#?} and the explicit ({explicit:#?} symbol tables"
                );
            }
            (Some(_), None) | (None, Some(_)) => (),
            (None, None) => {
                panic!(
                    "symbol {name} is returned by ImplicitSymbolTable::symbols() but is not defined there"
                );
            }
        }
    }

    if let Err(e) = assign_default_rc_word_tags(implicit_symtab, &mut rcblock, &mut final_symbols) {
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
            explicit_symtab,
            implicit_symtab,
            memory_map,
            index_register_assigner,
            &mut rcblock,
            &mut final_symbols,
            body,
            listing,
            &mut bad_symbol_definitions,
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

    match OneOrMore::try_from_iter(bad_symbol_definitions.into_values().map(|program_error| {
        let span = program_error.span();
        let location = body.location_of(span.start);
        WithLocation {
            location,
            inner: program_error,
        }
    })) {
        Ok(errors) => Err(AssemblerFailure::BadProgram(errors)),
        Err(_) => Ok((binary, final_symbols)),
    }
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
    source_file_body: &Source,
    errors: OneOrMore<Rich<lexer::Token>>,
) -> OneOrMore<WithLocation<ProgramError>> {
    errors.into_map(|e| {
        let span: Span = *e.span();
        WithLocation {
            location: source_file_body.location_of(span.start),
            inner: ProgramError::SyntaxError {
                span,
                msg: cleanup_control_chars(e.to_string()),
            },
        }
    })
}

pub(crate) fn assemble_source(
    source_file_body: &str,
    mut options: OutputOptions,
) -> Result<Binary, AssemblerFailure> {
    let source_file_body = Source::new(source_file_body);
    let mut p2output = match assemble_nonempty_input(&source_file_body) {
        AssemblerPass1Or2Output::Pass1Failed(Err(e)) => {
            return Err(e);
        }
        AssemblerPass1Or2Output::Pass1Failed(Ok(errors)) => {
            return Err(AssemblerFailure::BadProgram(fail_with_diagnostics(
                &source_file_body,
                errors,
            )));
        }
        AssemblerPass1Or2Output::Pass2Failed(e) => {
            return Err(e);
        }
        AssemblerPass1Or2Output::Success(
            errors,
            _output_options,
            Pass2Output {
                directive: None, ..
            },
        ) if errors.is_empty() => {
            panic!("assembly pass1 generated no errors, a directive should have been returned");
        }
        AssemblerPass1Or2Output::Success(errors, output_options, p2output) => {
            match OneOrMore::try_from_vec(errors) {
                Ok(errors) => {
                    return Err(AssemblerFailure::BadProgram(fail_with_diagnostics(
                        &source_file_body,
                        errors,
                    )));
                }
                Err(_) => {
                    // No errors.
                    options = options.merge(output_options);
                    p2output
                }
            }
        }
    };

    // Now we do pass 3, which generates the binary output
    let binary = {
        let mut listing = Listing::default();
        let (binary, final_symbols) = assemble_pass3(
            p2output
                .directive
                .expect("directive should have already been checked for None-ness"),
            &mut p2output.explicit_symbols,
            &mut p2output.implicit_symbols,
            &mut p2output.memory_map,
            &mut p2output.index_register_assigner,
            &source_file_body,
            &mut listing,
        )?;

        listing.set_final_symbols(final_symbols);
        if options.list {
            println!(
                "{0}",
                ListingWithBody {
                    listing: &listing,
                    body: &source_file_body,
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
        sequences: vec![InstructionSequence {
            local_symbols: None,
            instructions: vec![TaggedProgramInstruction {
                span: span(0..2),
                tags: Vec::new(),
                instruction: UntaggedProgramInstruction::from(OneOrMore::new(
                    CommaDelimitedFragment {
                        leading_commas: None,
                        holdbit: HoldBit::Unspecified,
                        span: span(0..2),
                        fragment: atom_to_fragment(Atom::from(LiteralValue::from((
                            span(0..2),
                            Script::Normal,
                            u36!(0o14),
                        )))),
                        trailing_commas: None,
                    },
                )),
            }],
        }],
    };

    let mut errors = Vec::new();
    let input_source = Source::new(input);
    assert_eq!(
        assemble_pass1(&input_source, &mut errors).expect("assembly should succeed"),
        (
            Some(SourceFile {
                punch: Some(PunchCommand(expected_directive_entry_point)),
                blocks: vec![expected_block],
                global_equalities: Default::default(), // no equalities
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

#[test]
fn test_duplicate_global_tag() {
    let input = concat!("TGX->0\n", "TGX->0\n");
    let input_source = Source::new(input);
    match assemble_nonempty_input(&input_source) {
        AssemblerPass1Or2Output::Pass2Failed(AssemblerFailure::BadProgram(errors)) => {
            dbg!(&errors);
            match errors.first() {
                WithLocation {
                    inner: ProgramError::SyntaxError { msg, span: _ },
                    ..
                } => {
                    assert!(
                        msg.contains(
                            "bad symbol definition for TGX: TGX is defined more than once"
                        )
                    );
                }
                other => {
                    panic!("expected a syntax error report, got {other:?}");
                }
            }
        }
        AssemblerPass1Or2Output::Success(errors, _output_options, p2output) => {
            dbg!(&errors);
            dbg!(&p2output);
            panic!("assembler unexpectedly succeeded with a bad input {input}");
        }
        unexpected => {
            panic!("assembly failed, but not in the way expected by this test: {unexpected:?}");
        }
    }
}
