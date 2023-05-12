mod output;
#[cfg(test)]
mod tests;

use std::cmp::max;
use std::collections::HashSet;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read};
use std::path::Path;

use chumsky::error::Rich;
use tracing::{event, span, Level};

use super::ast::*;
use super::parser::parse_source_file;
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::symtab::*;
use super::types::*;
use base::prelude::{Address, Unsigned36Bit, Unsigned6Bit};

#[cfg(test)]
use base::charset::Script;
#[cfg(test)]
use base::prelude::Unsigned18Bit;
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
struct OutputOptions {
    // TODO: implement arguments of the LIST, PLIST, TYPE
    // metacommands.
    list: bool,
}

fn convert_source_file_to_directive(source_file: &SourceFile) -> Directive {
    let mut directive: Directive = Directive::default();
    for mblock in source_file.blocks.iter() {
        if mblock.instruction_count() == 0 {
            // This block contains only things that don't generate
            // code (e.g. assignments), so don't emit it.
            continue;
        }
        let effective_origin = match mblock.origin {
            None => {
                let address = Origin::default();
                event!(
                    Level::DEBUG,
                    "Locating a block at default address {:o}",
                    address
                );
                address
            }
            Some(address) => {
                event!(
                    Level::DEBUG,
                    "Locating a block at specified address {:o}",
                    address
                );
                address
            }
        };
        let mut block = Block {
            origin: effective_origin,
            items: Vec::new(),
        };
        for statement in mblock.statements.iter() {
            match statement {
                Statement::Instruction(inst) => {
                    block.push(inst.clone());
                }
                Statement::Assignment(_, _) => (),
            }
        }
        directive.push(block);
    }

    match source_file.punch {
        Some(PunchCommand(Some(address))) => {
            event!(
                Level::INFO,
                "program entry point was specified as {address:o}"
            );
            directive.set_entry_point(address);
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

    directive
}

/// Pass 1 converts the program source into an abstract syntax representation.
fn assemble_pass1<'a>(
    source_file_body: &'a str,
    errors: &mut Vec<Rich<'a, char>>,
) -> Result<(Option<SourceFile>, OutputOptions), AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 1");
    let _enter = span.enter();
    let options = OutputOptions {
        // Because we don't parse the LIST etc. metacommands yet, we
        // simply hard-code the list option so that the symbol table isn't
        // unused.
        list: true,
    };

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
pub(crate) fn assemble_nonempty_valid_input<'a>(input: &'a str) -> (Directive, FinalSymbolTable) {
    let symtab = SymbolTable::default();
    let mut errors: Vec<Rich<'_, char>> = Vec::new();
    let result: Result<(Option<SourceFile>, OutputOptions), AssemblerFailure> =
        assemble_pass1(input, &mut errors);
    if !errors.is_empty() {
        panic!("assemble_nonempty_valid_input: errors were reported: {errors:?}");
    }
    match result {
        Ok((None, _)) => unreachable!("parser should generate output if there are no errors"),
        Ok((Some(source_file), _options)) => {
            let (directive, final_symbols) = assemble_pass2(&source_file, symtab)
                .expect("test program should not extend beyong physical memory");
            (directive, final_symbols)
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

fn calculate_block_origins(
    source_file: &SourceFile,
    _symtab: &SymbolTable,
) -> Result<Vec<Address>, AddressOverflow> {
    let mut result = Vec::new();
    let mut next_address: Option<Address> = None;
    for block in source_file.blocks.iter() {
        let base = match block.origin {
            // When symbolic origins become supported we will need to use
            // the symbol table.
            Some(Origin(address)) => address,
            None => match next_address {
                Some(a) => a,
                None => Origin::default().into(),
            },
        };
        result.push(base);
        let next = offset_from_origin(&base, block.instruction_count())?;
        next_address = Some(if let Some(n) = next_address {
            max(n, next)
        } else {
            next
        });
    }
    Ok(result)
}

fn unique_symbols_in_order<'a, I>(items: I) -> Vec<SymbolName>
where
    I: IntoIterator<Item = SymbolName>,
{
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for sym in items {
        if !seen.contains(&sym) {
            seen.insert(sym.clone());
            result.push(sym);
        }
    }
    result
}

/// Pass 2 converts the abstract syntax representation into a
/// `Directive`, which is closer to binary code.
fn assemble_pass2(
    source_file: &SourceFile,
    mut symtab: SymbolTable,
) -> Result<(Directive, FinalSymbolTable), AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 2");
    let _enter = span.enter();

    for (symbol, context) in source_file.global_symbol_references() {
        eprintln!("recording use of {} with {:?}", symbol, context);
        symtab.record_usage_context(symbol.clone(), context)
    }
    for (symbol, definition) in source_file.global_symbol_definitions() {
        eprintln!("recording definition of {} as {:?}", symbol, definition);
        match symtab.define(symbol.clone(), definition.clone()) {
            Ok(_) => (),
            Err(e) => {
                let msg = format!("bad symbol definition: {e}");
                return Err(AssemblerFailure::SymbolError(
                    symbol.clone(),
                    SymbolLookupFailure::Inconsistent { symbol, msg },
                ));
            }
        }
    }
    let mut next_free_address: Option<Address> = None;
    let origins: Vec<Address> = match calculate_block_origins(source_file, &symtab) {
        Ok(origins) => origins,
        Err(e) => {
            return Err(e.into());
        }
    };
    for (block_number, address) in origins.iter().enumerate() {
        symtab.record_block_origin(block_number, *address);
        let size = source_file.blocks[block_number].instruction_count();
        let after_end = offset_from_origin(address, size)?;
        next_free_address = next_free_address
            .map(|current| max(current, after_end))
            .or(Some(after_end));
    }

    let final_symbols = match next_free_address {
        Some(next_free) => {
            let mut rc_block: Vec<Unsigned36Bit> = Vec::new();
            let mut index_registers_used: Unsigned6Bit = Unsigned6Bit::ZERO;
            let symbol_refs_in_program_order: Vec<SymbolName> = unique_symbols_in_order(
                source_file
                    .global_symbol_references()
                    .map(|(symbol, _)| symbol),
            );
            match finalise_symbol_table(
                symtab,
                symbol_refs_in_program_order.iter(),
                next_free.into(),
                &mut rc_block,
                &mut index_registers_used,
            ) {
                Ok(fs) => fs,
                Err(e) => {
                    return Err(e.into());
                }
            }
        }
        None => {
            event!(
                Level::WARN,
                "the program appears to be empty; generating 0 instructions"
            );
            return Ok((Directive::default(), FinalSymbolTable::default()));
        }
    };

    let directive = convert_source_file_to_directive(source_file);
    event!(
        Level::INFO,
        "assembly generated {} instructions",
        directive.instruction_count()
    );
    Ok((directive, final_symbols))
}

/// Pass 3 generates binary code.
fn assemble_pass3<S: SymbolLookup>(
    directive: Directive,
    symtab: &mut S,
) -> Result<Binary, S::Error> {
    let span = span!(Level::ERROR, "assembly pass 3");
    let _enter = span.enter();

    let mut binary = Binary::default();
    if let Some(address) = directive.entry_point() {
        binary.set_entry_point(address);
    }

    for block in directive.blocks.iter() {
        let words: Vec<Unsigned36Bit> = block
            .items
            .iter()
            .map(|inst| inst.value(symtab))
            .collect::<Result<Vec<_>, S::Error>>()?;
        binary.add_chunk(BinaryChunk {
            address: block.origin.into(),
            words,
        });
    }
    Ok(binary)
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

pub(crate) fn assemble_source(
    source_file_body: &str,
    symbols: SymbolTable,
) -> Result<Binary, AssemblerFailure> {
    let mut errors = Vec::new();
    let (source_file, options) = assemble_pass1(source_file_body, &mut errors)?;
    match errors.as_slice() {
        [first, ..] => {
            for e in errors.iter() {
                eprintln!("{}", e);
            }
            let (line, column) = pos_line_column(source_file_body, first.span().start)
                .expect("span for error message should be inside the file");
            return Err(AssemblerFailure::SyntaxError {
                line: line as u32,
                column: Some(column),
                msg: first.to_string(),
            });
        }
        [] => (),
    }
    let source_file =
        source_file.expect("assembly pass1 generated no errors, an AST should have been returned");

    // Now we do passes 2 and 3.
    let binary = {
        let (directive, mut final_symbols) = assemble_pass2(&source_file, symbols)?;
        event!(
            Level::INFO,
            "assembly pass 2 generated {} instructions",
            directive.instruction_count()
        );

        if options.list {
            // List the symbols.
            for (name, definition) in final_symbols.list() {
                println!("{name} = {definition}");
            }
        }

        // Pass 3 generates the binary output
        let result: Result<Binary, Infallible> = assemble_pass3(directive, &mut final_symbols);
        match result {
            Ok(binary) => binary,
            Err(_) => {
                unreachable!("instances of Infallible cannot be created");
            }
        }
    };

    // The count here also doesn't include the size of the RC-block as
    // that is not yet implemented.
    event!(
        Level::INFO,
        "assembly pass 3 generated {} words of binary output (not counting the reader leader)",
        binary.count_words()
    );
    Ok(binary)
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let expected_directive_entry_point = Some(Address::new(Unsigned18Bit::from(0o26_u8)));
    let expected_block = ManuscriptBlock {
        origin: None,
        statements: vec![Statement::Instruction(ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: vec![InstructionFragment {
                value: Expression::Literal(LiteralValue::from((Script::Normal, u36!(0o14)))),
            }],
        })],
    };

    let mut errors = Vec::new();
    assert_eq!(
        assemble_pass1(input, &mut errors).expect("assembly should succeed"),
        (
            Some(SourceFile {
                punch: Some(PunchCommand(expected_directive_entry_point)),
                blocks: vec![expected_block],
            }),
            OutputOptions { list: true }
        )
    );
    assert!(errors.is_empty());
}

pub fn assemble_file(
    input_file_name: &OsStr,
    output_file_name: &Path,
) -> Result<(), AssemblerFailure> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnInput {
            filename: input_file_name.to_owned(),
            error: e,
            line_number: None,
        })?;

    let symbols = SymbolTable::default();
    let source_file_body = {
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

    let user_program: Binary = assemble_source(&source_file_body, symbols)?;

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
