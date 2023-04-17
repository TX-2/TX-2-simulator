use std::cmp::max;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read};
use std::path::Path;

use tracing::{event, span, Level};

use super::ast::*;
use super::ek;
use super::parser::{source_file, ErrorLocation};
use super::state::{Error, NumeralMode, State};
use super::symtab::*;
use super::types::*;
use base::prelude::{Address, Unsigned36Bit};

mod output;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct OutputOptions {
    // TODO: implement arguments of the LIST, PLIST, TYPE
    // metacommands.
    list: bool,
}

fn convert_source_file_to_directive(source_file: &SourceFile) -> Directive {
    let mut directive: Directive = Directive::new();
    for mblock in source_file.blocks.iter() {
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
fn assemble_pass1(
    source_file_body: &str,
    errors: &mut Vec<Error>,
) -> Result<(SourceFile, OutputOptions), AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 1");
    let _enter = span.enter();
    let options = OutputOptions {
        // Because we don't parse the LIST etc. metacommands yet, we
        // simply hard-code the list option so that the symbol table isn't
        // unused.
        list: true,
    };

    fn setup(state: &mut State) {
        // Octal is actually the default numeral mode, we just call
        // set_numeral_mode here to keep Clippy happy until we
        // implement ☛☛DECIMAL and ☛☛OCTAL.
        state.set_numeral_mode(NumeralMode::Decimal); // appease Clippy
        state.set_numeral_mode(NumeralMode::Octal);
    }
    let (source_file, new_errors) = ek::parse_with(source_file_body, source_file, setup);
    if !new_errors.is_empty() {
        errors.extend(new_errors.into_iter());
    }
    Ok((source_file, options))
}

/// This test helper is defined here so that we don't have to expose
/// assemble_pass1, assemble_pass2.
#[cfg(test)]
pub(crate) fn assemble_nonempty_valid_input(input: &str) -> (Directive, SymbolTable) {
    let mut symtab = SymbolTable::default();
    let mut errors: Vec<Error> = Vec::new();
    let result: Result<(SourceFile, OutputOptions), AssemblerFailure> =
        assemble_pass1(input, &mut errors);
    if !errors.is_empty() {
        panic!("assemble_nonempty_valid_input: errors were reported: {errors:?}");
    }
    match result {
        Ok((source_file, _options)) => {
            let directive = assemble_pass2(&source_file, &mut symtab)
                .expect("test program should not extend beyong physical memory");
            (directive, symtab)
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
) -> Result<Vec<(Option<SymbolName>, Address)>, AddressOverflow> {
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
        result.push((None, base));
        let next = offset_from_origin(&base, block.instruction_count())?;
        next_address = Some(if let Some(n) = next_address {
            max(n, next)
        } else {
            next
        });
    }
    Ok(result)
}

/// Pass 2 converts the abstract syntax representation into a
/// `Directive`, which is closer to binary code.
fn assemble_pass2(
    source_file: &SourceFile,
    symtab: &mut SymbolTable,
) -> Result<Directive, AddressOverflow> {
    let span = span!(Level::ERROR, "assembly pass 2");
    let _enter = span.enter();

    for (symbol, context) in source_file.global_symbol_references() {
        symtab.record_usage_context(symbol.clone(), context)
    }
    for (symbol, definition) in source_file.global_symbol_definitions() {
        symtab.define(symbol.clone(), definition.clone())
    }
    let origins: Vec<(Option<SymbolName>, Address)> = calculate_block_origins(source_file, symtab)?;
    for (block_number, (maybe_sym, address)) in origins.iter().enumerate() {
        if let Some(sym) = maybe_sym {
            symtab.define(sym.clone(), SymbolDefinition::Origin(*address));
        }
        symtab.record_block_origin(block_number, *address);
    }
    let directive = convert_source_file_to_directive(source_file);
    event!(
        Level::INFO,
        "assembly generated {} instructions",
        directive.instruction_count()
    );
    Ok(directive)
}

/// Pass 3 generates binary code.
fn assemble_pass3(
    directive: Directive,
    symtab: &SymbolTable,
) -> Result<Binary, SymbolLookupFailure> {
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
            .collect::<Result<Vec<_>, SymbolLookupFailure>>()?;
        binary.add_chunk(BinaryChunk {
            address: block.origin.0,
            words,
        });
    }
    Ok(binary)
}

pub(crate) fn assemble_source(
    source_file_body: &str,
    symbols: &mut SymbolTable,
) -> Result<Binary, AssemblerFailure> {
    let mut errors = Vec::new();
    let (source_file, options) = assemble_pass1(source_file_body, &mut errors)?;
    match errors.as_slice() {
        [first, ..] => {
            for e in errors.iter() {
                eprintln!("{}", e);
            }
            let location: &ErrorLocation = &first.0;
            let msg = first.1.as_str();
            return Err(AssemblerFailure::SyntaxError {
                line: location.line,
                column: location.column,
                msg: msg.to_string(),
            });
        }
        [] => (),
    }

    // Now we do pass 2.
    let binary = {
        let directive = match assemble_pass2(&source_file, symbols) {
            Ok(d) => d,
            Err(AddressOverflow(base, size)) => {
                return Err(AssemblerFailure::ProgramTooBig(base, size));
            }
        };
        event!(
            Level::INFO,
            "assembly pass 2 generated {} instructions",
            directive.instruction_count()
        );

        if options.list {
            // List the symbols.
            for (name, definition) in symbols.list() {
                println!("{name} = {definition}");
            }
        }

        // Pass 3 generates the binary output
        assemble_pass3(directive, symbols).expect("all symbols should already have final values")
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

    let mut symbols = SymbolTable::default();
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

    let user_program: Binary = assemble_source(&source_file_body, &mut symbols)?;

    // The Users Guide explains on page 6-23 how the punched binary
    // is created (and read back in).
    let output_file = OpenOptions::new()
        .create(true)
        .write(true)
        .open(output_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnOutput {
            filename: output_file_name.to_owned(),
            error: e,
        })?;
    let mut writer = BufWriter::new(output_file);
    output::write_user_program(&user_program, &mut writer, output_file_name)
}

#[cfg(test)]
mod tests {
    use base::prelude::{u18, u36, Address};

    use super::super::{
        ast::{
            Elevation, Expression, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock,
            ProgramInstruction, PunchCommand, SourceFile, Statement,
        },
        state::Error,
    };
    use super::assemble_pass1;

    #[test]
    fn test_assemble_pass1() {
        let input = concat!("14\n", "☛☛PUNCH 26\n");
        let mut errors: Vec<Error> = Vec::new();
        let (source_file, _options) =
            assemble_pass1(input, &mut errors).expect("pass 1 should succeed");

        assert_eq!(
            source_file,
            SourceFile {
                punch: Some(PunchCommand(Some(Address::from(u18!(0o26))))),
                blocks: vec![ManuscriptBlock {
                    origin: None,
                    statements: vec![Statement::Instruction(ProgramInstruction {
                        tag: None,
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment {
                            value: Expression::Literal(LiteralValue::from((
                                Elevation::Normal,
                                u36!(0o14)
                            )))
                        }]
                    })]
                }]
            }
        );
    }
}
