use crate::parser::ErrorLocation;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, Read};

use crate::parser::{source_file, ManuscriptItem, ManuscriptMetaCommand, ProgramInstruction};
use crate::state::{Error, NumeralMode};
use crate::types::*;
use base::prelude::*;

/// Represents the meta commands which are still relevant in the
/// directive.  Excludes things like the PUNCH meta command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectiveMetaCommand {
    Invalid, // e.g."☛☛BOGUS"
    BaseChange(NumeralMode),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectiveItem {
    MetaCommand(DirectiveMetaCommand),
    Instruction(ProgramInstruction),
}

#[derive(Debug)]
pub struct Directive {
    // This is a temporary definition.  Eventually a Directive will
    // become a sequene of blocks, each block having a specific
    // origin.
    items: Vec<DirectiveItem>,
    entry_point: Option<Address>,
    symbols: SymbolTable,
}

impl Directive {
    fn with_capacity(symbols: SymbolTable, cap: usize) -> Directive {
        Directive {
            items: Vec::with_capacity(cap),
            entry_point: None,
            symbols,
        }
    }
}

impl Directive {
    fn push(&mut self, item: DirectiveItem) {
        self.items.push(item)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct OutputOptions {
    // TODO: implement arguments of the LIST, PLIST, TYPE
    // metacommands.
    list: bool,
}

fn assemble_pass1(
    source_file_body: &str,
    errors: &mut Vec<Error>,
) -> Result<(Directive, OutputOptions), AssemblerFailure> {
    let options = OutputOptions {
        // Because we don't parse the LIST etc. metacommands yet, we
        // simply hard-code the list option so that the symbol table isn't
        // unused.
        list: true,
    };
    let mut symbols = SymbolTable::new();
    let manuscript = source_file(source_file_body, &mut symbols, errors)?;
    let mut directive: Directive = Directive::with_capacity(symbols, manuscript.len());
    for manuscript_item in manuscript {
        match manuscript_item {
            ManuscriptItem::Instruction(inst) => {
                directive.push(DirectiveItem::Instruction(inst));
            }
            ManuscriptItem::MetaCommand(ManuscriptMetaCommand::Invalid) => {
                directive.push(DirectiveItem::MetaCommand(DirectiveMetaCommand::Invalid));
            }
            ManuscriptItem::MetaCommand(ManuscriptMetaCommand::BaseChange(base)) => {
                directive.push(DirectiveItem::MetaCommand(
                    DirectiveMetaCommand::BaseChange(base),
                ));
            }
            ManuscriptItem::MetaCommand(ManuscriptMetaCommand::Punch(address)) => {
                directive.entry_point = address;
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
                break;
            }
        }
    }
    // TODO: implement the PUNCH metacommand.
    // TODO: implement the SAVE metacommand.
    // TODO: implement the READ metacommand.
    // TODO: implement the TAPE metacommand.
    // TODO: implement the CORE metacommand.
    // TODO: implement the ERRORS metacommand.
    Ok((directive, options))
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26");
    let mut errors: Vec<Error> = Vec::new();
    let expected_directive = Directive {
        items: vec![DirectiveItem::Instruction(ProgramInstruction {
            origin: None,
            tag: None,
            parts: vec![InstructionFragment {
                elevation: Elevation::Normal,
                value: u36!(0o14),
            }],
        })],
        entry_point: Some(Address::new(Unsigned18Bit::from(0o26_u8))),
        symbols: SymbolTable {},
    };
    let (directive, _options) = assemble_pass1(input, &mut errors).expect("pass 1 should succeed");
    assert_eq!(expected_directive.items, directive.items);
    assert_eq!(expected_directive.entry_point, directive.entry_point);
}

pub fn assemble_file(
    input_file_name: &OsStr,
    _output_file: &OsStr,
) -> Result<(), AssemblerFailure> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnInput {
            filename: input_file_name.to_owned(),
            error: e,
            line_number: None,
        })?;

    let mut source_file_body: String = String::new();
    let (directive, options) =
        match BufReader::new(input_file).read_to_string(&mut source_file_body) {
            Err(e) => {
                return Err(AssemblerFailure::IoErrorOnInput {
                    filename: input_file_name.to_owned(),
                    error: e,
                    line_number: None,
                })
            }
            Ok(_) => {
                let mut errors = Vec::new();
                let directive = assemble_pass1(&source_file_body, &mut errors)?;
                match errors.as_slice() {
                    [first, ..] => {
                        for e in errors.iter() {
                            eprintln!("{}", e);
                        }
                        let location: &ErrorLocation = &first.0;
                        let msg = first.1.as_str();
                        let columns = location
                            .columns
                            .as_ref()
                            .map(|range| (range.start, range.end));
                        return Err(AssemblerFailure::SyntaxError {
                            line: location.line,
                            columns,
                            msg: msg.to_string(),
                        });
                    }
                    [] => directive,
                }
            }
        };
    // Now we do pass 2.
    if options.list {
        directive
            .symbols
            .list()
            .map_err(|e| AssemblerFailure::IoErrorOnStdout { error: e })?;
    }
    todo!("address resolution (and assembly pass 2) is not implemented")
}
