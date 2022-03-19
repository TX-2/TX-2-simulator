use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, Read};

use crate::parser::parse_source_file;
use crate::types::*;

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
    match BufReader::new(input_file).read_to_string(&mut source_file_body) {
        Err(e) => Err(AssemblerFailure::IoErrorOnInput {
            filename: input_file_name.to_owned(),
            error: e,
            line_number: None,
        }),
        Ok(_) => {
            let mut symtab = SymbolTable::new();
            let mut errors = Vec::new();
            let _directive = parse_source_file(&source_file_body, &mut symtab, &mut errors)?;
            match errors.as_slice() {
                [first, ..] => {
                    for e in errors.iter() {
                        eprintln!("{}", e);
                    }
                    let location = &first.0;
                    let msg = first.1.as_str();
                    let columns = location
                        .columns
                        .as_ref()
                        .map(|range| (range.start, range.end));
                    Err(AssemblerFailure::SyntaxError {
                        line: location.line,
                        columns,
                        msg: msg.to_string(),
                    })
                }
                [] => {
                    // We could parse the input.  Next, perform
                    // address patching from the symbol table and
                    // generate an output file.
                    todo!("address resolution is not implemented")
                }
            }
        }
    }
}
