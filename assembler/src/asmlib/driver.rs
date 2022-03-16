use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader};

use crate::ek;
use crate::parser::{assemble_line, ProgramInstruction};
use crate::types::*;

fn assemble_pass1(
    lines: &[String],
    symtab: &mut SymbolTable,
) -> Result<(Vec<ProgramInstruction>, Vec<ek::Error>), AssemblerFailure> {
    let mut output: Vec<ProgramInstruction> = Vec::new();
    let mut errors: Vec<ek::Error> = Vec::new();
    for (line_number, line) in lines.iter().enumerate().map(|(n, line)| (n + 1, line)) {
        match assemble_line(line_number, line, symtab, &mut errors) {
            Ok(None) => (),
            Ok(Some(instr)) => match instr {
                ProgramInstruction::Error => (),
                _ => {
                    output.push(instr);
                }
            },
            Err(e) => {
                return Err(e);
            }
        }
    }
    Ok((output, errors))
}

pub fn assemble_file(input_file: &OsStr, _output_file: &OsStr) -> Result<(), AssemblerFailure> {
    let input = OpenOptions::new()
        .read(true)
        .open(input_file)
        .map_err(|e| AssemblerFailure::IoErrorOnInput {
            filename: input_file.to_owned(),
            error: e,
            line_number: None,
        })?;
    let mut source_lines: Vec<String> = Vec::new();
    for (line, input_item) in BufReader::new(input)
        .lines()
        .enumerate()
        .map(|(n, sl)| (n + 1, sl))
    {
        match input_item {
            Err(e) => {
                return Err(AssemblerFailure::IoErrorOnInput {
                    filename: input_file.to_owned(),
                    error: e,
                    line_number: Some(line),
                });
            }
            Ok(source_line) => {
                source_lines.push(source_line);
            }
        }
    }

    let mut symtab = SymbolTable::new();
    let (pass1_output, pass1_errors) = assemble_pass1(&source_lines, &mut symtab)?;
    drop(pass1_output);
    drop(pass1_errors);
    todo!("pass 2 does not exist")
}
