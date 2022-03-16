// Assembler tests.
use base::prelude::*;

use super::ek;
use super::parser::{assemble_line, ProgramInstruction};
use super::types::{Elevation, InstructionFragment, SymbolTable};

#[test]
fn test_assemble_blank_line() {
    let mut symtab = SymbolTable::new();
    let mut errors: Vec<ek::Error> = Vec::new();
    match assemble_line(1, "", &mut symtab, &mut errors) {
        Err(e) => {
            panic!(
                "expected blank line not to generate an assembly error, got error {}",
                e
            );
        }
        Ok(Some(inst)) => {
            panic!(
                "expected blank line not to generate an instruction, but got {:?}",
                &inst
            );
        }
        Ok(None) => (),
    }
    assert!(errors.is_empty());
    assert!(symtab.is_empty());
}

#[cfg(test)]
fn assemble_nonempty_valid_line(line: &str) -> (Vec<InstructionFragment>, SymbolTable) {
    let mut symtab = SymbolTable::new();
    let mut errors: Vec<ek::Error> = Vec::new();
    match assemble_line(1, line, &mut symtab, &mut errors) {
        Ok(Some(ProgramInstruction::Error)) => {
            panic!("Failed to assemble '{}'", line);
        }
        Ok(Some(ProgramInstruction::Parts(v))) => {
            if !errors.is_empty() {
                dbg!(&errors);
                panic!("assemble_nonempty_valid_line: errors were reported");
            }
            (v, symtab)
        }
        Ok(None) => {
            panic!(
                "'{}' assembled to no instruction (as if it were an empty line)",
                line
            );
        }
        Err(e) => {
            panic!("Failed to assemble '{}': {}", line, e);
        }
    }
}

#[test]
fn test_assemble_octal_literal() {
    let (parts, symtab) = assemble_nonempty_valid_line("177777");
    match parts.as_slice() {
        [InstructionFragment {
            elevation: Elevation::Normal,
            value,
        }] => {
            assert_eq!(value, &Unsigned36Bit::from(0o177777_u32));
            assert!(symtab.is_empty());
        }
        _ => {
            panic!("unexpected assembler output {:?}", &parts);
        }
    }
}

#[test]
fn test_assemble_octal_superscript_literal() {
    let (parts, symtab) = assemble_nonempty_valid_line("³⁶"); // 36, superscript
    match parts.as_slice() {
        [InstructionFragment {
            elevation: Elevation::Superscript,
            value,
        }] => {
            assert_eq!(value, &Unsigned36Bit::from(0o36_u32));
            assert!(symtab.is_empty());
        }
        _ => {
            panic!("unexpected assembler output {:?}", &parts);
        }
    }
}

#[test]
fn test_assemble_octal_subscript_literal() {
    let (parts, symtab) = assemble_nonempty_valid_line("₁₃"); // 13, subscript
    match parts.as_slice() {
        [InstructionFragment {
            elevation: Elevation::Subscript,
            value,
        }] => {
            assert_eq!(value, &Unsigned36Bit::from(0o13_u32));
            assert!(symtab.is_empty());
        }
        _ => {
            panic!("unexpected assembler output {:?}", &parts);
        }
    }
}
