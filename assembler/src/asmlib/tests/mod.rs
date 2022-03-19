// Assembler tests.
use base::prelude::*;

use super::ek;
use super::parser::*;
use super::types::{Elevation, InstructionFragment, SymbolTable};

#[test]
fn test_assemble_blank_line() {
    let mut symtab = SymbolTable::new();
    let mut errors: Vec<ek::Error> = Vec::new();
    match parse_source_file("", &mut symtab, &mut errors) {
        Err(e) => {
            panic!(
                "expected blank line not to generate an assembly error, got error {}",
                e
            );
        }
        Ok(instructions) => {
            dbg!(&instructions);
            assert!(instructions.is_empty());
        }
    }
    assert!(errors.is_empty());
    assert!(symtab.is_empty());
}

#[cfg(test)]
pub(crate) fn parse_successfully_with<'a, T, F>(input_text: &'a str, parser: F) -> T
where
    F: for<'b> Fn(ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, T>,
{
    let (output, errors) = ek::parse_with(input_text, parser);
    if !errors.is_empty() {
        panic!("unexpected parse errors: {:?}", &errors);
    }
    output
}

#[test]
fn test_maybe_superscript_sign() {
    for sign in ['\u{207B}', '\u{207A}'] {
        let body = format!("{}", sign);
        assert_eq!(
            parse_successfully_with(&body, maybe_superscript_sign),
            Some(sign)
        );
    }
}

#[test]
fn test_maybe_subscript_sign() {
    for sign in ['\u{208B}', '\u{208A}'] {
        let body = format!("{}", sign);
        assert_eq!(
            parse_successfully_with(&body, maybe_subscript_sign),
            Some(sign)
        );
    }
}

#[test]
fn test_normal_literal_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("402", normal_literal_instruction_fragment),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(0o402_u32),
        }
    );
}

#[test]
fn test_superscript_literal_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("³⁶", superscript_literal_instruction_fragment),
        InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(0o36_u32),
        }
    );
}

#[test]
fn test_subscript_literal_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("₃₁", subscript_literal_instruction_fragment),
        InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o31_u32),
        }
    );
}

#[test]
fn test_program_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("₃₁", program_instruction_fragment),
        InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o31_u32),
        }
    );
    assert_eq!(
        parse_successfully_with("⁶³", program_instruction_fragment),
        InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(0o63_u32),
        }
    );
    assert_eq!(
        parse_successfully_with("6510", program_instruction_fragment),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(0o6510_u32),
        }
    );
}

#[test]
fn test_program_instruction() {
    assert_eq!(
        parse_successfully_with("⁶673₃₁", program_instruction),
        ProgramInstruction::Parts(vec![
            InstructionFragment {
                elevation: Elevation::Superscript,
                value: Unsigned36Bit::from(0o6_u32),
            },
            InstructionFragment {
                elevation: Elevation::Normal,
                value: Unsigned36Bit::from(0o673_u32),
            },
            InstructionFragment {
                elevation: Elevation::Subscript,
                value: Unsigned36Bit::from(0o31_u32),
            },
        ])
    );
}

#[test]
fn test_empty_directive() {
    assert_eq!(parse_successfully_with("", directive), vec![])
}

#[test]
fn test_directive() {
    assert_eq!(
        parse_successfully_with("673\n71\n", directive),
        vec![
            ProgramInstruction::Parts(vec![InstructionFragment {
                elevation: Elevation::Normal,
                value: Unsigned36Bit::from(0o673_u32),
            },]),
            ProgramInstruction::Parts(vec![InstructionFragment {
                elevation: Elevation::Normal,
                value: Unsigned36Bit::from(0o71_u32),
            },]),
        ]
    );
}

#[test]
fn test_end_of_file() {
    parse_successfully_with("", ek::expect_end_of_file);
}

#[test]
fn test_not_end_of_file() {
    let (_, errors) = ek::parse_with("something-is-here", ek::expect_end_of_file);
    assert!(!errors.is_empty());
}

#[cfg(test)]
fn assemble_nonempty_valid_input(input: &str) -> (Vec<ProgramInstruction>, SymbolTable) {
    let mut symtab = SymbolTable::new();
    let mut errors: Vec<ek::Error> = Vec::new();
    let result = parse_source_file(input, &mut symtab, &mut errors);
    if !errors.is_empty() {
        dbg!(&errors);
        panic!("assemble_nonempty_valid_input: errors were reported");
    }
    let instructions = result.expect("input should be valid");
    (instructions, symtab)
}

#[cfg(test)]
fn assemble_literal(input: &str, expected: &InstructionFragment) {
    let (directive, symtab) = assemble_nonempty_valid_input(input);
    if !symtab.is_empty() {
        panic!("no symbol should have been generated");
    }
    match directive.as_slice() {
        [ProgramInstruction::Parts(fragments)] => match fragments.as_slice() {
            [only_frag] => {
                if only_frag == expected {
                    return;
                }
                panic!("expected fragment {:?}, got {:?}", expected, only_frag);
            }
            _ => {
                panic!("expected fragment {:?}, got {:?}", expected, &fragments);
            }
        },
        _ => {
            panic!(
                "expected one instruction containing {:?}, got {:?}",
                &expected, &directive
            );
        }
    }
}

#[test]
fn test_assemble_octal_literal() {
    assemble_literal(
        "177777\n",
        &InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(0o177777_u32),
        },
    );
}

#[test]
fn test_assemble_octal_superscript_literal() {
    assemble_literal(
        "³⁶\n", // 36, superscript
        &InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(0o36_u32),
        },
    );
}

#[test]
fn test_assemble_octal_subscript_literal() {
    assemble_literal(
        "₁₃\n",
        &InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o13_u32),
        },
    );
}
