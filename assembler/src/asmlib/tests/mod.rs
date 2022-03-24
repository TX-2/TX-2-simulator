// Assembler tests.
use base::prelude::*;

use nom::combinator::map;

use super::ek::{self, parse_partially_with};
use super::parser::*;
use super::types::{Elevation, InstructionFragment, SymbolName, SymbolTable};

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
        ProgramInstruction {
            tag: None,
            parts: vec![
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
            ]
        }
    );
}

#[test]
fn test_parse_symex() {
    for (input, expected) in [
        ("SOMENAME", "SOMENAME"),
        ("SOME NAME", "SOMENAME"),
        // OK to use a reserved identifier if it is not the first
        // syllable in the symex.
        ("TEST A", "TESTA"),
        // If there's no space after it, it's not reserved
        ("ATEST", "ATEST"),
        // Otherwise, the reserved identifier is the whole of it.
        ("B", "B"),
        // A symex can contain digits and can even start with one.
        ("HOP2IT", "HOP2IT"),
        ("HOP 2 IT", "HOP2IT"),
        ("4REAL", "4REAL"),
        // Some lower case letters are supported
        ("j2", "j2"),
        // Dot, underscore
        (".q", ".q"),
        ("._q", "._q"),
        // Single quotes are allowed too
        ("SCRATCH 'N' SNIFF", "SCRATCH'N'SNIFF"),
        ("F '", "F'"),
    ] {
        let got: SymbolName = parse_successfully_with(input, parse_symex);
        assert_eq!(got.canonical, expected);
    }
}

#[test]
fn test_empty_directive() {
    assert_eq!(parse_successfully_with("", directive), vec![])
}

#[test]
fn test_directive_without_tag() {
    assert_eq!(
        parse_successfully_with("673\n71\n", directive),
        vec![
            ProgramInstruction {
                tag: None,
                parts: vec![InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o673_u32),
                },]
            },
            ProgramInstruction {
                tag: None,
                parts: vec![InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o71_u32),
                },]
            },
        ]
    );
}

#[test]
fn test_symbol_name_one_syllable() {
    assert_eq!(
        parse_successfully_with("START4", symbol_name),
        SymbolName {
            canonical: "START4".to_string(),
            as_used: "START4".to_string(),
        }
    );
}

#[test]
fn test_symbol_name_two_syllables() {
    assert_eq!(
        parse_successfully_with("TWO WORDS", symbol_name),
        SymbolName {
            canonical: "TWOWORDS".to_string(),
            as_used: "TWO WORDS".to_string(),
        }
    );
}

#[test]
fn test_directive_with_single_syllable_tag() {
    assert_eq!(
        parse_successfully_with("START4  \t->\t205\n", directive),
        vec![ProgramInstruction {
            tag: Some(SymbolName {
                canonical: "START4".to_string(),
                as_used: "START4".to_string(),
            }),
            parts: vec![InstructionFragment {
                elevation: Elevation::Normal,
                value: Unsigned36Bit::from(0o205_u32),
            },]
        },]
    );
}

#[test]
fn test_arrow() {
    fn arrow_string<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, String> {
        map(arrow, |s| s.to_string())(input)
    }
    assert_eq!(
        parse_successfully_with("->", arrow_string),
        "->".to_string()
    );
    assert_eq!(
        parse_successfully_with("  -> ", arrow_string),
        "  -> ".to_string()
    );
}

#[test]
fn test_multi_syllable_tag() {
    let (tail, symbol, errors) = parse_partially_with("CODE HERE->205\n", parse_symex);
    dbg!(&tail);
    dbg!(&symbol);
    dbg!(&errors);
    assert!(errors.is_empty());
    assert_eq!(
        symbol,
        SymbolName {
            canonical: "CODEHERE".to_string(),
            as_used: "CODE HERE".to_string(),
        }
    );
    assert_eq!(tail, "->205\n");
}

#[test]
fn test_directive_with_multi_syllable_tag() {
    assert_eq!(
        parse_successfully_with("CODE HERE->205\n", directive),
        vec![ProgramInstruction {
            tag: Some(SymbolName {
                canonical: "CODEHERE".to_string(),
                as_used: "CODE HERE".to_string(),
            }),
            parts: vec![InstructionFragment {
                elevation: Elevation::Normal,
                value: Unsigned36Bit::from(0o205_u32),
            },]
        },]
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
        [ProgramInstruction { tag: None, parts }] => match parts.as_slice() {
            [only_frag] => {
                if only_frag == expected {
                    return;
                }
                panic!("expected fragment {:?}, got {:?}", expected, only_frag);
            }
            _ => {
                panic!("expected fragment {:?}, got {:?}", expected, &parts);
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
