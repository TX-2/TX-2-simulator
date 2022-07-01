// Assembler tests.

use base::prelude::*;
use base::u36;
use std::cell::RefCell;

use nom::combinator::map;

use super::ek::{self, parse_partially_with};
use super::parser::*;
use super::state::{Error, NumeralMode, State, StateExtra};
use super::types::{AssemblerFailure, Elevation, InstructionFragment, SymbolName, SymbolTable};

#[test]
fn test_assemble_blank_line() {
    let mut symtab = SymbolTable::new();
    let mut errors: Vec<Error> = Vec::new();
    match source_file("", &mut symtab, &mut errors) {
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
pub(crate) fn parse_successfully_with<'a, T, F, M>(
    input_text: &'a str,
    parser: F,
    state_setup: M,
) -> T
where
    F: for<'b> Fn(ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, T>,
    M: FnMut(&mut State),
{
    let (output, errors) = ek::parse_with(input_text, parser, state_setup);
    if !errors.is_empty() {
        panic!("unexpected parse errors: {:?}", &errors);
    }
    output
}

#[cfg(test)]
fn parse_test_input<'a, F>(input_text: &'a str, parser: F) -> Result<String, String>
where
    F: for<'b> Fn(ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>>,
{
    let rstate = RefCell::new(State::new());
    let input: ek::LocatedSpan<'a, '_> =
        ek::LocatedSpan::new_extra(input_text, StateExtra::new(&rstate));
    match parser(input) {
        Ok(out) => Ok(out.1.fragment().to_string()),
        Err(e) => Err(e.to_string()),
    }
}

#[cfg(test)]
fn no_state_setup(_: &mut State) {}

#[cfg(test)]
fn set_decimal_mode(state: &mut State) {
    state.set_numeral_mode(NumeralMode::Decimal);
}

#[test]
fn test_maybe_superscript_sign() {
    for sign in [
        '\u{207B}', // ⁻
        '\u{207A}', // ⁺
    ] {
        let body = format!("{}", sign);
        assert_eq!(
            parse_successfully_with(&body, maybe_superscript_sign, no_state_setup),
            Some(sign)
        );
    }
}

#[test]
fn test_maybe_subscript_sign() {
    for sign in [
        '\u{208B}', // ₋
        '\u{208A}', // ₊
    ] {
        let body = format!("{}", sign);
        assert_eq!(
            parse_successfully_with(&body, maybe_subscript_sign, no_state_setup),
            Some(sign)
        );
    }
}

#[test]
fn test_normal_literal_instruction_fragment_oct_defaultmode() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("402", normal_literal_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: u36!(0o402),
        }
    );
}

#[test]
fn test_normal_literal_instruction_fragment_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with(
            "402·",
            normal_literal_instruction_fragment,
            set_decimal_mode
        ),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(0o402_u32), // note: octal
        }
    );
}

#[test]
fn test_normal_literal_instruction_fragment_dec_defaultmode() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("402·", normal_literal_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(402_u32),
        }
    );
}

#[test]
fn test_normal_literal_instruction_fragment_dec_decmode() {
    assert_eq!(
        // Decimal is the default if there was a previous ☛☛DECIMAL
        parse_successfully_with("402", normal_literal_instruction_fragment, set_decimal_mode),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(402_u32),
        }
    );
}

#[test]
fn test_superscript_literal_instruction_fragment_oct() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with(
            "³⁶",
            superscript_literal_instruction_fragment,
            no_state_setup
        ),
        InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(0o36_u32),
        }
    );
}

#[test]
fn test_superscript_literal_instruction_fragment_dec_defaultmode() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with(
            "³⁶̇ ",
            superscript_literal_instruction_fragment,
            no_state_setup
        ),
        InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(36_u32), // decimal
        }
    );
}

#[test]
fn test_superscript_literal_instruction_fragment_dec_decmode() {
    // Simulate a previous ☛☛DECIMAL.
    assert_eq!(
        parse_successfully_with(
            "³⁶",
            superscript_literal_instruction_fragment,
            set_decimal_mode
        ),
        InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(36_u32), // decimal
        }
    );
}

#[test]
fn test_subscript_literal_instruction_fragment_oct_defaultmode() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("₃₁", subscript_literal_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o31_u32),
        }
    );
}

#[test]
fn test_subscript_literal_instruction_fragment_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with(
            "₃₁.",
            subscript_literal_instruction_fragment,
            set_decimal_mode
        ),
        InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o31_u32),
        }
    );
}

#[test]
fn test_subscript_literal_instruction_fragment_dec() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with(
            "₃₁.",
            subscript_literal_instruction_fragment,
            no_state_setup
        ),
        InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(31_u32),
        }
    );
}

#[test]
fn test_program_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("₃₁", program_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o31_u32),
        }
    );
    assert_eq!(
        parse_successfully_with("⁶³", program_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(0o63_u32),
        }
    );
    assert_eq!(
        parse_successfully_with("6510", program_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: Unsigned36Bit::from(0o6510_u32),
        }
    );
}

#[test]
fn test_program_instruction() {
    assert_eq!(
        parse_successfully_with("⁶673₃₁", program_instruction, no_state_setup),
        (
            None,
            ManuscriptItem::Instruction(ProgramInstruction {
                tag: None,
                holdbit: HoldBit::Unspecified,
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
            })
        )
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
        let got: SymbolName = parse_successfully_with(input, parse_symex, no_state_setup);
        assert_eq!(got.canonical, expected);
    }
}

#[test]
fn test_dead_char() {
    let rstate = RefCell::new(State::new());
    let input: ek::LocatedSpan = ek::LocatedSpan::new_extra("X", StateExtra::new(&rstate));
    assert!(dead_char(input).is_err());

    let rstate = RefCell::new(State::new());
    let input: ek::LocatedSpan = ek::LocatedSpan::new_extra("\u{0332}", StateExtra::new(&rstate));
    assert!(dead_char(input).is_ok());

    assert!(parse_test_input("\u{0332}", dead_char).is_ok());
}

#[test]
fn test_parse_compound_char() {
    fn parse_cc<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, String> {
        map(parse_compound_char, |cc| cc.fragment().to_string())(input)
    }

    for (input, expected) in [("X\u{0008}Y", "X\u{0008}Y")] {
        let got: String = parse_successfully_with(input, parse_cc, no_state_setup);
        assert_eq!(got.as_str(), expected);
    }
}

#[test]
fn test_empty_manuscript() {
    assert_eq!(
        parse_successfully_with("", parse_manuscript, no_state_setup),
        vec![]
    )
}

#[test]
fn test_manuscript_without_tag() {
    assert_eq!(
        parse_successfully_with(
            "673 ** This is a comment\n71\n",
            parse_manuscript,
            no_state_setup
        ),
        vec![
            (
                None,
                ManuscriptItem::Instruction(ProgramInstruction {
                    tag: None,
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment {
                        elevation: Elevation::Normal,
                        value: Unsigned36Bit::from(0o673_u32),
                    },]
                })
            ),
            (
                None,
                ManuscriptItem::Instruction(ProgramInstruction {
                    tag: None,
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment {
                        elevation: Elevation::Normal,
                        value: Unsigned36Bit::from(0o71_u32),
                    },]
                })
            ),
        ]
    );
}

#[test]
fn test_symbol_name_one_syllable() {
    assert_eq!(
        parse_successfully_with("START4", symbol_name, no_state_setup),
        SymbolName {
            canonical: "START4".to_string(),
            //as_used: "START4".to_string(),
        }
    );
}

#[test]
fn test_symbol_name_two_syllables() {
    assert_eq!(
        parse_successfully_with("TWO WORDS", symbol_name, no_state_setup),
        SymbolName {
            canonical: "TWOWORDS".to_string(),
            //as_used: "TWO WORDS".to_string(),
        }
    );
}

#[test]
fn test_manuscript_with_single_syllable_tag() {
    assert_eq!(
        parse_successfully_with(
            "START4  \t->\t205 ** comment here\n",
            parse_manuscript,
            no_state_setup
        ),
        vec![(
            None,
            ManuscriptItem::Instruction(ProgramInstruction {
                tag: Some(SymbolName {
                    canonical: "START4".to_string(),
                    //as_used: "START4".to_string(),
                }),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o205_u32),
                },]
            })
        ),]
    );
}

#[test]
fn test_manuscript_with_origin() {
    assert_eq!(
        parse_successfully_with(
            "100 | 202 ** literal value\n",
            parse_manuscript,
            no_state_setup
        ),
        vec![(
            Some(Origin(Address::new(u18!(0o100)))),
            ManuscriptItem::Instruction(ProgramInstruction {
                tag: None,
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o202_u32),
                },]
            })
        ),]
    );
}

#[test]
fn test_arrow() {
    fn arrow_string<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, String> {
        map(arrow, |s| s.to_string())(input)
    }
    assert_eq!(
        parse_successfully_with("->", arrow_string, no_state_setup),
        "->".to_string()
    );
    assert_eq!(
        parse_successfully_with("  -> ", arrow_string, no_state_setup),
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
            //as_used: "CODE HERE".to_string(),
        }
    );
    assert_eq!(tail, "->205\n");
}

#[test]
fn test_manuscript_with_multi_syllable_tag() {
    assert_eq!(
        parse_successfully_with(
            "CODE HERE->205 ** Also a comment\n",
            parse_manuscript,
            no_state_setup
        ),
        vec![(
            None,
            ManuscriptItem::Instruction(ProgramInstruction {
                tag: Some(SymbolName {
                    canonical: "CODEHERE".to_string(),
                    //as_used: "CODE HERE".to_string(),
                }),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o205_u32),
                },]
            })
        ),]
    );
}

#[test]
fn test_manuscript_with_real_arrow_tag() {
    const INPUT: &str = "HERE→207\n"; // real Unicode rightward arrow (U+2192).
    assert_eq!(
        parse_successfully_with(INPUT, parse_manuscript, no_state_setup),
        vec![(
            None,
            ManuscriptItem::Instruction(ProgramInstruction {
                tag: Some(SymbolName {
                    canonical: "HERE".to_string(),
                    //as_used: "HERE".to_string(),
                }),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o207_u32),
                },]
            })
        ),]
    );
}

#[test]
fn test_end_of_file() {
    parse_successfully_with("", ek::expect_end_of_file, no_state_setup);
}

#[test]
fn test_not_end_of_file() {
    let (_, errors) = ek::parse_with("something-is-here", ek::expect_end_of_file, no_state_setup);
    assert!(!errors.is_empty());
}

#[cfg(test)]
fn assemble_nonempty_valid_input(input: &str) -> (Vec<ManuscriptBlock>, SymbolTable) {
    let mut symtab = SymbolTable::new();
    let mut errors: Vec<Error> = Vec::new();
    let result: Result<Vec<ManuscriptBlock>, AssemblerFailure> =
        source_file(input, &mut symtab, &mut errors);
    if !errors.is_empty() {
        dbg!(&errors);
        panic!("assemble_nonempty_valid_input: errors were reported");
    }
    let instructions = result.expect("input should be valid");
    (instructions, symtab)
}

#[cfg(test)]
fn assemble_literal(input: &str, expected: &InstructionFragment) {
    let (blocks, symtab) = assemble_nonempty_valid_input(input);
    if !symtab.is_empty() {
        panic!("no symbol should have been generated");
    }
    match blocks.as_slice() {
        [ManuscriptBlock { origin: _, items }] => match items.as_slice() {
            [ManuscriptItem::Instruction(ProgramInstruction {
                tag: None,
                holdbit: HoldBit::Unspecified,
                parts,
            })] => match parts.as_slice() {
                [only_frag] => {
                    if only_frag == expected {
                        return;
                    }
                }
                _ => (),
            },
            _ => (),
        },
        _ => (),
    }
    panic!(
        "expected one instruction containing {:?}, got {:?}",
        &expected, &blocks,
    );
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
        "⁺³⁶\n", // 36, superscript
        &InstructionFragment {
            elevation: Elevation::Superscript,
            value: Unsigned36Bit::from(0o36_u32),
        },
    );
}

#[test]
fn test_assemble_octal_subscript_literal() {
    assemble_literal(
        "₁₃\n", // without sign
        &InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o13_u32),
        },
    );
    assemble_literal(
        "₊₁₃\n", // with optional + sign
        &InstructionFragment {
            elevation: Elevation::Subscript,
            value: Unsigned36Bit::from(0o13_u32),
        },
    );
}

#[test]
fn test_metacommand_decimal() {
    assert_eq!(
        parse_successfully_with("☛☛DECIMAL", metacommand, no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)
    );
}

#[test]
fn test_metacommand_dec() {
    assert_eq!(
        parse_successfully_with("☛☛DEC", metacommand, no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)
    );
}

#[test]
fn test_metacommand_oct() {
    assert_eq!(
        parse_successfully_with("☛☛OCT", metacommand, no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)
    );
}

#[test]
fn test_metacommand_octal() {
    assert_eq!(
        parse_successfully_with("☛☛OCTAL", metacommand, no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)
    );
}

#[test]
fn test_metacommand_dec_changes_default_base() {
    const INPUT: &str = concat!("10\n", "☛☛DECIMAL\n", "10  ** Ten\n");
    let (blocks, _) = assemble_nonempty_valid_input(INPUT);
    if let [ManuscriptBlock {
        origin: None,
        items,
    }] = blocks.as_slice()
    {
        if let [ManuscriptItem::Instruction(ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: first_parts,
        }), ManuscriptItem::MetaCommand(ManuscriptMetaCommand::BaseChange(
            NumeralMode::Decimal,
        )), ManuscriptItem::Instruction(ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: second_parts,
        })] = items.as_slice()
        {
            assert_eq!(
                &first_parts.as_slice(),
                &[InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o10_u32),
                }],
            );
            assert_eq!(
                &second_parts.as_slice(),
                &[InstructionFragment {
                    elevation: Elevation::Normal,
                    value: Unsigned36Bit::from(0o12_u32),
                }],
            );
            return;
        }
    }
    panic!(
        "expected two items with value 10 octal and 12 octal, got {:?}",
        &blocks,
    );
}

#[test]
fn test_opcode_instruction_fragment() {
    let expected_instruction = Instruction::from(&SymbolicInstruction {
        held: false,
        configuration: Unsigned5Bit::ZERO,
        opcode: Opcode::Aux,
        index: Unsigned6Bit::ZERO,
        operand_address: OperandAddress::Direct(Address::ZERO),
    });
    assert_eq!(
        parse_successfully_with("AUX", opcode_instruction_fragment, no_state_setup),
        InstructionFragment {
            elevation: Elevation::Normal,
            value: expected_instruction.bits(),
        }
    );
}

#[test]
fn program_instruction_with_opcode() {
    let (maybe_origin, item) =
        parse_successfully_with("15000| ²¹IOS₅₂ 30106", program_instruction, no_state_setup);
    assert_eq!(maybe_origin, Some(Origin(Address::from(u18!(0o15000)))));
    if let ManuscriptItem::Instruction(inst) = item {
        assert_eq!(inst.value(), u36!(0o210452_030106));
    } else {
        panic!("Wrong instruction result: {item:?}")
    }
}

#[test]
fn hold() {
    assert_eq!(
        parse_successfully_with(" h", maybe_hold, no_state_setup),
        HoldBit::Hold
    );
    assert_eq!(
        parse_successfully_with(" :", maybe_hold, no_state_setup),
        HoldBit::Hold
    );
}

#[test]
fn not_hold() {
    assert_eq!(
        //parse_successfully_with(" ℏ", maybe_hold, no_state_setup),
        parse_successfully_with("ℏ", maybe_hold, no_state_setup),
        HoldBit::NotHold
    );
    assert_eq!(
        //parse_successfully_with(" ̅h", maybe_hold, no_state_setup),
        parse_successfully_with("̅h", maybe_hold, no_state_setup),
        HoldBit::NotHold
    );
}

#[test]
fn unspecified_hold() {
    assert_eq!(
        parse_successfully_with("", maybe_hold, no_state_setup),
        HoldBit::Unspecified
    );
}
