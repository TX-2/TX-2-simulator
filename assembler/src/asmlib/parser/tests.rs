use std::fmt::{Debug, Display};

use base::prelude::*;
use base::u36;

use chumsky::error::Rich;
use chumsky::prelude::*;

use super::super::ast::{
    Block, Elevation, Expression, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock,
    ManuscriptMetaCommand, Origin, ProgramInstruction, SourceFile, Statement, SymbolName,
};
use super::super::state::NumeralMode;
use super::super::symtab::SymbolTable;
use super::symex::{parse_multi_syllable_symex, parse_symex};
use super::*;

fn errors_as_string<'a, T: Display>(errors: &[Rich<'a, T>]) -> String {
    let n = errors.len();
    errors
        .iter()
        .enumerate()
        .map(|(i, e)| (i + 1, e))
        .map(|(i, e)| format!("error {i}/{n}: {e}\n"))
        .collect::<String>()
}

#[cfg(test)]
fn parse_test_input<'a, I, O, P>(input_text: I, parser: P) -> Result<O, String>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    P: Parser<'a, I, O, Extra<'a, char>>,
{
    let mut state = NumeralMode::default();
    let (output, errors) = parser
        .parse_with_state(input_text, &mut state)
        .into_output_errors();
    if !errors.is_empty() {
        Err(errors_as_string(errors.as_slice()))
    } else {
        match output {
            Some(out) => Ok(out),
            None => Err("the parser generated no output".to_string()),
        }
    }
}

#[cfg(test)]
pub(crate) fn parse_successfully_with<'a, I, O, P, M>(input: I, parser: P, mut state_setup: M) -> O
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + Display + Clone + Debug,
    P: Parser<'a, I, O, Extra<'a, char>>,
    M: FnMut(&mut NumeralMode),
    O: Debug,
{
    dbg!(&input);
    let mut state = NumeralMode::default();
    state_setup(&mut state);
    let (output, errors) = parser
        .parse_with_state(input.clone(), &mut state)
        .into_output_errors();
    if !errors.is_empty() {
        dbg!(&output);
        panic!(
            "{} unexpected parse errors for input '{input}': {:?}",
            errors.len(),
            &errors_as_string(errors.as_slice())
        );
    }
    match output {
        Some(out) => out,
        None => panic!("the parser generated no output"),
    }
}

#[cfg(test)]
fn no_state_setup(_: &mut NumeralMode) {}

#[cfg(test)]
fn set_decimal_mode(state: &mut NumeralMode) {
    state.set_numeral_mode(NumeralMode::Decimal);
}

#[test]
fn test_normal_literal_oct_defaultmode() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("402", normal_literal(), no_state_setup),
        LiteralValue::from((Elevation::Normal, u36!(0o402),))
    );
}

#[test]
fn test_normal_literal_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with("402·", normal_literal(), set_decimal_mode),
        LiteralValue::from((
            Elevation::Normal,
            Unsigned36Bit::from(0o402_u32), // note: octal
        ))
    );
}

#[test]
fn test_normal_literal_dec_defaultmode() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("402·", normal_literal(), no_state_setup),
        LiteralValue::from((Elevation::Normal, Unsigned36Bit::from(402_u32),))
    );
}

#[test]
fn test_normal_literald_ec_decmode() {
    assert_eq!(
        // Decimal is the default if there was a previous ☛☛DECIMAL
        parse_successfully_with("402", normal_literal(), set_decimal_mode),
        LiteralValue::from((Elevation::Normal, Unsigned36Bit::from(402_u32),))
    );
}

#[test]
fn test_superscript_literal_oct() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("³⁶", superscript_literal(), no_state_setup),
        LiteralValue::from((Elevation::Superscript, Unsigned36Bit::from(0o36_u32),))
    );
    assert_eq!(
        // U+207A: superscript plus
        parse_successfully_with("\u{207A}³⁶", superscript_literal(), no_state_setup),
        LiteralValue::from((Elevation::Superscript, Unsigned36Bit::from(0o36_u32),))
    );
}

#[test]
fn test_superscript_literal_dec_defaultmode() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("³⁶̇ ", superscript_literal(), no_state_setup),
        LiteralValue::from((
            Elevation::Superscript,
            Unsigned36Bit::from(36_u32), // decimal
        ))
    );
}

#[test]
fn test_superscript_literal_oct_defaultmode() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("³⁶", superscript_literal(), no_state_setup),
        LiteralValue::from((
            Elevation::Superscript,
            Unsigned36Bit::from(0o36_u32), // octal
        ))
    );
}

#[test]
fn test_superscript_literal_dec_decmode() {
    // Simulate a previous ☛☛DECIMAL.
    assert_eq!(
        parse_successfully_with("³⁶", superscript_literal(), set_decimal_mode),
        LiteralValue::from((
            Elevation::Superscript,
            Unsigned36Bit::from(36_u32), // decimal
        ))
    );
}

#[test]
fn test_subscript_literal_oct_defaultmode_nosign() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("₃₁", subscript_literal(), no_state_setup),
        LiteralValue::from((Elevation::Subscript, Unsigned36Bit::from(0o31_u32),))
    );
}

#[test]
fn test_subscript_literal_oct_defaultmode_plus() {
    assert_eq!(
        parse_successfully_with("₊₁₃", subscript_literal(), no_state_setup),
        LiteralValue::from((Elevation::Subscript, Unsigned36Bit::from(0o13_u32),))
    );
}

#[test]
fn test_subscript_literal_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with("₃₁.", subscript_literal(), set_decimal_mode),
        LiteralValue::from((Elevation::Subscript, Unsigned36Bit::from(0o31_u32),))
    );
}

#[test]
fn test_subscript_literal_dec() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("₃₁.", subscript_literal(), no_state_setup),
        LiteralValue::from((Elevation::Subscript, Unsigned36Bit::from(31_u32),))
    );
}

#[test]
fn test_program_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("₃₁", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((Elevation::Subscript, Unsigned36Bit::from(0o31_u32),))
    );
    assert_eq!(
        parse_successfully_with("⁶³", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((Elevation::Superscript, Unsigned36Bit::from(0o63_u32),))
    );
    assert_eq!(
        parse_successfully_with("6510", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((Elevation::Normal, Unsigned36Bit::from(0o6510_u32),))
    );
}

#[test]
fn test_assemble_octal_literal() {
    assert_eq!(
        parse_successfully_with(" 177777 ", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((Elevation::Normal, Unsigned36Bit::from(0o177777_u32))),
    );
}

#[test]
fn test_program_instruction() {
    assert_eq!(
        parse_successfully_with("⁶673₃₁", program_instruction(), no_state_setup),
        ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: vec![
                InstructionFragment::from((Elevation::Superscript, Unsigned36Bit::from(0o6_u32),)),
                InstructionFragment::from((Elevation::Normal, Unsigned36Bit::from(0o673_u32),)),
                InstructionFragment::from((Elevation::Subscript, Unsigned36Bit::from(0o31_u32),)),
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
        let got: SymbolName = parse_successfully_with(input, parse_symex(), no_state_setup);
        assert_eq!(got.canonical, expected);
    }
}

#[test]
fn test_empty_manuscript() {
    assert_eq!(
        parse_successfully_with("", source_file(), no_state_setup),
        SourceFile {
            blocks: vec![],
            punch: None
        }
    )
}

#[test]
fn test_comment() {
    parse_successfully_with("**THIS IS A COMMENT", terminal::comment(), no_state_setup);
}

#[test]
fn test_comment_does_not_eat_newline() {
    let comment_text = "**COMMENT";
    let comment_with_newline = format!("{comment_text}\n");
    match parse_test_input(comment_with_newline.as_str(), terminal::comment()) {
        Err(_) => (), // expected outcome
        Ok(out) => {
            panic!("attempt to parse '{comment_with_newline:?}' as a comment unexpectedly succeeded (the newline was not rejected), producing {out:?}");
        }
    }
    // Verify that the above (expected) error was in fact caused by
    // the presence of the newline.
    parse_test_input(comment_text, terminal::comment())
        .expect("should be able to successfully parse the comment itself");
}

#[test]
fn test_manuscript_line_with_bare_literal() {
    assert_eq!(
        parse_successfully_with("1", manuscript_line(), no_state_setup),
        ManuscriptLine::Code(
            None,
            Statement::Instruction(ProgramInstruction {
                tag: None,
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment::from((
                    Elevation::Normal,
                    Unsigned36Bit::from(1_u32),
                ))]
            })
        )
    );
}

#[test]
fn test_manuscript_with_bare_literal() {
    assert_eq!(
        parse_successfully_with("1\n", source_file(), no_state_setup),
        SourceFile {
            punch: None,
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(ProgramInstruction {
                    tag: None,
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::from((
                        Elevation::Normal,
                        Unsigned36Bit::from(1_u32),
                    ))],
                }),]
            }]
        }
    );
}

#[test]
fn test_terminated_manuscript_line_with_bare_literal() {
    let expected_line = ManuscriptLine::Code(
        None,
        Statement::Instruction(ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: vec![InstructionFragment::from((
                Elevation::Normal,
                Unsigned36Bit::from(1_u32),
            ))],
        }),
    );

    assert_eq!(
        parse_successfully_with("1", manuscript_line(), no_state_setup),
        expected_line
    );
    assert_eq!(
        parse_successfully_with("1\n", terminated_manuscript_line(), no_state_setup),
        Some(expected_line)
    );
    assert_eq!(
        parse_successfully_with("\n", terminated_manuscript_line(), no_state_setup),
        None
    );
}

#[test]
fn test_manuscript_without_tag() {
    assert_eq!(
        parse_successfully_with(
            "673 ** This is a comment\n71\n",
            source_file(),
            no_state_setup
        ),
        SourceFile {
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![
                    Statement::Instruction(ProgramInstruction {
                        tag: None,
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            Elevation::Normal,
                            Unsigned36Bit::from(0o673_u32),
                        ))],
                    }),
                    Statement::Instruction(ProgramInstruction {
                        tag: None,
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            Elevation::Normal,
                            Unsigned36Bit::from(0o71_u32),
                        ))],
                    }),
                ]
            }],
            punch: None,
        }
    );
}

#[test]
fn test_symbol_name_one_syllable() {
    assert_eq!(
        parse_successfully_with("START4", symbol(), no_state_setup),
        SymbolName {
            canonical: "START4".to_string(),
            //as_used: "START4".to_string(),
        }
    );
}

#[test]
fn test_symbol_name_two_syllables() {
    assert_eq!(
        parse_successfully_with("TWO WORDS", symbol(), no_state_setup),
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
            source_file(),
            no_state_setup
        ),
        SourceFile {
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(ProgramInstruction {
                    tag: Some(SymbolName {
                        canonical: "START4".to_string(),
                        //as_used: "START4".to_string(),
                    }),
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::from((
                        Elevation::Normal,
                        Unsigned36Bit::from(0o205_u32),
                    )),]
                })]
            }],
            punch: None
        }
    );
}

#[test]
fn test_manuscript_with_origin() {
    assert_eq!(
        parse_successfully_with(
            "100 | 202 ** literal value\n",
            source_file(),
            no_state_setup
        ),
        SourceFile {
            punch: None,
            blocks: vec![ManuscriptBlock {
                origin: Some(Origin(Address::new(u18!(0o100)))),
                statements: vec![Statement::Instruction(ProgramInstruction {
                    tag: None,
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::from((
                        Elevation::Normal,
                        Unsigned36Bit::from(0o202_u32),
                    ))]
                })],
            }]
        }
    );
}

#[test]
fn test_arrow() {
    assert_eq!(
        parse_successfully_with("FOO->", tag_definition(), no_state_setup),
        SymbolName {
            canonical: "FOO".to_string()
        }
    );
    assert_eq!(
        parse_successfully_with("BAR  -> ", tag_definition(), no_state_setup),
        SymbolName {
            canonical: "BAR".to_string(),
        }
    );
}

#[test]
fn test_multi_syllable_tag() {
    let inst = parse_successfully_with("CODE HERE->205 ", program_instruction(), no_state_setup);
    assert_eq!(
        inst,
        ProgramInstruction {
            tag: Some(SymbolName {
                canonical: "CODEHERE".to_string(),
                //as_used: "CODE HERE".to_string(),
            }),
            holdbit: HoldBit::Unspecified,
            parts: vec![InstructionFragment {
                value: Expression::from(LiteralValue::from((Elevation::Normal, u36!(0o205)))),
            }]
        }
    );
}

#[test]
fn test_manuscript_with_multi_syllable_tag() {
    assert_eq!(
        parse_successfully_with(
            "CODE HERE->205 ** Also a comment\n",
            source_file(),
            no_state_setup
        ),
        SourceFile {
            punch: None,
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(ProgramInstruction {
                    tag: Some(SymbolName {
                        canonical: "CODEHERE".to_string(),
                    }),
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::from((
                        Elevation::Normal,
                        Unsigned36Bit::from(0o205_u32),
                    ))]
                })]
            }]
        }
    );
}

#[test]
fn test_manuscript_line_with_real_arrow_tag() {
    const INPUT: &str = "HERE→207"; // real Unicode rightward arrow (U+2192).
    assert_eq!(
        parse_successfully_with(INPUT, manuscript_line(), no_state_setup),
        ManuscriptLine::Code(
            None,
            Statement::Instruction(ProgramInstruction {
                tag: Some(SymbolName {
                    canonical: "HERE".to_string(),
                }),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment {
                    value: Expression::from((Elevation::Normal, u36!(0o207)))
                }],
            })
        )
    );
}

#[test]
fn test_manuscript_with_real_arrow_tag() {
    const INPUT: &str = "HERE→207\n"; // real Unicode rightward arrow (U+2192).
    assert_eq!(
        parse_successfully_with(INPUT, source_file(), no_state_setup),
        SourceFile {
            punch: None,
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(ProgramInstruction {
                    tag: Some(SymbolName {
                        canonical: "HERE".to_string(),
                        //as_used: "HERE".to_string(),
                    }),
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::from((
                        Elevation::Normal,
                        Unsigned36Bit::from(0o207_u32),
                    ))]
                })]
            }]
        }
    );
}

#[test]
fn test_assignment_literal() {
    const INPUTS: &[&'static str] = &[
        "FOO=2",
        "FOO =2",
        "F O O = 2", // spaces are also allowed inside symexes.
    ];
    for input in INPUTS {
        dbg!(&input);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            Statement::Assignment(
                SymbolName {
                    canonical: "FOO".to_string(),
                },
                Expression::Literal(LiteralValue::from((Elevation::Normal, u36!(2))))
            )
        )
    }
}

#[test]
fn test_assignment_superscript() {
    const INPUTS: &[&'static str] = &[
        // Unicode code point B2 is a superscript 2.
        "FOO=\u{00B2}",
        "FOO =\u{00B2}",
        "F O O = \u{00B2}", // spaces are also allowed inside symexes.
    ];
    for input in INPUTS {
        dbg!(input);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            Statement::Assignment(
                SymbolName {
                    canonical: "FOO".to_string(),
                },
                Expression::Literal(LiteralValue::from((Elevation::Superscript, u36!(2))))
            )
        )
    }
}

#[test]
fn test_assignment_subscript() {
    const INPUTS: &[&'static str] = &[
        // Unicode code point 2083 is a subscript 3.
        "FOO=\u{2083}",
        "FOO =\u{2083}",
        "F O O = \u{2083}", // spaces are also allowed inside symexes.
    ];
    for input in INPUTS {
        dbg!(&input);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            Statement::Assignment(
                SymbolName {
                    canonical: "FOO".to_string(),
                },
                Expression::Literal(LiteralValue::from((Elevation::Subscript, u36!(3))))
            )
        )
    }
}

#[test]
fn test_assignment_lines() {
    assert_eq!(
        parse_successfully_with(
            concat!(
                "FOO=2\n",
                // The trailing space on the next line is there to ensure we don't
                // have a regression in end_of_line (which previously didn't permit
                // trailing spaces).
                "    BAR = 1 \n", // leading and trailing spaces are allowed.
                // we also want to make sure we can parse a comment
                // preceded by a space, and regular instructions
                // following an assignment.
                "6 ** WE PUT A NON-ASSIGNMENT HERE TO CHECK WE CAN PARSE REGULAR INSTRUCTIONS\n"
            ),
            source_file(),
            no_state_setup
        ),
        SourceFile {
            punch: None,
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![
                    Statement::Assignment(
                        SymbolName {
                            canonical: "FOO".to_string(),
                        },
                        Expression::Literal(LiteralValue::from((Elevation::Normal, u36!(2))))
                    ),
                    Statement::Assignment(
                        SymbolName {
                            canonical: "BAR".to_string(),
                        },
                        Expression::Literal(LiteralValue::from((Elevation::Normal, u36!(1))))
                    ),
                    Statement::Instruction(ProgramInstruction {
                        tag: None,
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment {
                            value: Expression::Literal(LiteralValue::from((
                                Elevation::Normal,
                                u36!(6)
                            )))
                        }]
                    })
                ]
            }]
        }
    );
}

#[test]
fn test_assignment_origin() {
    const INPUT: &str = concat!("FOO=1000\n", "1000|4\n",);
    let tree = parse_successfully_with(INPUT, source_file(), no_state_setup);
    assert_eq!(
        tree,
        SourceFile {
            punch: None,
            blocks: vec![
                ManuscriptBlock {
                    origin: None,
                    statements: vec![Statement::Assignment(
                        SymbolName {
                            canonical: "FOO".to_string()
                        },
                        Expression::Literal(LiteralValue::from((Elevation::Normal, u36!(0o1000))))
                    ),]
                },
                ManuscriptBlock {
                    origin: Some(Origin(Address::new(u18!(0o1000)))),
                    statements: vec![Statement::Instruction(ProgramInstruction {
                        tag: None,
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((Elevation::Normal, u36!(4),))]
                    })]
                }
            ]
        }
    );
}

#[test]
fn test_metacommand_decimal() {
    assert_eq!(
        parse_successfully_with("☛☛DECIMAL", metacommand(), no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)
    );
}

#[test]
fn test_metacommand_dec() {
    assert_eq!(
        parse_successfully_with("☛☛DEC", metacommand(), no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)
    );
}

#[test]
fn test_metacommand_oct() {
    assert_eq!(
        parse_successfully_with("☛☛OCT", metacommand(), no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)
    );
}

#[test]
fn test_metacommand_octal() {
    assert_eq!(
        parse_successfully_with("☛☛OCTAL", metacommand(), no_state_setup),
        ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)
    );
}

#[test]
fn test_opcode() {
    let expected_instruction = Instruction::from(&SymbolicInstruction {
        held: false,
        configuration: Unsigned5Bit::ZERO,
        opcode: Opcode::Aux,
        index: Unsigned6Bit::ZERO,
        operand_address: OperandAddress::Direct(Address::ZERO),
    });
    assert_eq!(
        parse_successfully_with("AUX", super::terminal::opcode(), no_state_setup),
        LiteralValue::from((Elevation::Normal, expected_instruction.bits(),))
    );
}

#[test]
fn test_multi_syllable_symex() {
    assert_eq!(
        parse_successfully_with("FOO", parse_multi_syllable_symex(), no_state_setup),
        "FOO"
    );
    assert_eq!(
        parse_successfully_with("FOO BAR", parse_multi_syllable_symex(), no_state_setup),
        "FOOBAR"
    );
    assert_eq!(
        parse_successfully_with("FOO  BAR", parse_multi_syllable_symex(), no_state_setup),
        "FOOBAR"
    );
}

#[test]
fn program_instruction_with_opcode() {
    let nosyms = SymbolTable::default();
    assert_eq!(
        parse_successfully_with("²¹IOS₅₂ 30106", program_instruction(), no_state_setup)
            .value(&nosyms),
        Ok(u36!(0o210452_030106))
    );
}

#[test]
fn test_hold() {
    assert_eq!(
        parse_successfully_with("h", terminal::hold(), no_state_setup),
        HoldBit::Hold
    );
    assert_eq!(
        parse_successfully_with(":", terminal::hold(), no_state_setup),
        HoldBit::Hold
    );
}

#[test]
fn not_hold() {
    assert_eq!(
        parse_successfully_with("ℏ", terminal::hold(), no_state_setup),
        HoldBit::NotHold
    );
    assert_eq!(
        parse_successfully_with("̅h", terminal::hold(), no_state_setup),
        HoldBit::NotHold
    );
}

#[test]
fn test_end_of_line() {
    fn good(s: &str) {
        parse_successfully_with(s, end_of_line(), no_state_setup);
    }
    good("\n");
    good(" \n");
    good("\t\n");
    good("\n\n");
    good("\n \n");
    good("**COMMENT\n");
    good("**COMMENT \n");
    good(" **COMMENT \n");
    good(" **COMMENT1 \n**COMMENT2\n");
    good(" **COMMENT1 \n**COMMENT2\n\n");
}
