use std::fmt::{Debug, Display};
#[cfg(test)]
use std::ops::Range;

use base::prelude::*;
use base::u36;

use chumsky::error::Rich;
use chumsky::prelude::*;

use super::super::ast::{
    Expression, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock, ManuscriptMetaCommand,
    Origin, SourceFile, Statement, TaggedProgramInstruction, UntaggedProgramInstruction,
};
#[cfg(test)]
use super::Span;

use super::super::eval::SymbolLookup;
use super::super::state::NumeralMode;
use super::super::symbol::SymbolName;
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
    let mut state = Default::default();
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
    let mut state = Default::default();
    state_setup(&mut state);
    let (output, errors) = parser
        .parse_with_state(input.clone(), &mut state)
        .into_output_errors();
    if !errors.is_empty() {
        dbg!(&output);
        panic!(
            "{} unexpected parse errors for input '{input}': {:?}",
            errors.len(),
            &errors.as_slice()
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

#[cfg(test)]
fn span(range: Range<usize>) -> Span {
    Span::from(range)
}

#[test]
fn test_normal_literal_oct_defaultmode() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("402", literal(Script::Normal), no_state_setup),
        LiteralValue::from((span(0..3), Script::Normal, u36!(0o402),))
    );
}

#[test]
fn test_normal_literal_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with("402@dot@", literal(Script::Normal), set_decimal_mode),
        LiteralValue::from((
            span(0..8),
            Script::Normal,
            Unsigned36Bit::from(0o402_u32), // note: octal
        ))
    );
}

#[test]
fn test_normal_literal_dec_defaultmode() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("402·", literal(Script::Normal), no_state_setup),
        LiteralValue::from((span(0..5), Script::Normal, Unsigned36Bit::from(402_u32),))
    );
    assert_eq!(
        parse_successfully_with("402@dot@", literal(Script::Normal), no_state_setup),
        LiteralValue::from((span(0..8), Script::Normal, Unsigned36Bit::from(402_u32),))
    );
}

#[test]
fn test_normal_literald_ec_decmode() {
    assert_eq!(
        // Decimal is the default if there was a previous ☛☛DECIMAL
        parse_successfully_with("402", literal(Script::Normal), set_decimal_mode),
        LiteralValue::from((span(0..3), Script::Normal, Unsigned36Bit::from(402_u32),))
    );
}

#[test]
fn test_superscript_literal_oct() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("³⁶", literal(Script::Super), no_state_setup),
        LiteralValue::from((span(0..5), Script::Super, Unsigned36Bit::from(0o36_u32),))
    );
    assert_eq!(
        // U+207A: superscript plus
        parse_successfully_with("\u{207A}³⁶", literal(Script::Super), no_state_setup),
        LiteralValue::from((span(0..8), Script::Super, Unsigned36Bit::from(0o36_u32),))
    );
}

#[test]
fn test_superscript_literal_dec_defaultmode() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("³⁶̇ ", literal(Script::Super), no_state_setup),
        LiteralValue::from((
            span(0..8),
            Script::Super,
            Unsigned36Bit::from(36_u32), // decimal
        ))
    );
}

#[test]
fn test_superscript_literal_oct_defaultmode() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("³⁶", literal(Script::Super), no_state_setup),
        LiteralValue::from((
            span(0..5),
            Script::Super,
            Unsigned36Bit::from(0o36_u32), // octal
        ))
    );
}

#[test]
fn test_superscript_literal_dec_decmode() {
    // Simulate a previous ☛☛DECIMAL.
    assert_eq!(
        parse_successfully_with("³⁶", literal(Script::Super), set_decimal_mode),
        LiteralValue::from((
            span(0..5),
            Script::Super,
            Unsigned36Bit::from(36_u32), // decimal
        ))
    );
}

#[test]
fn test_subscript_literal_oct_defaultmode_nosign() {
    // No trailing dot on a number indicates octal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("₃₁", literal(Script::Sub), no_state_setup),
        LiteralValue::from((span(0..6), Script::Sub, Unsigned36Bit::from(0o31_u32),))
    );
}

#[test]
fn test_subscript_literal_oct_defaultmode_plus() {
    assert_eq!(
        parse_successfully_with("₊₁₃", literal(Script::Sub), no_state_setup),
        LiteralValue::from((span(0..9), Script::Sub, Unsigned36Bit::from(0o13_u32),))
    );
}

#[test]
fn test_subscript_literal_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with("₃₁@sub_dot@", literal(Script::Sub), set_decimal_mode),
        LiteralValue::from((span(0..15), Script::Sub, Unsigned36Bit::from(0o31_u32),))
    );
}

#[test]
fn test_subscript_literal_dec() {
    // A trailing dot on a number indicates decimal base (unless there
    // was a previous ☛☛DECIMAL).
    assert_eq!(
        parse_successfully_with("₃₁@sub_dot@", literal(Script::Sub), no_state_setup),
        LiteralValue::from((span(0..15), Script::Sub, Unsigned36Bit::from(31_u32),))
    );
}

#[test]
fn test_program_instruction_fragment() {
    assert_eq!(
        parse_successfully_with("₃₁", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((span(0..6), Script::Sub, Unsigned36Bit::from(0o31_u32),))
    );
    assert_eq!(
        parse_successfully_with("⁶³", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((span(0..5), Script::Super, Unsigned36Bit::from(0o63_u32),))
    );
    assert_eq!(
        parse_successfully_with("6510", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((span(0..4), Script::Normal, Unsigned36Bit::from(0o6510_u32),))
    );
}

#[test]
fn test_assemble_octal_literal() {
    assert_eq!(
        parse_successfully_with(" 177777 ", program_instruction_fragment(), no_state_setup),
        InstructionFragment::from((
            span(1..7),
            Script::Normal,
            Unsigned36Bit::from(0o177777_u32)
        )),
    );
}

#[test]
fn test_program_instruction() {
    assert_eq!(
        parse_successfully_with("⁶673₃₁", tagged_program_instruction(), no_state_setup),
        TaggedProgramInstruction {
            tag: None,
            instruction: UntaggedProgramInstruction {
                span: span(0..12),
                holdbit: HoldBit::Unspecified,
                parts: vec![
                    InstructionFragment::from((
                        span(0..3),
                        Script::Super,
                        Unsigned36Bit::from(0o6_u32),
                    )),
                    InstructionFragment::from((
                        span(3..6),
                        Script::Normal,
                        Unsigned36Bit::from(0o673_u32),
                    )),
                    InstructionFragment::from((
                        span(6..12),
                        Script::Sub,
                        Unsigned36Bit::from(0o31_u32),
                    )),
                ]
            }
        },
    );
}

#[test]
fn test_parse_symex() {
    for (input, expected) in [
        ("SOMENAME", "SOMENAME"),
        ("SOME NAME", "SOMENAME"),
        ("Q", "Q"),
        ("@Q@", "Q"),
        // OK to use a reserved identifier if it is not the first
        // syllable in the symex.
        ("TEST A", "TESTA"),
        // If there's no space after it, it's not reserved
        ("ATEST", "ATEST"),
        // Otherwise, the reserved identifier is the whole of it.
        ("B", "B"),
        ("@B@", "B"),
        // A symex can contain digits and can even start with one.
        ("HOP2IT", "HOP2IT"),
        ("HOP 2 IT", "HOP2IT"),
        ("HOP @2@ IT", "HOP2IT"),
        ("4REAL", "4REAL"),
        // Some lower case letters are supported
        ("j2", "j2"),
        // Dot, underscore
        ("@dot@q", "\u{00B7}q"),
        ("@dot@_q", "\u{00B7}_q"),
        // Single quotes are allowed too
        ("SCRATCH 'N' SNIFF", "SCRATCH'N'SNIFF"),
        ("SCRATCH @apostrophe@N@apostrophe@ SNIFF", "SCRATCH'N'SNIFF"),
        ("F '", "F'"),
    ] {
        let got: SymbolName =
            parse_successfully_with(input, parse_symex(Script::Normal), no_state_setup);
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
            Statement::Instruction(TaggedProgramInstruction {
                tag: None,
                instruction: UntaggedProgramInstruction {
                    span: span(0..1),
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::from((
                        span(0..1),
                        Script::Normal,
                        Unsigned36Bit::from(1_u32),
                    ))]
                }
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(0..1),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(0..1),
                            Script::Normal,
                            Unsigned36Bit::from(1_u32),
                        ))],
                    }
                })]
            }]
        }
    );
}

#[test]
fn test_terminated_manuscript_line_with_bare_literal() {
    let expected_line = ManuscriptLine::Code(
        None,
        Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instruction: UntaggedProgramInstruction {
                span: span(0..1),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment::from((
                    span(0..1),
                    Script::Normal,
                    Unsigned36Bit::from(1_u32),
                ))],
            },
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
                    Statement::Instruction(TaggedProgramInstruction {
                        tag: None,
                        instruction: UntaggedProgramInstruction {
                            span: span(0..4),
                            holdbit: HoldBit::Unspecified,
                            parts: vec![InstructionFragment::from((
                                span(0..3),
                                Script::Normal,
                                Unsigned36Bit::from(0o673_u32),
                            ))],
                        }
                    }),
                    Statement::Instruction(TaggedProgramInstruction {
                        tag: None,
                        instruction: UntaggedProgramInstruction {
                            span: span(25..27),
                            holdbit: HoldBit::Unspecified,
                            parts: vec![InstructionFragment::from((
                                span(25..27),
                                Script::Normal,
                                Unsigned36Bit::from(0o71_u32),
                            ))],
                        }
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
        parse_successfully_with("START4", symbol(Script::Normal), no_state_setup),
        SymbolName {
            canonical: "START4".to_string(),
            //as_used: "START4".to_string(),
        }
    );
}

#[test]
fn test_symbol_name_two_syllables() {
    assert_eq!(
        parse_successfully_with("TWO WORDS", symbol(Script::Normal), no_state_setup),
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: Some(Tag {
                        name: SymbolName {
                            canonical: "START4".to_string(),
                        },
                        span: span(0..6),
                    }),
                    instruction: UntaggedProgramInstruction {
                        span: span(12..16),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(12..15),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        )),]
                    }
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
                origin: Some(Origin::Literal(span(0..3), Address::new(u18!(0o100)))),
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(5..10),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(6..9),
                            Script::Normal,
                            Unsigned36Bit::from(0o202_u32),
                        ))]
                    }
                })]
            }]
        }
    );
}

#[test]
fn test_arrow() {
    assert_eq!(
        parse_successfully_with("FOO->", tag_definition(), no_state_setup),
        Tag {
            name: SymbolName {
                canonical: "FOO".to_string()
            },
            span: span(0..3),
        }
    );
    assert_eq!(
        parse_successfully_with("BAR  -> ", tag_definition(), no_state_setup),
        Tag {
            name: SymbolName {
                canonical: "BAR".to_string(),
            },
            span: span(0..3),
        }
    );
}

#[test]
fn test_multi_syllable_tag() {
    let inst = parse_successfully_with(
        "CODE HERE->205 ",
        tagged_program_instruction(),
        no_state_setup,
    );
    assert_eq!(
        inst,
        TaggedProgramInstruction {
            tag: Some(Tag {
                name: SymbolName {
                    canonical: "CODEHERE".to_string(),
                },
                span: span(0..9),
            }),
            instruction: UntaggedProgramInstruction {
                span: span(11..15),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment {
                    value: Expression::from(LiteralValue::from((
                        span(11..14),
                        Script::Normal,
                        u36!(0o205)
                    ))),
                }]
            }
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: Some(Tag {
                        name: SymbolName {
                            canonical: "CODEHERE".to_string(),
                        },
                        span: span(0..9),
                    }),
                    instruction: UntaggedProgramInstruction {
                        span: span(11..15),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(11..14),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        ))]
                    }
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
            Statement::Instruction(TaggedProgramInstruction {
                tag: Some(Tag {
                    name: SymbolName {
                        canonical: "HERE".to_string(),
                    },
                    span: span(0..4),
                }),
                instruction: UntaggedProgramInstruction {
                    span: span(7..10),
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment {
                        value: Expression::from((span(7..10), Script::Normal, u36!(0o207)))
                    }],
                }
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: Some(Tag {
                        name: SymbolName {
                            canonical: "HERE".to_string(),
                        },
                        span: span(0..4),
                    }),
                    instruction: UntaggedProgramInstruction {
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(7..10),
                            Script::Normal,
                            Unsigned36Bit::from(0o207_u32),
                        ))],
                        span: span(7..10),
                    }
                })]
            }]
        }
    );
}

#[test]
fn test_assignment_literal() {
    const INPUTS: &[(&'static str, usize)] = &[
        ("FOO=2", 4),
        ("FOO =2", 5),
        ("F O O = 2", 8), // spaces are also allowed inside symexes.
    ];
    for (input, begin) in INPUTS {
        dbg!(&input);
        dbg!(&begin);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            Statement::Assignment(
                span(0..(*begin + 1)),
                SymbolName {
                    canonical: "FOO".to_string(),
                },
                Expression::Literal(LiteralValue::from((
                    span(*begin..(*begin + 1)),
                    Script::Normal,
                    u36!(2)
                )))
            )
        )
    }
}

#[test]
fn test_assignment_superscript() {
    const INPUTS: &[(&'static str, usize, usize)] = &[
        // Unicode code point B2 is a superscript 2.
        ("FOO=\u{00B2}", 4, 6),
        ("FOO =\u{00B2}", 5, 7),
        ("F O O = \u{00B2}", 8, 10), // spaces are also allowed inside symexes.
    ];
    for (input, val_begin, val_end) in INPUTS {
        dbg!(input);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            Statement::Assignment(
                span(0..*val_end),
                SymbolName {
                    canonical: "FOO".to_string(),
                },
                Expression::Literal(LiteralValue::from((
                    span(*val_begin..*val_end),
                    Script::Super,
                    u36!(2)
                )))
            )
        )
    }
}

#[test]
fn test_assignment_subscript() {
    const INPUTS: &[(&'static str, usize, usize)] = &[
        // Unicode code point 2083 is a subscript 3.
        ("FOO=\u{2083}", 4, 7),
        ("FOO =\u{2083}", 5, 8),
        ("F O O = \u{2083}", 8, 11), // spaces are also allowed inside symexes.
    ];
    for (input, val_begin, val_end) in INPUTS {
        dbg!(&input);
        dbg!(&val_begin);
        dbg!(&val_end);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            Statement::Assignment(
                span(0..*val_end),
                SymbolName {
                    canonical: "FOO".to_string(),
                },
                Expression::Literal(LiteralValue::from((
                    span(*val_begin..*val_end),
                    Script::Sub,
                    u36!(3)
                )))
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
                        span(0..5),
                        SymbolName {
                            canonical: "FOO".to_string(),
                        },
                        Expression::Literal(LiteralValue::from((
                            span(4..5),
                            Script::Normal,
                            u36!(2)
                        )))
                    ),
                    Statement::Assignment(
                        span(6..17),
                        SymbolName {
                            canonical: "BAR".to_string(),
                        },
                        Expression::Literal(LiteralValue::from((
                            span(16..17),
                            Script::Normal,
                            u36!(1)
                        )))
                    ),
                    Statement::Instruction(TaggedProgramInstruction {
                        tag: None,
                        instruction: UntaggedProgramInstruction {
                            span: span(19..21),
                            holdbit: HoldBit::Unspecified,
                            parts: vec![InstructionFragment {
                                value: Expression::Literal(LiteralValue::from((
                                    span(19..20),
                                    Script::Normal,
                                    u36!(6)
                                )))
                            }]
                        }
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
                        span(0..8),
                        SymbolName {
                            canonical: "FOO".to_string()
                        },
                        Expression::Literal(LiteralValue::from((
                            span(4..8),
                            Script::Normal,
                            u36!(0o1000)
                        )))
                    ),]
                },
                ManuscriptBlock {
                    origin: Some(Origin::Literal(span(9..13), Address::new(u18!(0o1000)))),
                    statements: vec![Statement::Instruction(TaggedProgramInstruction {
                        tag: None,
                        instruction: UntaggedProgramInstruction {
                            span: span(14..15),
                            holdbit: HoldBit::Unspecified,
                            parts: vec![InstructionFragment::from((
                                span(14..15),
                                Script::Normal,
                                u36!(4),
                            ))]
                        }
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
        LiteralValue::from((span(0..3), Script::Normal, expected_instruction.bits(),))
    );
}

#[test]
fn test_multi_syllable_symex() {
    assert_eq!(
        parse_successfully_with(
            "FOO",
            parse_multi_syllable_symex(Script::Normal),
            no_state_setup
        ),
        "FOO"
    );
    assert_eq!(
        parse_successfully_with(
            "FOO BAR",
            parse_multi_syllable_symex(Script::Normal),
            no_state_setup
        ),
        "FOOBAR"
    );
    assert_eq!(
        parse_successfully_with(
            "FOO  BAR",
            parse_multi_syllable_symex(Script::Normal),
            no_state_setup
        ),
        "FOOBAR"
    );
}

#[derive(Default, Debug, PartialEq, Eq)]
struct UnexpectedLookup {}

#[derive(Default, PartialEq, Eq)]
struct NoSymbols {}

impl SymbolLookup for NoSymbols {
    type Error = UnexpectedLookup;

    fn lookup(
        &mut self,
        _name: &SymbolName,
        _span: Span,
        _context: &crate::eval::SymbolContext,
    ) -> Result<Unsigned36Bit, Self::Error> {
        Err(UnexpectedLookup {})
    }
}

#[test]
fn program_instruction_with_opcode() {
    let mut nosyms = NoSymbols::default();
    assert_eq!(
        parse_successfully_with(
            "²¹IOS₅₂ 30106",
            tagged_program_instruction(),
            no_state_setup
        )
        .value(&mut nosyms),
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

/// Verify that the substitutions in Jurij's assembler -> HTML
/// converter are correctly understood.
#[test]
fn test_subs() {
    fn check(input: &str, expected: &str) {
        let got = parse_successfully_with(
            input,
            parse_multi_syllable_symex(Script::Normal),
            no_state_setup,
        );
        if got != expected {
            panic!("Parsing '{input}' with parse_multi_syllable_symex, expected '{expected}', got '{got}'");
        }
    }

    check("@beta@", "β");
    check("@gamma@", "γ");
    check("@alpha@", "α");
    check("@delta@", "Δ");
    check("@eps@", "ε");
    check("@lambda@", "λ");
    for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".chars() {
        // We use a leading X here to avoid collisions with register
        // names.
        let s = format!("X{ch}");
        check(&s, &s);
    }
    check("@y@", "y");
    // @dot@ expands to a center dot, not a full stop as in Jurij's script.
    check("@dot@", "·");
    // untested: @+@, @hamb@, @times@, @arr@, @hand@, @pipe@, @rect_dash@, @circled_v@, @sup@, @minus@
}

#[test]
fn test_greek_letters() {
    fn check(input: &str) {
        let got = parse_successfully_with(
            input,
            parse_multi_syllable_symex(Script::Normal),
            no_state_setup,
        );
        if got != input {
            panic!("Parsing '{input}' with parse_multi_syllable_symex, expected '{input}', got '{got}'");
        }
    }
    check("β");
    check("γ");
    check("α");
    check("Δ");
    check("ε");
    check("λ");
}
