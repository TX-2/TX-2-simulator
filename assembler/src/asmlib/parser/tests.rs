#[cfg(test)]
use std::ops::Range;
use std::{collections::BTreeMap, fmt::Debug};

use base::prelude::*;
use base::u36;

use chumsky::{error::Rich, input::ValueInput, prelude::Input, Parser};

use super::super::{
    ast::{
        Atom, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock, ManuscriptMetaCommand,
        Origin, SourceFile, Statement, TaggedProgramInstruction, UntaggedProgramInstruction,
    },
    eval::{Evaluate, HereValue},
    parser::symex::{parse_multi_syllable_symex, parse_symex},
    state::NumeralMode,
    symbol::SymbolName,
    symtab::{make_empty_rc_block_for_test, LookupOperation, SymbolTable},
};
use super::*;

#[cfg(test)]
use super::Span;

type StateInitFn = fn(s: &mut NumeralMode);

#[cfg(test)]
pub(crate) fn parse_successfully_with<'a, O, P>(
    input: &'a str,
    parser: P,
    state_setup: StateInitFn,
) -> O
where
    P: Parser<'a, super::Mi, O, Extra<'a>>,
    O: Debug,
{
    dbg!(&input);

    let (output, errors) = tokenize_and_parse_with(input, state_setup, parser);
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
        parse_successfully_with("³⁶@sup_dot@", literal(Script::Super), no_state_setup),
        LiteralValue::from((
            span(0..14),
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
fn test_program_instruction_fragments() {
    assert_eq!(
        parse_successfully_with("₃₁", program_instruction_fragments(), no_state_setup),
        vec![InstructionFragment::from((
            span(0..6),
            Script::Sub,
            Unsigned36Bit::from(0o31_u32),
        ))],
    );
    assert_eq!(
        parse_successfully_with("⁶³", program_instruction_fragments(), no_state_setup),
        vec![InstructionFragment::from((
            span(0..5),
            Script::Super,
            Unsigned36Bit::from(0o63_u32),
        ))]
    );
    assert_eq!(
        parse_successfully_with("6510", program_instruction_fragments(), no_state_setup),
        vec![InstructionFragment::from((
            span(0..4),
            Script::Normal,
            Unsigned36Bit::from(0o6510_u32),
        ))]
    );
}

#[test]
fn test_assemble_octal_literal() {
    assert_eq!(
        parse_successfully_with(" 177777 ", program_instruction_fragments(), no_state_setup),
        vec![InstructionFragment::from((
            span(1..7),
            Script::Normal,
            Unsigned36Bit::from(0o177777_u32)
        )),]
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
        ("Q", "Q"),
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
        ("HOP2", "HOP2"),
        ("HOP2IT", "HOP2IT"),
        ("HOP 2", "HOP2"),
        ("HOP 2@dot@", "HOP2·"),
        ("HOP 2 IT", "HOP2IT"),
        ("4REAL", "4REAL"),
        // Some lower case letters are supported
        ("j2", "j2"),
        // Dot, underscore
        ("@dot@x", "\u{00B7}x"),
        ("q@dot@q", "q\u{00B7}q"),
        ("@dot@_X", "\u{00B7}_X"),
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
            blocks: BTreeMap::new(),
            macros: vec![],
            punch: None,
        }
    )
}

#[test]
fn test_blank_lines_manuscript() {
    assert_eq!(
        parse_successfully_with("\n\n", source_file(), no_state_setup),
        SourceFile {
            blocks: BTreeMap::new(),
            macros: vec![],
            punch: None,
        }
    )
}

#[test]
fn test_comments_only_manuscript() {
    assert_eq!(
        parse_successfully_with(
            concat!(
                "** THIS PROGRAM CONTAINS ONLY BLANK LINES\n",
                "\n",
                "** AND SOME LINES CONTAINING ONLY SPACES\n",
                "    \n",
                "** OR TABS\n",
                "\t\t\t\n",
                "** AND SOME COMMENTS.\n",
                "    ** SOME COMMENTS ARE PRECEDED BY BLANKS\n",
            ),
            source_file(),
            no_state_setup
        ),
        SourceFile {
            blocks: BTreeMap::new(),
            macros: vec![],
            punch: None,
        }
    )
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

fn manuscript_blocks(blocks: Vec<ManuscriptBlock>) -> BTreeMap<BlockIdentifier, ManuscriptBlock> {
    let mut result = BTreeMap::new();
    for (i, block) in blocks.into_iter().enumerate() {
        result.insert(BlockIdentifier::Number(i), block);
    }
    result
}

#[test]
fn test_manuscript_with_bare_literal() {
    assert_eq!(
        parse_successfully_with("1\n", source_file(), no_state_setup),
        SourceFile {
            punch: None,
            blocks: manuscript_blocks(vec![ManuscriptBlock {
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
            }]),
            macros: vec![],
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
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: None,
                statements: vec![
                    Statement::Instruction(TaggedProgramInstruction {
                        tag: None,
                        instruction: UntaggedProgramInstruction {
                            span: span(0..3),
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
            }]),
            macros: vec![],
            punch: None,
        }
    );
}

/// Comments can appear both inside and outside RC-blocks (see TX-2
/// User Handbook section 6-2.8 "Special Symbols").
#[test]
fn test_comment_in_rc_block() {
    assert_eq!(
        parse_successfully_with(
            "{1 ** ONE} ** EXTERNAL COMMENT\n",
            source_file(),
            no_state_setup
        ),
        SourceFile {
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(0..10),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from(ArithmeticExpression::from(
                            Atom::RcRef(
                                span(0..10),
                                Box::new(InstructionFragment::Arithmetic(
                                    ArithmeticExpression::from(Atom::Literal(LiteralValue::from(
                                        (span(1..2), Script::Normal, Unsigned36Bit::ONE),
                                    )))
                                ))
                            )
                        ))]
                    }
                })]
            }]),
            macros: vec![],
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
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: Some(Tag {
                        name: SymbolName {
                            canonical: "START4".to_string(),
                        },
                        span: span(0..6),
                    }),
                    instruction: UntaggedProgramInstruction {
                        span: span(12..15),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(12..15),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        )),]
                    }
                })]
            }]),
            macros: vec![],
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
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: Some(Origin::Literal(span(0..3), Address::new(u18!(0o100)))),
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(6..9),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(6..9),
                            Script::Normal,
                            Unsigned36Bit::from(0o202_u32),
                        ))]
                    }
                })]
            }]),
            macros: vec![],
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
                span: span(11..14),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment::Arithmetic(ArithmeticExpression::from(
                    Atom::from(LiteralValue::from((
                        span(11..14),
                        Script::Normal,
                        u36!(0o205)
                    )))
                ))]
            }
        }
    );
}

#[test]
fn test_infix_minus_interpreted_as_subtraction() {
    let head = Atom::Literal(LiteralValue::from((span(0..1), Script::Normal, u36!(4))));
    for (input, rhs_span) in [("4 - 2", 4..5), ("4-2", 2..3), ("4 -2", 3..4)] {
        let tail = vec![(
            Operator::Subtract,
            Atom::Literal(LiteralValue::from((
                span(rhs_span),
                Script::Normal,
                u36!(2),
            ))),
        )];
        assert_eq!(
            parse_successfully_with(input, arithmetic_expression(Script::Normal), no_state_setup),
            ArithmeticExpression::with_tail(head.clone(), tail),
            "incorrect parse for '{input}'"
        );
    }
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
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: Some(Tag {
                        name: SymbolName {
                            canonical: "CODEHERE".to_string(),
                        },
                        span: span(0..9),
                    }),
                    instruction: UntaggedProgramInstruction {
                        span: span(11..14),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment::from((
                            span(11..14),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        ))]
                    }
                })]
            }]),
            macros: vec![],
        }
    );
}

fn atom_to_fragment(atom: Atom) -> InstructionFragment {
    InstructionFragment::Arithmetic(ArithmeticExpression::from(atom))
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
                    parts: vec![atom_to_fragment(Atom::from((
                        span(7..10),
                        Script::Normal,
                        u36!(0o207)
                    )))],
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
            blocks: manuscript_blocks(vec![ManuscriptBlock {
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
            }]),
            macros: Vec::new(),
        }
    );
}

#[cfg(test)]
fn assignment_of_literal(name: &str, assignment_span: Span, literal: LiteralValue) -> Statement {
    let symbol = SymbolName {
        canonical: name.to_string(),
    };
    Statement::Assignment(
        assignment_span,
        symbol,
        UntaggedProgramInstruction {
            span: span((literal.span().start)..(assignment_span.end)),
            holdbit: HoldBit::Unspecified,
            parts: vec![atom_to_fragment(Atom::Literal(literal))],
        },
    )
}

#[test]
fn test_assignment_literal() {
    const INPUTS: &[(&str, usize)] = &[
        ("FOO=2", 4),
        ("FOO =2", 5),
        ("F O O = 2", 8), // spaces are also allowed inside symexes.
    ];
    for (input, begin) in INPUTS {
        dbg!(&input);
        dbg!(&begin);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            assignment_of_literal(
                "FOO",
                span(0..(*begin + 1)),
                LiteralValue::from((span(*begin..(*begin + 1)), Script::Normal, u36!(2))),
            )
        )
    }
}

#[test]
fn test_assignment_superscript() {
    const INPUTS: &[(&str, usize, usize)] = &[
        // Unicode code point B2 is a superscript 2.
        ("FOO=\u{00B2}", 4, 6),
        ("FOO =\u{00B2}", 5, 7),
        ("F O O = \u{00B2}", 8, 10), // spaces are also allowed inside symexes.
    ];
    for (input, val_begin, val_end) in INPUTS {
        dbg!(input);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            assignment_of_literal(
                "FOO",
                span(0..*val_end),
                LiteralValue::from((span(*val_begin..*val_end), Script::Super, u36!(2))),
            )
        );
    }
}

#[test]
fn test_assignment_subscript() {
    const INPUTS: &[(&str, usize, usize)] = &[
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
            assignment_of_literal(
                "FOO",
                span(0..*val_end),
                LiteralValue::from((span(*val_begin..*val_end), Script::Sub, u36!(3))),
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
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: None,
                statements: vec![
                    assignment_of_literal(
                        "FOO",
                        span(0..5),
                        LiteralValue::from((span(4..5), Script::Normal, u36!(2))),
                    ),
                    assignment_of_literal(
                        "BAR",
                        span(10..17),
                        LiteralValue::from((span(16..17), Script::Normal, u36!(1))),
                    ),
                    Statement::Instruction(TaggedProgramInstruction {
                        tag: None,
                        instruction: UntaggedProgramInstruction {
                            span: span(19..20),
                            holdbit: HoldBit::Unspecified,
                            parts: vec![atom_to_fragment(Atom::Literal(LiteralValue::from((
                                span(19..20),
                                Script::Normal,
                                u36!(6)
                            ))))]
                        }
                    })
                ]
            }]),
            macros: Vec::new(),
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
            blocks: manuscript_blocks(vec![
                ManuscriptBlock {
                    origin: None,
                    statements: vec![assignment_of_literal(
                        "FOO",
                        span(0..8),
                        LiteralValue::from((span(4..8), Script::Normal, u36!(0o1000))),
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
            ]),
            macros: Vec::new(),
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

type Extra<'a> = super::Extra<'a>;
fn extract_sole_expr<'a>(
    mut frags: Vec<InstructionFragment>,
    span: Span,
) -> Result<ArithmeticExpression, Rich<'a, Tok>> {
    if let Some(InstructionFragment::Arithmetic(expr)) = frags.pop() {
        if frags.is_empty() {
            Ok(expr)
        } else {
            Err(Rich::custom(span, "too many fragments".to_string()))
        }
    } else {
        Err(Rich::custom(
            span,
            "expected one fragment, not zero".to_string(),
        ))
    }
}

/// This is just a convenience function so that our tests'
/// expected-values don't have to contain so much boiler-plate.
fn arithmetic_expression<'a, I>(
    _script_required: Script,
) -> impl Parser<'a, I, ArithmeticExpression, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    program_instruction_fragments().try_map(extract_sole_expr)
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
        parse_successfully_with(
            "AUX",
            super::program_instruction_fragments(),
            no_state_setup
        ),
        vec![InstructionFragment::Arithmetic(ArithmeticExpression::from(
            Atom::Literal(LiteralValue::from((
                span(0..3),
                Script::Normal,
                expected_instruction.bits(),
            )))
        ))],
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

#[test]
fn program_instruction_with_opcode() {
    let mut nosyms = SymbolTable::new(None);
    let mut op = LookupOperation::default();
    let mut rc_block =
        make_empty_rc_block_for_test(Address::from(Unsigned18Bit::from(0o20_000u16)));
    assert_eq!(
        parse_successfully_with(
            "²¹IOS₅₂ 30106",
            tagged_program_instruction(),
            no_state_setup
        )
        .evaluate(
            &HereValue::Address(Address::ZERO),
            &mut nosyms,
            &mut rc_block,
            &mut op
        ),
        Ok(u36!(0o210452_030106))
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

#[test]
fn test_annotation() {
    assert_eq!(
        parse_successfully_with("[hello] FOO", parse_symex(Script::Normal), no_state_setup),
        SymbolName::from("FOO".to_string()),
    );
}

#[test]
fn test_logical_or_naked() {
    assert_eq!(
        parse_successfully_with("∨", terminal::operator(Script::Normal), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_logical_or_glyph_normal() {
    assert_eq!(
        parse_successfully_with("@or@", terminal::operator(Script::Normal), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_logical_or_glyph_subscript() {
    assert_eq!(
        parse_successfully_with("@sub_or@", terminal::operator(Script::Sub), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_logical_or_glyph_superscript() {
    assert_eq!(
        parse_successfully_with(
            "@sup_or@",
            terminal::operator(Script::Super),
            no_state_setup
        ),
        Operator::LogicalOr
    );
}

#[test]
fn test_arithmetic_expression_head_only() {
    assert_eq!(
        parse_successfully_with("6", arithmetic_expression(Script::Normal), no_state_setup),
        ArithmeticExpression::from(Atom::Literal(LiteralValue::from((
            span(0..1),
            Script::Normal,
            u36!(6)
        ))))
    );
}

#[test]
fn test_arithmetic_expression_two_atoms() {
    let head = Atom::Literal(LiteralValue::from((span(0..1), Script::Normal, u36!(4))));
    let tail = vec![(
        Operator::LogicalOr,
        Atom::Literal(LiteralValue::from((span(6..7), Script::Normal, u36!(2)))),
    )];
    assert_eq!(
        parse_successfully_with(
            "4 ∨ 2",
            arithmetic_expression(Script::Normal),
            no_state_setup
        ),
        ArithmeticExpression::with_tail(head, tail),
    );
}

#[test]
fn test_parenthesised_expression() {
    assert_eq!(
        parse_successfully_with("(1)", arithmetic_expression(Script::Normal), no_state_setup),
        ArithmeticExpression::from(Atom::Parens(
            Script::Normal,
            Box::new(ArithmeticExpression::from(Atom::from(LiteralValue::from(
                (span(1..2), Script::Normal, u36!(1))
            ))))
        ))
    );
}

#[test]
fn test_macro_arg() {
    assert_eq!(
        parse_successfully_with("@hand@A01", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A01".to_string()),
            span: span(0..9),
            preceding_terminator: '☛',
        }
    );

    assert_eq!(
        parse_successfully_with("@dot@A02", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A02".to_string()),
            span: span(0..8),
            preceding_terminator: '·',
        }
    );

    assert_eq!(
        parse_successfully_with("=A03", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A03".to_string()),
            span: span(0..4),
            preceding_terminator: '=',
        }
    );

    assert_eq!(
        parse_successfully_with("@arr@A04", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A04".to_string()),
            span: span(0..8),
            preceding_terminator: '→',
        }
    );

    assert_eq!(
        // Alternative form for convenience (and consistency with
        // what we allow for tags).
        parse_successfully_with("->A04", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A04".to_string()),
            span: span(0..5),
            preceding_terminator: '→',
        }
    );

    assert_eq!(
        parse_successfully_with("|A05", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A05".to_string()),
            span: span(0..4),
            preceding_terminator: '|',
        }
    );

    assert_eq!(
        parse_successfully_with("⊃A06", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A06".to_string()),
            span: span(0..6),
            preceding_terminator: '⊃',
        }
    );

    assert_eq!(
        parse_successfully_with("≡A07", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A07".to_string()),
            span: span(0..6),
            preceding_terminator: '≡',
        }
    );

    assert_eq!(
        parse_successfully_with("@hamb@A07", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A07".to_string()),
            span: span(0..9),
            preceding_terminator: '≡',
        }
    );

    assert_eq!(
        parse_successfully_with("~A08", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A08".to_string()),
            span: span(0..4),
            preceding_terminator: '~',
        }
    );

    assert_eq!(
        parse_successfully_with("<A09", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A09".to_string()),
            span: span(0..4),
            preceding_terminator: '<',
        }
    );

    assert_eq!(
        parse_successfully_with(">A10", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A10".to_string()),
            span: span(0..4),
            preceding_terminator: '>',
        }
    );

    assert_eq!(
        parse_successfully_with("∩A11", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A11".to_string()),
            span: span(0..6),
            preceding_terminator: '∩',
        }
    );

    assert_eq!(
        parse_successfully_with("∪A12", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A12".to_string()),
            span: span(0..6),
            preceding_terminator: '∪',
        }
    );

    assert_eq!(
        parse_successfully_with("/A13", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A13".to_string()),
            span: span(0..4),
            preceding_terminator: '/',
        }
    );

    assert_eq!(
        parse_successfully_with("×A14", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A14".to_string()),
            span: span(0..5),
            preceding_terminator: '×',
        }
    );

    assert_eq!(
        parse_successfully_with("∨A15", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A15".to_string()),
            span: span(0..6),
            preceding_terminator: '∨',
        }
    );

    assert_eq!(
        parse_successfully_with("∧A16", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A16".to_string()),
            span: span(0..6),
            preceding_terminator: '∧',
        }
    );
}

#[test]
fn test_macro_args() {
    assert_eq!(
        parse_successfully_with("=X@hand@YZ@arr@P", macro_arguments(), no_state_setup),
        MacroArguments::OneOrMore(vec![
            MacroArgument {
                name: SymbolName::from("X".to_string()),
                span: span(0..2),
                preceding_terminator: '=',
            },
            MacroArgument {
                name: SymbolName::from("YZ".to_string()),
                span: span(2..10),
                preceding_terminator: '☛',
            },
            MacroArgument {
                name: SymbolName::from("P".to_string()),
                span: span(10..16),
                preceding_terminator: '→',
            },
        ])
    );
}

#[test]
fn test_macro_definition_with_empty_body() {
    // TBD: where in a macro definition are comments allowed?
    let got = parse_successfully_with(
        concat!("☛☛DEF MYMACRO≡\n", "☛☛EMD"), // deliberately no terminating newline, see comment in macro_definition().
        macro_definition(),
        no_state_setup,
    );
    let expected = MacroDefinition {
        name: SymbolName::from("MYMACRO".to_string()),
        args: MacroArguments::Zero('≡'),
        body: Vec::new(), // no body
        span: span(0..30),
    };
    assert_eq!(got, expected);
}

#[test]
fn test_macro_definition_with_trivial_body() {
    let got = parse_successfully_with(
        concat!(
            "☛☛DEF JUST|A\n",
            // This macro definition has a one-line body.
            "A ** This is the only line in the body.\n",
            "☛☛EMD" // deliberately no terminating newline, see comment in macro_definition().
        ),
        macro_definition(),
        no_state_setup,
    );
    let expected = MacroDefinition {
        name: SymbolName::from("JUST".to_string()),
        args: MacroArguments::OneOrMore(vec![MacroArgument {
            name: SymbolName::from("A".to_string()),
            span: span(14..16),
            preceding_terminator: '|',
        }]),
        body: vec![Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instruction: UntaggedProgramInstruction {
                span: span(17..18),
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment::Arithmetic(ArithmeticExpression::from(
                    Atom::Symbol(
                        span(17..18),
                        Script::Normal,
                        SymbolName::from("A".to_string()),
                    ),
                ))],
            },
        })],
        span: span(0..66),
    };
    assert_eq!(got, expected);
}

#[test]
fn test_macro_definition_as_entire_source_file() {
    let got = parse_successfully_with("☛☛DEF JUST|A\nA\n☛☛EMD\n", source_file(), no_state_setup);
    let expected = SourceFile {
        blocks: BTreeMap::new(), // empty
        macros: vec![MacroDefinition {
            name: SymbolName {
                canonical: "JUST".to_string(),
            },
            args: MacroArguments::OneOrMore(vec![MacroArgument {
                name: SymbolName {
                    canonical: "A".to_string(),
                },
                span: span(14..16),
                preceding_terminator: '|',
            }]),
            body: vec![Statement::Instruction(TaggedProgramInstruction {
                tag: None,
                instruction: UntaggedProgramInstruction {
                    span: span(17..18),
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::Symbol(
                            span(17..18),
                            Script::Normal,
                            SymbolName {
                                canonical: "A".to_string(),
                            },
                        ),
                    ))],
                },
            })],
            span: span(0..28),
        }],
        punch: None,
    };
    assert_eq!(got, expected);
}
