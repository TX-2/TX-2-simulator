#[cfg(test)]
use std::ops::Range;
use std::{collections::BTreeMap, fmt::Debug};

use base::prelude::*;
use base::u36;

use chumsky::Parser;

use super::super::{
    ast::{
        Atom, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock, ManuscriptMetaCommand,
        Origin, SourceFile, Statement, TaggedProgramInstruction, UntaggedProgramInstruction,
    },
    eval::{make_empty_rc_block_for_test, Evaluate, HereValue},
    parser::symex::{parse_multi_syllable_symex, parse_symex},
    state::NumeralMode,
    symbol::SymbolName,
    symtab::{LookupOperation, SymbolTable},
    types::*,
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

#[cfg(test)]
fn parse_single_instruction_fragment(input: &str) -> InstructionFragment {
    let output = parse_multiple_instruction_fragments(input);
    let mut it = output.into_iter();
    match it.next() {
        Some(inst) => match it.next() {
            None => inst,
            Some(succ) => {
                panic!("expected single instruction, got unexpected {succ:?}")
            }
        },
        None => {
            panic!("expected single instruction, got zero parse output items")
        }
    }
}

#[cfg(test)]
fn parse_multiple_instruction_fragments(input: &str) -> Vec<InstructionFragment> {
    let parse_result = parse_comma_expression(input);
    parse_result
        .into_iter()
        .map(|comma_delimited_insn| match comma_delimited_insn {
            CommaDelimitedInstruction {
                leading_commas: _,
                instruction:
                    UntaggedProgramInstruction {
                        span: _,
                        holdbit: _,
                        inst,
                    },
                trailing_commas: _,
            } => inst,
        })
        .collect()
}

#[test]
fn test_program_instruction_fragments() {
    assert_eq!(
        parse_single_instruction_fragment("₃₁"),
        InstructionFragment::from((span(0..6), Script::Sub, Unsigned36Bit::from(0o31_u32),)),
    );
    assert_eq!(
        parse_single_instruction_fragment("⁶³"),
        InstructionFragment::Config(ConfigValue::Literal(
            span(0..5),
            Unsigned36Bit::from(0o63_u32)
        ))
    );
    assert_eq!(
        parse_single_instruction_fragment("6510"),
        InstructionFragment::from((span(0..4), Script::Normal, Unsigned36Bit::from(0o6510_u32),))
    );
}

#[test]
fn test_assemble_octal_literal() {
    assert_eq!(
        parse_single_instruction_fragment(" 177777 "),
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
        parse_multiple_instruction_fragments("⁶673₃₁"),
        vec![
            InstructionFragment::Config(ConfigValue::Literal(span(0..3), u36!(0o6),)),
            InstructionFragment::from(
                (span(3..6), Script::Normal, Unsigned36Bit::from(0o673_u32),)
            ),
            InstructionFragment::from((span(6..12), Script::Sub, Unsigned36Bit::from(0o31_u32),)),
        ]
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
        // Dot.  We don't use underscore because on the Lincoln Writer
        // this character does not advance the carriage.  IOW it
        // generates a combined symex.
        ("@dot@x", "\u{00B7}x"),
        ("q@dot@q", "q\u{00B7}q"),
        // Single quotes are allowed too
        ("@dot@'X", "\u{00B7}'X"),
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
                "    \n",
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
            Statement::Instruction(TaggedProgramInstruction::single(
                None,
                UntaggedProgramInstruction {
                    span: span(0..1),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::from((
                        span(0..1),
                        Script::Normal,
                        Unsigned36Bit::from(1_u32),
                    ))
                }
            ))
        )
    );
}

fn manuscript_blocks(blocks: Vec<ManuscriptBlock>) -> BTreeMap<BlockIdentifier, ManuscriptBlock> {
    let mut result = BTreeMap::new();
    for (i, block) in blocks.into_iter().enumerate() {
        result.insert(BlockIdentifier::from(i), block);
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                    None,
                    UntaggedProgramInstruction {
                        span: span(0..1),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from((
                            span(0..1),
                            Script::Normal,
                            Unsigned36Bit::from(1_u32),
                        )),
                    }
                ))]
            }]),
            macros: vec![],
        }
    );
}

#[test]
fn test_terminated_manuscript_line_with_bare_literal() {
    let expected_line = ManuscriptLine::Code(
        None,
        Statement::Instruction(TaggedProgramInstruction::single(
            None,
            UntaggedProgramInstruction {
                span: span(0..1),
                holdbit: HoldBit::Unspecified,
                inst: InstructionFragment::from((
                    span(0..1),
                    Script::Normal,
                    Unsigned36Bit::from(1_u32),
                )),
            },
        )),
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
                    Statement::Instruction(TaggedProgramInstruction::single(
                        None,
                        UntaggedProgramInstruction {
                            span: span(0..3),
                            holdbit: HoldBit::Unspecified,
                            inst: InstructionFragment::from((
                                span(0..3),
                                Script::Normal,
                                Unsigned36Bit::from(0o673_u32),
                            )),
                        }
                    )),
                    Statement::Instruction(TaggedProgramInstruction::single(
                        None,
                        UntaggedProgramInstruction {
                            span: span(25..27),
                            holdbit: HoldBit::Unspecified,
                            inst: InstructionFragment::from((
                                span(25..27),
                                Script::Normal,
                                Unsigned36Bit::from(0o71_u32),
                            )),
                        }
                    )),
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                    None,
                    UntaggedProgramInstruction {
                        span: span(0..10),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from(ArithmeticExpression::from(Atom::RcRef(
                            span(0..10),
                            vec![InstructionFragment::Arithmetic(ArithmeticExpression::from(
                                Atom::Literal(LiteralValue::from((
                                    span(1..2),
                                    Script::Normal,
                                    Unsigned36Bit::ONE
                                ),))
                            ))]
                        )))
                    }
                ))]
            }]),
            macros: vec![],
            punch: None,
        }
    );
}

#[test]
fn test_symbol_name_one_syllable() {
    assert_eq!(
        parse_successfully_with(
            "START4",
            named_symbol_or_here(Script::Normal),
            no_state_setup
        ),
        SymbolOrHere::from("START4")
    );
}

#[test]
fn test_symbol_name_two_syllables() {
    assert_eq!(
        parse_successfully_with(
            "TWO WORDS",
            named_symbol_or_here(Script::Normal),
            no_state_setup
        ),
        SymbolOrHere::from("TWOWORDS")
    );
}

#[test]
fn test_manuscript_with_single_syllable_tag() {
    assert_eq!(
        parse_successfully_with(
            "START4 -> 205 ** comment here\n",
            source_file(),
            no_state_setup
        ),
        SourceFile {
            blocks: manuscript_blocks(vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                    Some(Tag {
                        name: SymbolName {
                            canonical: "START4".to_string(),
                        },
                        span: span(0..6),
                    }),
                    UntaggedProgramInstruction {
                        span: span(10..13),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from((
                            span(10..13),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        )),
                    }
                ))]
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                    None,
                    UntaggedProgramInstruction {
                        span: span(6..9),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from((
                            span(6..9),
                            Script::Normal,
                            Unsigned36Bit::from(0o202_u32),
                        ))
                    }
                ))]
            }]),
            macros: vec![],
        }
    );
}

#[cfg(test)]
fn parse_tagged_instruction(input: &str) -> TaggedProgramInstruction {
    let stmt = parse_successfully_with(input, statement(), no_state_setup);
    if let Statement::Instruction(inst) = stmt {
        inst
    } else {
        panic!("expected {input} to be parsed as an instruction, but instead we got {stmt:?}");
    }
}

#[cfg(test)]
fn parse_comma_expression(input: &str) -> Vec<CommaDelimitedInstruction> {
    let stmt = parse_successfully_with(input, super::statement(), no_state_setup);
    if let Statement::Instruction(TaggedProgramInstruction {
        tag: _,
        instructions,
    }) = stmt
    {
        instructions
    } else {
        panic!("expected {input} to be parsed as comma-separated instructions, but instead we got {stmt:?}");
    }
}

#[test]
fn test_arrow() {
    assert_eq!(
        parse_tagged_instruction("FOO->0"),
        TaggedProgramInstruction {
            tag: Some(Tag {
                name: SymbolName {
                    canonical: "FOO".to_string()
                },
                span: span(0..3),
            }),
            instructions: vec![CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(5..6),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::Literal(LiteralValue::from((
                            span(5..6),
                            Script::Normal,
                            Unsigned36Bit::ZERO
                        )))
                    )),
                },
                trailing_commas: None
            }]
        }
    );
    assert_eq!(
        parse_tagged_instruction("BAR  -> 1"),
        TaggedProgramInstruction {
            tag: Some(Tag {
                name: SymbolName {
                    canonical: "BAR".to_string(),
                },
                span: span(0..3),
            }),
            instructions: vec![CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(8..9),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::Literal(LiteralValue::from((span(8..9), Script::Normal, u36!(1),)))
                    )),
                },
                trailing_commas: None
            }]
        }
    );
}

#[test]
fn test_multi_syllable_tag() {
    assert_eq!(
        parse_tagged_instruction("CODE HERE->205 "),
        TaggedProgramInstruction::single(
            Some(Tag {
                name: SymbolName {
                    canonical: "CODEHERE".to_string(),
                },
                span: span(0..9),
            }),
            UntaggedProgramInstruction {
                span: span(11..14),
                holdbit: HoldBit::Unspecified,
                inst: InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                    LiteralValue::from((span(11..14), Script::Normal, u36!(0o205)))
                )))
            }
        )
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
            parse_arithmetic_expression(input),
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                    Some(Tag {
                        name: SymbolName {
                            canonical: "CODEHERE".to_string(),
                        },
                        span: span(0..9),
                    }),
                    UntaggedProgramInstruction {
                        span: span(11..14),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from((
                            span(11..14),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        ))
                    }
                ))]
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
            Statement::Instruction(TaggedProgramInstruction::single(
                Some(Tag {
                    name: SymbolName {
                        canonical: "HERE".to_string(),
                    },
                    span: span(0..4),
                }),
                UntaggedProgramInstruction {
                    span: span(7..10),
                    holdbit: HoldBit::Unspecified,
                    inst: atom_to_fragment(Atom::from((span(7..10), Script::Normal, u36!(0o207)))),
                }
            ))
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
                statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                    Some(Tag {
                        name: SymbolName {
                            canonical: "HERE".to_string(),
                        },
                        span: span(0..4),
                    }),
                    UntaggedProgramInstruction {
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from((
                            span(7..10),
                            Script::Normal,
                            Unsigned36Bit::from(0o207_u32),
                        )),
                        span: span(7..10),
                    }
                ))]
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
        EqualityValue::from(vec![CommaDelimitedInstruction {
            leading_commas: None,
            instruction: UntaggedProgramInstruction {
                span: span((literal.span().start)..(assignment_span.end)),
                holdbit: HoldBit::Unspecified,
                inst: atom_to_fragment(Atom::Literal(literal)),
            },
            trailing_commas: None,
        }]),
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
            Statement::Assignment(
                span(0..*val_end),
                SymbolName {
                    canonical: "FOO".to_string()
                },
                EqualityValue::from(vec![CommaDelimitedInstruction {
                    leading_commas: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(*val_begin..*val_end),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::Config(ConfigValue::Literal(
                            span(*val_begin..*val_end),
                            u36!(0o2)
                        )),
                    },
                    trailing_commas: None
                }])
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
        dbg!(&input.len());
        dbg!(input.char_indices().collect::<Vec<_>>());
        dbg!(&val_begin);
        dbg!(&val_end);
        assert_eq!(
            parse_successfully_with(*input, statement(), no_state_setup),
            assignment_of_literal(
                "FOO",
                span(0..*val_end),
                LiteralValue::from((span(*val_begin..*val_end), Script::Sub, u36!(3))),
            ),
            "Incorrect parse of input {input:?}"
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
                    Statement::Instruction(TaggedProgramInstruction::single(
                        None,
                        UntaggedProgramInstruction {
                            span: span(19..20),
                            holdbit: HoldBit::Unspecified,
                            inst: atom_to_fragment(Atom::Literal(LiteralValue::from((
                                span(19..20),
                                Script::Normal,
                                u36!(6)
                            ))))
                        }
                    ))
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
                    statements: vec![Statement::Instruction(TaggedProgramInstruction::single(
                        None,
                        UntaggedProgramInstruction {
                            span: span(14..15),
                            holdbit: HoldBit::Unspecified,
                            inst: InstructionFragment::from((
                                span(14..15),
                                Script::Normal,
                                u36!(4),
                            ))
                        }
                    ))]
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

fn parse_arithmetic_expression(input: &str) -> ArithmeticExpression {
    let mut comma_expression = parse_comma_expression(input);
    if let Some(CommaDelimitedInstruction {
        leading_commas: _,
        instruction:
            UntaggedProgramInstruction {
                span: _,
                holdbit: _,
                inst: InstructionFragment::Arithmetic(expr),
            },
        trailing_commas: _,
    }) = comma_expression.pop()
    {
        if comma_expression.is_empty() {
            expr
        } else {
            panic!("too many fragments: {comma_expression:?}");
        }
    } else {
        panic!("expected one fragment, not zero");
    }
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
        parse_single_instruction_fragment("AUX"),
        InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::Literal(
            LiteralValue::from((span(0..3), Script::Normal, expected_instruction.bits(),))
        ))),
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
        parse_tagged_instruction("²¹IOS₅₂ 30106").evaluate(
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
        parse_successfully_with("∨", operator(Script::Normal), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_logical_or_glyph_normal() {
    assert_eq!(
        parse_successfully_with("@or@", operator(Script::Normal), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_logical_or_glyph_subscript() {
    assert_eq!(
        parse_successfully_with("@sub_or@", operator(Script::Sub), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_logical_or_glyph_superscript() {
    assert_eq!(
        parse_successfully_with("@sup_or@", operator(Script::Super), no_state_setup),
        Operator::LogicalOr
    );
}

#[test]
fn test_arithmetic_expression_head_only() {
    assert_eq!(
        parse_arithmetic_expression("6"),
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
        parse_arithmetic_expression("4 ∨ 2"),
        ArithmeticExpression::with_tail(head, tail),
    );
}

#[test]
fn test_parenthesised_expression() {
    assert_eq!(
        parse_arithmetic_expression("(1)"),
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
        parse_successfully_with("@comma@A02", macro_argument(), no_state_setup),
        MacroArgument {
            name: SymbolName::from("A02".to_string()),
            span: span(0..10),
            preceding_terminator: ',',
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
    let expected =
        MacroDefinition {
            name: SymbolName::from("JUST".to_string()),
            args: MacroArguments::OneOrMore(vec![MacroArgument {
                name: SymbolName::from("A".to_string()),
                span: span(14..16),
                preceding_terminator: '|',
            }]),
            body: vec![Statement::Instruction(TaggedProgramInstruction::single(
                None,
                UntaggedProgramInstruction {
                    span: span(17..18),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::Symbol(span(17..18), Script::Normal, SymbolOrHere::from("A")),
                    )),
                },
            ))],
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
            body: vec![Statement::Instruction(TaggedProgramInstruction::single(
                None,
                UntaggedProgramInstruction {
                    span: span(17..18),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::Symbol(span(17..18), Script::Normal, SymbolOrHere::from("A")),
                    )),
                },
            ))],
            span: span(0..28),
        }],
        punch: None,
    };
    assert_eq!(got, expected);
}

#[test]
fn test_asterisk_for_deferred_addressing() {
    // This instruction is taken from the code for Leonard
    // Kleinrock's network simulation, at address 200762.
    assert_eq!(
        parse_multiple_instruction_fragments("@sup_1@DPX@sub_0@ *B"),
        vec![
            InstructionFragment::Config(ConfigValue::Literal(span(0..7), u36!(0o1))),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::Literal(
                LiteralValue::from((span(7..10), Script::Normal, u36!(0o1600000000)))
            ))),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::Literal(
                LiteralValue::from((span(10..17), Script::Sub, Unsigned36Bit::ZERO))
            ),)),
            InstructionFragment::DeferredAddressing,
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::Symbol(
                span(19..20),
                Script::Normal,
                SymbolOrHere::from("B"),
            ),)),
        ]
    );
}

#[test]
fn test_double_pipe_config_symbolic() {
    // The input "‖4" sets the configuration syllable of the
    // instruction word to 4.  This is described in section 6-2.1 of
    // the Users Handbook.  Spaces are not allowed in the
    // configuration syllable, so "‖X Y" should be parsed as a
    // configuration syllable X followed by the symbolic value Y
    // (which would therefore go into the address portion of the
    // instruction word).
    let input_xy = "‖X Y";
    let got = parse_tagged_instruction(input_xy);
    let expected = TaggedProgramInstruction {
        tag: None,
        instructions: vec![
            CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(0..4),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::Config(ConfigValue::Symbol(
                        span(3..4),
                        SymbolOrHere::from("X"),
                    )),
                },
                trailing_commas: None,
            },
            CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(5..6),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::Symbol(span(5..6), Script::Normal, SymbolOrHere::from("Y")),
                    )),
                },
                trailing_commas: None,
            },
        ],
    };
    assert_eq!(got, expected);
}

#[test]
fn test_double_pipe_config_literal() {
    let input = "‖10"; // 10 octal = 8 decimal.
    let got = parse_tagged_instruction(input);
    let expected = TaggedProgramInstruction::single(
        None,
        UntaggedProgramInstruction {
            span: span(0..5),
            holdbit: HoldBit::Unspecified,
            inst: InstructionFragment::Config(ConfigValue::Literal(span(3..5), u36!(8))),
        },
    );
    assert_eq!(got, expected);
}

#[test]
fn test_superscript_configuration_literal() {
    let input = "@sup_1@AUX";
    let config = InstructionFragment::Config(ConfigValue::Literal(span(0..7), u36!(0o1)));
    let aux = InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::Literal(
        LiteralValue::from((
            span(7..10),
            Script::Normal,
            // AUX is opcode 0o10.
            u36!(0o10 << 24),
        )),
    )));

    assert_eq!(
        parse_comma_expression(input),
        vec![
            CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(0..7),
                    holdbit: HoldBit::Unspecified,
                    inst: config,
                },
                trailing_commas: None,
            },
            CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(7..10),
                    holdbit: HoldBit::Unspecified,
                    inst: aux,
                },
                trailing_commas: None,
            },
        ]
    );
}

#[test]
fn test_superscript_configuration_hash() {
    assert_eq!(
        parse_single_instruction_fragment("@sup_hash@"),
        InstructionFragment::Config(ConfigValue::Symbol(span(0..10), SymbolOrHere::Here))
    );
}

#[test]
fn test_pipe_construct() {
    let input = "@sub_alpha@@sub_pipe@@sub_beta@DISPTBL";
    let got = parse_single_instruction_fragment(input);
    let expected = InstructionFragment::PipeConstruct {
        index: SymbolOrLiteral::Symbol(Script::Sub, SymbolName::from("α"), span(0..11)),
        rc_word_span: span(31..38),
        rc_word_value: Box::new((
            InstructionFragment::Arithmetic(ArithmeticExpression::from(SymbolOrLiteral::Symbol(
                Script::Normal,
                SymbolName::from("DISPTBL"),
                span(31..38),
            ))),
            Atom::Symbol(
                span(21..31),
                Script::Sub,
                SymbolOrHere::Named(SymbolName::from("β")),
            ),
        )),
    };
    assert_eq!(got, expected, "incorrect parse of input {input}");
}

#[test]
fn test_comments_without_newline_manuscript() {
    assert_eq!(
        parse_successfully_with("** NO NEWLINE AFTER COMMENT", source_file(), no_state_setup),
        SourceFile {
            blocks: BTreeMap::new(),
            macros: vec![],
            punch: None,
        }
    )
}

#[test]
fn test_commas_instruction() {
    let input = "200,200,,200,200";
    let got = parse_tagged_instruction(input);
    let expected = TaggedProgramInstruction::multiple(
        None,
        vec![
            CommaDelimitedInstruction {
                leading_commas: None,
                instruction: UntaggedProgramInstruction {
                    span: span(0..3),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::from((
                        span(0..3),
                        Script::Normal,
                        Unsigned36Bit::from(0o200u8),
                    )),
                },
                trailing_commas: Some(Commas::One(span(3..4))),
            },
            CommaDelimitedInstruction {
                leading_commas: Some(Commas::One(span(3..4))),
                instruction: UntaggedProgramInstruction {
                    span: span(4..7),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::from((
                        span(4..7),
                        Script::Normal,
                        Unsigned36Bit::from(0o200u8),
                    )),
                },
                trailing_commas: Some(Commas::Two(span(7..9))),
            },
            CommaDelimitedInstruction {
                leading_commas: Some(Commas::Two(span(7..9))),
                instruction: UntaggedProgramInstruction {
                    span: span(9..12),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::from((
                        span(9..12),
                        Script::Normal,
                        Unsigned36Bit::from(0o200u8),
                    )),
                },
                trailing_commas: Some(Commas::One(span(12..13))),
            },
            CommaDelimitedInstruction {
                leading_commas: Some(Commas::One(span(12..13))),
                instruction: UntaggedProgramInstruction {
                    span: span(13..16),
                    holdbit: HoldBit::Unspecified,
                    inst: InstructionFragment::from((
                        span(13..16),
                        Script::Normal,
                        Unsigned36Bit::from(0o200u8),
                    )),
                },
                trailing_commas: None,
            },
        ],
    );
    assert_eq!(got, expected);
}
