use base::prelude::*;
use base::u36;
use std::fmt::Debug;
#[cfg(test)]
use std::ops::Range;

use chumsky::Parser;

use super::super::{
    ast::{
        Atom, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock, ManuscriptMetaCommand,
        Origin, SourceFile, TaggedProgramInstruction,
    },
    eval::{make_empty_rc_block_for_test, Evaluate, EvaluationContext, HereValue},
    lexer::Token,
    parser::symex::{parse_multi_syllable_symex, parse_symex},
    state::NumeralMode,
    symbol::SymbolName,
    symtab::{IndexRegisterAssigner, MemoryMap, SymbolTable},
};
use super::*;

#[cfg(test)]
use super::Span;

type ParseErrors<'a> = Vec<Rich<'a, Tok>>;

#[cfg(test)]
fn notags() -> Vec<Tag> {
    Vec::new()
}

#[cfg(test)]
pub(crate) fn parse_with<'a, O, P, F>(
    input: &'a str,
    parser: P,
    state_setup: F,
) -> Result<O, ParseErrors<'a>>
where
    P: Parser<'a, super::Mi, O, ExtraWithoutContext<'a>>,
    O: Debug,
    F: FnMut(&mut State),
{
    let (output, errors) = tokenize_and_parse_with(input, state_setup, parser);
    if errors.is_empty() {
        Ok(output.expect("a successful parse should return an output"))
    } else {
        Err(errors)
    }
}

#[cfg(test)]
pub(crate) fn parse_successfully_with<'a, O, P, F>(input: &'a str, parser: P, state_setup: F) -> O
where
    P: Parser<'a, super::Mi, O, ExtraWithoutContext<'a>>,
    O: Debug,
    F: FnMut(&mut State),
{
    dbg!(&input);

    match parse_with(input, parser, state_setup) {
        Ok(out) => out,
        Err(errors) => {
            panic!(
                "{} unexpected parse errors for input '{input}': {:?}",
                errors.len(),
                &errors.as_slice()
            );
        }
    }
}

#[cfg(test)]
fn no_state_setup(_: &mut State) {}

#[cfg(test)]
fn set_decimal_mode(state: &mut State) {
    state.numeral_mode.set_numeral_mode(NumeralMode::Decimal);
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
}

#[test]
fn test_superscript_unary_plus_expression() {
    // A leading + isn't part of the literal.  That is, +36 is a valid
    // arithmetic expression, but not a literal.
    let input = "\u{207A}³⁶";
    dbg!(input.len());
    assert_eq!(
        // U+207A: superscript plus
        parse_superscript_arithmetic_expression(input),
        Ok(ArithmeticExpression::from(SignedAtom {
            span: span(0..8),
            negated: false,
            magnitude: Atom::from(LiteralValue::from((
                span(3..8),
                Script::Super,
                Unsigned36Bit::from(0o36_u32)
            )))
        }))
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
fn test_subscript_unary_plus() {
    assert_eq!(
        // This is actually not a valid literal (as they don't have a
        // leading sign), but it is a valid arithmetic expression.
        parse_subscript_arithmetic_expression("₊₁₃"),
        Ok(ArithmeticExpression::from(SignedAtom {
            span: span(0..9),
            negated: false,
            magnitude: Atom::from(LiteralValue::from((
                span(3..9),
                Script::Sub,
                Unsigned36Bit::from(0o13_u32)
            )))
        }))
    );
}

#[test]
fn test_subscript_literal_oct_decmode() {
    // Simulate a previous ☛☛DECIMAL, so that the trailing dot selects octal.
    assert_eq!(
        parse_successfully_with("₃₁@sub_dot@", literal(Script::Sub), set_decimal_mode),
        LiteralValue::from((span(0..15), Script::Sub, Unsigned36Bit::from(0o31_u32),))
    );
    assert_eq!(
        parse_successfully_with("₃₁․", literal(Script::Sub), set_decimal_mode),
        LiteralValue::from((span(0..9), Script::Sub, Unsigned36Bit::from(0o31_u32),))
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
    let parser = grammar().instruction_fragment;
    parse_successfully_with(input, parser, no_state_setup)
}

#[cfg(test)]
fn parse_multiple_instruction_fragments(input: &str) -> Vec<InstructionFragment> {
    let parse_result = parse_untagged_program_instruction(input);
    parse_result
        .fragments
        .into_iter()
        .map(|comma_delimited_insn| comma_delimited_insn.fragment)
        .collect()
}

#[test]
fn test_assemble_octal_superscript_literal() {
    let input = "⁺³⁶"; // 36, superscript
    assert_eq!(input.len(), 8);
    assert_eq!(
        parse_superscript_arithmetic_expression(input),
        Ok(ArithmeticExpression::from(SignedAtom {
            span: span(0..8),
            negated: false,
            magnitude: Atom::from(LiteralValue::from((
                span(3..8),
                Script::Super,
                Unsigned36Bit::from(0o36_u32)
            )))
        }))
    );
}

#[test]
fn test_assemble_octal_subscript_literal_nosign() {
    let input = "₁₃"; // without sign
    assert_eq!(
        parse_subscript_arithmetic_expression(input),
        Ok(ArithmeticExpression::from(SignedAtom {
            span: span(0..6),
            negated: false,
            magnitude: Atom::from(LiteralValue::from((
                span(0..6),
                Script::Sub,
                Unsigned36Bit::from(0o13_u32)
            )))
        }))
    );

    assert_eq!(
        parse_single_instruction_fragment(input),
        InstructionFragment::from((span(0..6), Script::Sub, Unsigned36Bit::from(0o13_u32)))
    );
}

#[test]
fn test_assemble_octal_subscript_literal_plussign() {
    let input = "₊₁₃"; // with optional + sign
    assert_eq!(input.len(), 9);

    let expression_expected = ArithmeticExpression::from(SignedAtom {
        span: span(0..9),
        negated: false,
        magnitude: Atom::from(LiteralValue::from((
            span(3..9),
            Script::Sub,
            Unsigned36Bit::from(0o13_u32),
        ))),
    });

    // Parse it as an arithmetic expression
    assert_eq!(
        parse_subscript_arithmetic_expression(input),
        Ok(expression_expected.clone())
    );

    // Verify that it parses identically as part of a larger syntactic
    // unit.
    assert_eq!(
        parse_single_instruction_fragment(input),
        InstructionFragment::from(expression_expected),
    );
}

#[test]
fn test_program_instruction_fragments() {
    assert_eq!(
        parse_single_instruction_fragment("₃₁"),
        InstructionFragment::from((span(0..6), Script::Sub, Unsigned36Bit::from(0o31_u32),)),
    );
    assert_eq!(
        parse_single_instruction_fragment("⁶³"),
        InstructionFragment::Config(ConfigValue {
            already_superscript: true,
            expr: ArithmeticExpression::from(Atom::from((
                span(0..5),
                Script::Super,
                Unsigned36Bit::from(0o63_u32)
            )))
        }),
    );
    assert_eq!(
        parse_single_instruction_fragment("6510"),
        InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from((
            span(0..4),
            Script::Normal,
            Unsigned36Bit::from(0o6510_u32)
        ))))
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
            InstructionFragment::Config(ConfigValue {
                already_superscript: true,
                expr: ArithmeticExpression::from(SignedAtom::from(Atom::from((
                    span(0..3),
                    Script::Super,
                    u36!(0o6)
                ))))
            }),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(SignedAtom::from(
                Atom::from((span(3..6), Script::Normal, Unsigned36Bit::from(0o673_u32)))
            ))),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(SignedAtom::from(
                Atom::from((span(6..12), Script::Sub, Unsigned36Bit::from(0o31_u32)))
            ))),
        ]
    );
}

#[test]
fn test_program_instruction_negative_config_value() {
    assert_eq!(
        parse_multiple_instruction_fragments("⁻⁶673₃₁"),
        vec![
            InstructionFragment::Config(ConfigValue {
                already_superscript: true,
                expr: ArithmeticExpression::from(SignedAtom {
                    span: span(0..6),
                    negated: true,
                    magnitude: Atom::from((span(3..6), Script::Super, u36!(0o6)))
                })
            }),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(SignedAtom::from(
                Atom::from((span(6..9), Script::Normal, Unsigned36Bit::from(0o673_u32)))
            ))),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(SignedAtom::from(
                Atom::from((span(9..15), Script::Sub, Unsigned36Bit::from(0o31_u32)))
            ))),
        ]
    );
}

#[test]
fn test_parse_multi_syllable_symex() {
    let zero_or_more_symexes = parse_symex(SymexSyllableRule::Multiple, Script::Normal)
        .repeated()
        .collect();
    struct Case(&'static str, &'static [&'static str]);

    const TEST_CASES: &[Case] = &[
        Case("Q", &["Q"]),
        Case("SOMENAME", &["SOMENAME"]),
        Case("SOME NAME", &["SOMENAME"]),
        // OK to use a reserved identifier if it is not the first
        // syllable in the symex.
        Case("TEST A", &["TESTA"]),
        // If there's no space after it, it's not reserved
        Case("ATEST", &["ATEST"]),
        // Otherwise, the reserved identifier is the whole of it.
        Case("B", &["B"]),
        // For reserved identifier, we don't join the first syllable
        // of the symex with one that follows (unlike for example the
        // "TEST A" case above).
        Case("B Z", &["B", "Z"]),
        // A symex can contain digits and can even start with one.
        Case("HOP2", &["HOP2"]),
        Case("HOP2IT", &["HOP2IT"]),
        Case("HOP 2", &["HOP2"]),
        Case("HOP 2@dot@", &["HOP2·"]),
        Case("HOP 2 IT", &["HOP2IT"]),
        Case("4REAL", &["4REAL"]),
        // Some lower case letters are supported
        Case("j2", &["j2"]),
        // Dot.  We don't use underscore because on the Lincoln Writer
        // this character does not advance the carriage.  IOW it
        // generates a combined symex.
        Case("@dot@x", &["\u{00B7}x"]),
        Case("q@dot@q", &["q\u{00B7}q"]),
        // Single quotes are allowed too
        Case("@dot@'X", &["\u{00B7}'X"]),
        Case("SCRATCH 'N' SNIFF", &["SCRATCH'N'SNIFF"]),
        Case(
            "SCRATCH @apostrophe@N@apostrophe@ SNIFF",
            &["SCRATCH'N'SNIFF"],
        ),
        Case("F '", &["F'"]),
    ];
    for Case(input, expected) in TEST_CASES {
        let got: Vec<SymbolName> =
            parse_successfully_with(input, zero_or_more_symexes.clone(), no_state_setup);
        let got_canonicals: Vec<String> =
            got.into_iter().map(|symbol| symbol.to_string()).collect();
        let expected_canonicals: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(got_canonicals, expected_canonicals);
    }
}

#[test]
fn test_parse_single_syllable_symex() {
    let zero_or_more_symexes = parse_symex(SymexSyllableRule::OneOnly, Script::Normal)
        .repeated()
        .collect();
    struct Case(&'static str, &'static [&'static str]);

    const TEST_CASES: &[Case] = &[
        Case("Q", &["Q"]),        // there's only one syllable anyway
        Case("A", &["A"]),        // there's only one syllable anyway
        Case("A A", &["A", "A"]), // special symexes are never joined anyway
        Case("Q Q", &["Q", "Q"]), // Use of OneOnly forces these syllables not to be joined.
    ];
    for Case(input, expected) in TEST_CASES {
        let got: Vec<SymbolName> =
            parse_successfully_with(input, zero_or_more_symexes.clone(), no_state_setup);
        let got_canonicals: Vec<String> =
            got.into_iter().map(|symbol| symbol.to_string()).collect();
        let expected_canonicals: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(got_canonicals, expected_canonicals);
    }
}

#[test]
fn test_empty_manuscript() {
    assert_eq!(
        parse_successfully_with("", source_file(), no_state_setup),
        SourceFile {
            blocks: Vec::new(),
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
            punch: None,
        }
    )
}

#[test]
fn test_blank_lines_manuscript() {
    assert_eq!(
        parse_successfully_with("\n\n", source_file(), no_state_setup),
        SourceFile {
            blocks: Default::default(),
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
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
            blocks: Default::default(),
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
            punch: None,
        }
    )
}

#[test]
fn test_manuscript_line_with_bare_literal() {
    assert_eq!(
        parse_successfully_with("1", manuscript_line(), no_state_setup),
        ManuscriptLine::StatementOnly(TaggedProgramInstruction::single(
            notags(),
            HoldBit::Unspecified,
            span(0..1),
            span(0..1),
            InstructionFragment::from((span(0..1), Script::Normal, Unsigned36Bit::from(1_u32),))
        ))
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
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        notags(),
                        HoldBit::Unspecified,
                        span(0..1),
                        span(0..1),
                        InstructionFragment::from((
                            span(0..1),
                            Script::Normal,
                            Unsigned36Bit::from(1_u32),
                        )),
                    )]
                }],
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
        }
    );
}

#[test]
fn test_terminated_manuscript_line_with_bare_literal() {
    let expected_line = ManuscriptLine::StatementOnly(TaggedProgramInstruction::single(
        notags(),
        HoldBit::Unspecified,
        span(0..1),
        span(0..1),
        InstructionFragment::from((span(0..1), Script::Normal, Unsigned36Bit::from(1_u32))),
    ));

    assert_eq!(
        parse_successfully_with("1", manuscript_line(), no_state_setup),
        expected_line
    );
    assert_eq!(
        parse_successfully_with("1\n", terminated_manuscript_line(), no_state_setup),
        Some((span(0..1), expected_line))
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
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![
                        TaggedProgramInstruction::single(
                            notags(),
                            HoldBit::Unspecified,
                            span(0..3),
                            span(0..3),
                            InstructionFragment::from((
                                span(0..3),
                                Script::Normal,
                                Unsigned36Bit::from(0o673_u32),
                            )),
                        ),
                        TaggedProgramInstruction::single(
                            notags(),
                            HoldBit::Unspecified,
                            span(25..27),
                            span(25..27),
                            InstructionFragment::from((
                                span(25..27),
                                Script::Normal,
                                Unsigned36Bit::from(0o71_u32),
                            )),
                        ),
                    ]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
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
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        notags(),
                        HoldBit::Unspecified,
                        span(0..10),
                        span(0..10),
                        // The output is an RC-reference to a location containing the value 1.
                        InstructionFragment::from(ArithmeticExpression::from(Atom::RcRef(
                            span(0..10),
                            RegistersContaining::from_words(OneOrMore::new(
                                RegisterContaining::from(TaggedProgramInstruction {
                                    span: span(1..2),
                                    tags: notags(),
                                    instruction: UntaggedProgramInstruction::from(OneOrMore::new(
                                        CommaDelimitedFragment {
                                            leading_commas: None,
                                            holdbit: HoldBit::Unspecified,
                                            span: span(1..2),
                                            fragment: InstructionFragment::Arithmetic(
                                                ArithmeticExpression::from(Atom::from(
                                                    LiteralValue::from((
                                                        span(1..2),
                                                        Script::Normal,
                                                        Unsigned36Bit::ONE
                                                    ))
                                                ))
                                            ),
                                            trailing_commas: None,
                                        }
                                    ))
                                })
                            )),
                        )))
                    )]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
            punch: None,
        }
    );
}

#[test]
fn test_symbol_name_one_syllable() {
    assert_eq!(
        parse_successfully_with(
            "START4",
            named_symbol(SymexSyllableRule::Multiple, Script::Normal),
            no_state_setup
        ),
        SymbolName::from("START4")
    );
}

#[test]
fn test_symbol_name_two_syllables() {
    assert_eq!(
        parse_successfully_with(
            "TWO WORDS",
            named_symbol(SymexSyllableRule::Multiple, Script::Normal),
            no_state_setup
        ),
        SymbolName::from("TWOWORDS")
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
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        vec![Tag {
                            name: SymbolName {
                                canonical: "START4".to_string(),
                            },
                            span: span(0..6),
                        }],
                        HoldBit::Unspecified,
                        span(0..13),
                        span(10..13),
                        InstructionFragment::from((
                            span(10..13),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        )),
                    )]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
            punch: None
        }
    );
}

#[test]
fn test_manuscript_with_multiple_tags() {
    assert_eq!(
        parse_successfully_with("START4 -> START5 -> 205\n", source_file(), no_state_setup),
        SourceFile {
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        vec![
                            Tag {
                                name: SymbolName {
                                    canonical: "START4".to_string(),
                                },
                                span: span(0..6),
                            },
                            Tag {
                                name: SymbolName {
                                    canonical: "START5".to_string(),
                                },
                                span: span(10..16),
                            },
                        ],
                        HoldBit::Unspecified,
                        span(0..23),
                        span(20..23),
                        InstructionFragment::from((
                            span(20..23),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        )),
                    )]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
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
                origin: Some(Origin::Literal(span(0..5), Address::new(u18!(0o100)))),
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        notags(),
                        HoldBit::Unspecified,
                        span(6..9),
                        span(6..9),
                        InstructionFragment::from((
                            span(6..9),
                            Script::Normal,
                            Unsigned36Bit::from(0o202_u32),
                        ))
                    )]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
        }
    );
}

#[cfg(test)]
fn parse_tagged_instruction(input: &str) -> TaggedProgramInstruction {
    parse_successfully_with(input, tagged_instruction(), no_state_setup)
}

#[cfg(test)]
fn parse_untagged_program_instruction(input: &str) -> UntaggedProgramInstruction {
    let stmt = parse_successfully_with(input, tagged_instruction(), no_state_setup);
    stmt.instruction
}

#[test]
fn test_arrow() {
    assert_eq!(
        parse_tagged_instruction("FOO->0"),
        TaggedProgramInstruction {
            span: span(0..6),
            tags: vec![Tag {
                name: SymbolName {
                    canonical: "FOO".to_string()
                },
                span: span(0..3),
            }],
            instruction: UntaggedProgramInstruction::from(OneOrMore::new(CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(5..6),
                fragment: InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                    LiteralValue::from((span(5..6), Script::Normal, Unsigned36Bit::ZERO))
                ))),
                trailing_commas: None
            }))
        }
    );
    assert_eq!(
        parse_tagged_instruction("BAR  -> 1"),
        TaggedProgramInstruction {
            span: span(0..9),
            tags: vec![Tag {
                name: SymbolName {
                    canonical: "BAR".to_string(),
                },
                span: span(0..3),
            }],
            instruction: UntaggedProgramInstruction::from(OneOrMore::new(CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(8..9),
                fragment: InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                    LiteralValue::from((span(8..9), Script::Normal, u36!(1),))
                ))),
                trailing_commas: None
            }))
        }
    );
}

#[test]
fn test_multi_syllable_tag() {
    assert_eq!(
        parse_tagged_instruction("CODE HERE->205 "),
        TaggedProgramInstruction::single(
            vec![Tag {
                name: SymbolName {
                    canonical: "CODEHERE".to_string(),
                },
                span: span(0..9),
            }],
            HoldBit::Unspecified,
            span(0..14),
            span(11..14),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                LiteralValue::from((span(11..14), Script::Normal, u36!(0o205)))
            )))
        )
    );
}

#[test]
fn test_infix_minus_interpreted_as_subtraction() {
    let head = SignedAtom::from(Atom::from(LiteralValue::from((
        span(0..1),
        Script::Normal,
        u36!(4),
    ))));
    for (input, rhs_span) in [("4 - 2", 4..5), ("4-2", 2..3), ("4 -2", 3..4)] {
        let tail = vec![(
            Operator::Subtract,
            SignedAtom::from(Atom::from(LiteralValue::from((
                span(rhs_span),
                Script::Normal,
                u36!(2),
            )))),
        )];
        assert_eq!(
            parse_normal_arithmetic_expression(input),
            Ok(ArithmeticExpression::with_tail(head.clone(), tail)),
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
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        vec![Tag {
                            name: SymbolName {
                                canonical: "CODEHERE".to_string(),
                            },
                            span: span(0..9),
                        }],
                        HoldBit::Unspecified,
                        span(0..14),
                        span(11..14),
                        InstructionFragment::from((
                            span(11..14),
                            Script::Normal,
                            Unsigned36Bit::from(0o205_u32),
                        ))
                    )]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
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
        ManuscriptLine::StatementOnly(TaggedProgramInstruction::single(
            vec![Tag {
                name: SymbolName {
                    canonical: "HERE".to_string(),
                },
                span: span(0..4),
            }],
            HoldBit::Unspecified,
            span(0..10),
            span(7..10),
            atom_to_fragment(Atom::from((span(7..10), Script::Normal, u36!(0o207)))),
        ))
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
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        vec![Tag {
                            name: SymbolName {
                                canonical: "HERE".to_string(),
                            },
                            span: span(0..4),
                        }],
                        HoldBit::Unspecified,
                        span(0..10),
                        span(7..10),
                        InstructionFragment::from((
                            span(7..10),
                            Script::Normal,
                            Unsigned36Bit::from(0o207_u32),
                        )),
                    )]
                }]
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
        }
    );
}

#[cfg(test)]
fn assignment_of_literal(name: &str, assignment_span: Span, literal: LiteralValue) -> Equality {
    Equality {
        span: assignment_span,
        name: SymbolName::from(name),
        value: EqualityValue::from((
            literal.span(),
            UntaggedProgramInstruction::from(OneOrMore::new(CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: literal.span(),
                fragment: atom_to_fragment(Atom::from(literal)),
                trailing_commas: None,
            })),
        )),
    }
}

#[test]
fn test_assignment_literal() {
    const INPUTS: &[(&str, usize)] = &[
        ("FOO=2", 4),
        ("FOO =2", 5),
        ("F O O = 2", 8), // spaces are also allowed inside symexes.
    ];
    let assignment = grammar().assignment;
    for (input, begin) in INPUTS {
        dbg!(&input);
        dbg!(&begin);
        assert_eq!(
            parse_successfully_with(input, assignment.clone(), no_state_setup),
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
        ("ZOO=\u{00B2}", 4, 6),
        ("ZOO =\u{00B2}", 5, 7),
        ("Z O O = \u{00B2}", 8, 10), // spaces are also allowed inside symexes.
    ];
    for (input, val_begin, val_end) in INPUTS {
        dbg!(input);
        let val_span = span(*val_begin..*val_end);
        let assignment = grammar().assignment;
        assert_eq!(
            parse_successfully_with(input, assignment, no_state_setup),
            Equality {
                span: span(0..*val_end),
                name: SymbolName::from("ZOO"),
                value: EqualityValue::from((
                    val_span,
                    UntaggedProgramInstruction::from(OneOrMore::new(CommaDelimitedFragment {
                        leading_commas: None,
                        holdbit: HoldBit::Unspecified,
                        span: span(*val_begin..*val_end),
                        fragment: InstructionFragment::Config(ConfigValue {
                            already_superscript: true,
                            expr: ArithmeticExpression::from(Atom::from((
                                span(*val_begin..*val_end),
                                Script::Super,
                                u36!(0o2)
                            )))
                        }),
                        trailing_commas: None
                    }))
                ))
            }
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
    let assignment = grammar().assignment;
    for (input, val_begin, val_end) in INPUTS {
        dbg!(&input);
        dbg!(&input.len());
        dbg!(input.char_indices().collect::<Vec<_>>());
        dbg!(&val_begin);
        dbg!(&val_end);
        assert_eq!(
            parse_successfully_with(input, assignment.clone(), no_state_setup),
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
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        Vec::new(),
                        HoldBit::Unspecified,
                        span(19..20),
                        span(19..20),
                        atom_to_fragment(Atom::from(LiteralValue::from((
                            span(19..20),
                            Script::Normal,
                            u36!(6)
                        ))))
                    )]
                }]
            }],
            global_equalities: vec![
                assignment_of_literal(
                    "FOO",
                    span(0..5),
                    LiteralValue::from((span(4..5), Script::Normal, u36!(2))),
                ),
                assignment_of_literal(
                    "BAR",
                    span(10..17),
                    LiteralValue::from((span(16..17), Script::Normal, u36!(1))),
                )
            ],
            macros: Default::default(),
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
            blocks: vec![ManuscriptBlock {
                origin: Some(Origin::Literal(span(9..14), Address::new(u18!(0o1000)))),
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        Vec::new(),
                        HoldBit::Unspecified,
                        span(14..15),
                        span(14..15),
                        InstructionFragment::from((span(14..15), Script::Normal, u36!(4),))
                    )]
                }]
            }],
            global_equalities: vec![assignment_of_literal(
                "FOO",
                span(0..8),
                LiteralValue::from((span(4..8), Script::Normal, u36!(0o1000))),
            )],
            macros: Default::default(),
        }
    );
}

#[test]
fn test_symbolic_origin() {
    const INPUT: &str = concat!("BEGIN|2\n",);
    let tree = parse_successfully_with(INPUT, source_file(), no_state_setup);
    assert_eq!(
        tree,
        SourceFile {
            punch: None,
            blocks: vec![ManuscriptBlock {
                // One of the key things to check here is that the pipe
                // symbol is included in the origin's span.  We do
                // this in order to include the pipe symbol in the
                // output listing.
                origin: Some(Origin::Symbolic(span(0..6), SymbolName::from("BEGIN"))),
                sequences: vec![InstructionSequence::Unscoped {
                    instructions: vec![TaggedProgramInstruction::single(
                        Vec::new(),
                        HoldBit::Unspecified,
                        span(6..7),
                        span(6..7),
                        InstructionFragment::from((span(6..7), Script::Normal, u36!(2),))
                    )]
                }]
            }],
            global_equalities: Default::default(),
            macros: Default::default(),
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

fn parse_normal_arithmetic_expression(input: &str) -> Result<ArithmeticExpression, ParseErrors> {
    let g = grammar();
    parse_with(
        input,
        g.normal_arithmetic_expression_allowing_spaces,
        no_state_setup,
    )
}

fn parse_superscript_arithmetic_expression(
    input: &str,
) -> Result<ArithmeticExpression, ParseErrors> {
    let g = grammar();
    parse_with(
        input,
        g.superscript_arithmetic_expression_allowing_spaces,
        no_state_setup,
    )
}

fn parse_subscript_arithmetic_expression(input: &str) -> Result<ArithmeticExpression, ParseErrors> {
    let g = grammar();
    parse_with(
        input,
        g.subscript_arithmetic_expression_allowing_spaces,
        no_state_setup,
    )
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
        InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
            LiteralValue::from((span(0..3), Script::Normal, expected_instruction.bits(),))
        ))),
    );
}

#[test]
fn test_multi_syllable_symex() {
    assert_eq!(
        parse_successfully_with(
            "FOO",
            parse_multi_syllable_symex(SymexSyllableRule::Multiple, Script::Normal),
            no_state_setup
        ),
        "FOO"
    );
    assert_eq!(
        parse_successfully_with(
            "FOO BAR",
            parse_multi_syllable_symex(SymexSyllableRule::Multiple, Script::Normal),
            no_state_setup
        ),
        "FOOBAR"
    );
    assert_eq!(
        parse_successfully_with(
            "FOO  BAR",
            parse_multi_syllable_symex(SymexSyllableRule::Multiple, Script::Normal),
            no_state_setup
        ),
        "FOOBAR"
    );
}

#[test]
fn program_instruction_with_opcode() {
    let mut nosyms = SymbolTable::default();
    let input = "²¹IOS₅₂ 30106";
    let mut memory_map = MemoryMap::new([(span(0..input.len()), None, u18!(1))]);
    let mut index_register_assigner = IndexRegisterAssigner::default();
    let mut rc_block =
        make_empty_rc_block_for_test(Address::from(Unsigned18Bit::from(0o20_000u16)));
    let mut ctx = EvaluationContext {
        symtab: &mut nosyms,
        memory_map: &mut memory_map,
        here: HereValue::Address(Address::ZERO),
        index_register_assigner: &mut index_register_assigner,
        rc_updater: &mut rc_block,
        lookup_operation: Default::default(),
    };
    assert_eq!(
        parse_tagged_instruction(input).evaluate(&mut ctx),
        Ok(u36!(0o210452_030106))
    );
    assert!(
        index_register_assigner.is_empty(),
        "No index register should have been default-assigned"
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
            parse_multi_syllable_symex(SymexSyllableRule::Multiple, Script::Normal),
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
            parse_multi_syllable_symex(SymexSyllableRule::Multiple, Script::Normal),
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
        parse_successfully_with(
            "[hello] FOO",
            parse_symex(SymexSyllableRule::Multiple, Script::Normal),
            no_state_setup
        ),
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
        parse_normal_arithmetic_expression("6"),
        Ok(ArithmeticExpression::from(Atom::from(LiteralValue::from(
            (span(0..1), Script::Normal, u36!(6))
        ))))
    );
}

#[test]
fn test_arithmetic_expression_two_atoms() {
    let head = SignedAtom::from(Atom::from(LiteralValue::from((
        span(0..1),
        Script::Normal,
        u36!(4),
    ))));
    let tail = vec![(
        Operator::LogicalOr,
        SignedAtom::from(Atom::from(LiteralValue::from((
            span(6..7),
            Script::Normal,
            u36!(2),
        )))),
    )];
    assert_eq!(
        parse_normal_arithmetic_expression("4 ∨ 2"),
        Ok(ArithmeticExpression::with_tail(head, tail)),
    );
}

#[test]
fn test_parenthesised_expression() {
    assert_eq!(
        parse_normal_arithmetic_expression("(1)"),
        Ok(ArithmeticExpression::from(Atom::Parens(
            span(0..3),
            Script::Normal,
            Box::new(ArithmeticExpression::from(Atom::from(LiteralValue::from(
                (span(1..2), Script::Normal, u36!(1))
            ))))
        )))
    );
}

#[test]
fn test_macro_arg() {
    assert_eq!(
        parse_successfully_with(
            "@hand@A01",
            macro_definition_dummy_parameter(),
            no_state_setup
        ),
        MacroParameter {
            name: SymbolName::from("A01".to_string()),
            span: span(0..9),
            preceding_terminator: Token::Hand(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with(
            "@comma@A02",
            macro_definition_dummy_parameter(),
            no_state_setup
        ),
        MacroParameter {
            name: SymbolName::from("A02".to_string()),
            span: span(0..10),
            preceding_terminator: Token::Comma(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("=A03", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A03".to_string()),
            span: span(0..4),
            preceding_terminator: Token::Equals(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with(
            "@arr@A04",
            macro_definition_dummy_parameter(),
            no_state_setup
        ),
        MacroParameter {
            name: SymbolName::from("A04".to_string()),
            span: span(0..8),
            preceding_terminator: Token::Arrow(Script::Normal),
        }
    );

    assert_eq!(
        // Alternative form for convenience (and consistency with
        // what we allow for tags).
        parse_successfully_with("->A04", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A04".to_string()),
            span: span(0..5),
            preceding_terminator: Token::Arrow(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("|A05", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A05".to_string()),
            span: span(0..4),
            preceding_terminator: Token::Pipe(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("⊃A06", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A06".to_string()),
            span: span(0..6),
            preceding_terminator: Token::ProperSuperset(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("≡A07", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A07".to_string()),
            span: span(0..6),
            preceding_terminator: Token::IdenticalTo(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with(
            "@hamb@A07",
            macro_definition_dummy_parameter(),
            no_state_setup
        ),
        MacroParameter {
            name: SymbolName::from("A07".to_string()),
            span: span(0..9),
            preceding_terminator: Token::IdenticalTo(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("~A08", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A08".to_string()),
            span: span(0..4),
            preceding_terminator: Token::Tilde(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("<A09", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A09".to_string()),
            span: span(0..4),
            preceding_terminator: Token::LessThan(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with(">A10", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A10".to_string()),
            span: span(0..4),
            preceding_terminator: Token::GreaterThan(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("∩A11", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A11".to_string()),
            span: span(0..6),
            preceding_terminator: Token::Intersection(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("∪A12", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A12".to_string()),
            span: span(0..6),
            preceding_terminator: Token::Union(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("/A13", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A13".to_string()),
            span: span(0..4),
            preceding_terminator: Token::Solidus(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("×A14", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A14".to_string()),
            span: span(0..5),
            preceding_terminator: Token::Times(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("∨A15", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A15".to_string()),
            span: span(0..6),
            preceding_terminator: Token::LogicalOr(Script::Normal),
        }
    );

    assert_eq!(
        parse_successfully_with("∧A16", macro_definition_dummy_parameter(), no_state_setup),
        MacroParameter {
            name: SymbolName::from("A16".to_string()),
            span: span(0..6),
            preceding_terminator: Token::LogicalAnd(Script::Normal),
        }
    );
}

#[test]
fn test_macro_args() {
    assert_eq!(
        parse_successfully_with(
            "=X@hand@YZ@arr@P",
            macro_definition_dummy_parameters(),
            no_state_setup
        ),
        MacroDummyParameters::OneOrMore(vec![
            MacroParameter {
                name: SymbolName::from("X".to_string()),
                span: span(0..2),
                preceding_terminator: Token::Equals(Script::Normal),
            },
            MacroParameter {
                name: SymbolName::from("YZ".to_string()),
                span: span(2..10),
                preceding_terminator: Token::Hand(Script::Normal),
            },
            MacroParameter {
                name: SymbolName::from("P".to_string()),
                span: span(10..16),
                preceding_terminator: Token::Arrow(Script::Normal),
            },
        ])
    );
}

#[test]
fn test_asterisk_for_deferred_addressing() {
    // This instruction is taken from the code for Leonard
    // Kleinrock's network simulation, at address 200762.
    assert_eq!(
        parse_multiple_instruction_fragments("@sup_1@DPX@sub_0@ *B"),
        vec![
            InstructionFragment::Config(ConfigValue {
                already_superscript: true,
                expr: ArithmeticExpression::from(Atom::from(LiteralValue::from((
                    span(0..7),
                    Script::Super,
                    u36!(0o1)
                ))))
            }),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                LiteralValue::from((span(7..10), Script::Normal, u36!(0o1600000000)))
            ))),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                LiteralValue::from((span(10..17), Script::Sub, Unsigned36Bit::ZERO))
            ),)),
            InstructionFragment::DeferredAddressing(span(18..19)),
            InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from((
                span(19..20),
                Script::Normal,
                SymbolName::from("B"),
            ))),)
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
        tags: notags(),
        span: span(0..6),
        instruction: UntaggedProgramInstruction::from(OneOrMore::with_tail(
            CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(0..4),
                fragment: InstructionFragment::Config(ConfigValue {
                    already_superscript: false,
                    expr: ArithmeticExpression::from(Atom::from((
                        span(3..4),
                        Script::Normal,
                        SymbolName::from("X"),
                    ))),
                }),
                trailing_commas: None,
            },
            vec![CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(5..6),
                fragment: InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                    (span(5..6), Script::Normal, SymbolName::from("Y")),
                ))),
                trailing_commas: None,
            }],
        )),
    };
    assert_eq!(got, expected);
}

#[test]
fn test_double_pipe_config_expression() {
    // Asd described in section 6-2.1 of the Users Handbook, "‖Q Y"
    // should be parsed as a configuration syllable Q followed by the
    // symbolic value Y (which would therefore go into the address
    // portion of the instruction word).  Spaces are not allowed in
    // the configuration syllable, but the syllable can contain
    // expressions.  See for example the use of unary minus in Leonard
    // Kleinrock's network simulator (e.g. the body of the TAKE macro
    // on page 14 of the PDF).
    let input_qy = "‖-(Q×2) Y";
    assert_eq!(input_qy.len(), 12);
    let got = parse_tagged_instruction(input_qy);
    let expected = TaggedProgramInstruction {
        tags: notags(),
        span: span(0..12),
        instruction: UntaggedProgramInstruction::from(OneOrMore::with_tail(
            CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(0..10),
                fragment: InstructionFragment::Config(ConfigValue {
                    already_superscript: false,
                    expr: ArithmeticExpression {
                        first: SignedAtom {
                            span: span(3..10),
                            negated: true,
                            magnitude: Atom::Parens(
                                span(4..10),
                                Script::Normal,
                                Box::new(ArithmeticExpression {
                                    first: SignedAtom {
                                        span: span(5..6),
                                        negated: false,
                                        magnitude: Atom::from((
                                            span(5..6),
                                            Script::Normal,
                                            SymbolName::from("Q"),
                                        )),
                                    },
                                    tail: vec![(
                                        Operator::Multiply,
                                        SignedAtom {
                                            span: span(8..9),
                                            negated: false,
                                            magnitude: Atom::from((
                                                span(8..9),
                                                Script::Normal,
                                                u36!(2),
                                            )),
                                        },
                                    )],
                                }),
                            ),
                        },
                        tail: Vec::new(),
                    },
                }),
                trailing_commas: None,
            },
            vec![CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(11..12),
                fragment: InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
                    (span(11..12), Script::Normal, SymbolName::from("Y")),
                ))),
                trailing_commas: None,
            }],
        )),
    };
    assert_eq!(got, expected);
}

#[test]
fn test_double_pipe_config_expression_disallows_spaces() {
    // Spaces are not allowed in config expressions.  First we verify
    // that an expression without spaces is valid:
    let input_qy_unspaced = "‖-(Q×2) Y";
    assert!(dbg!(parse_with(
        input_qy_unspaced,
        tagged_instruction(),
        no_state_setup
    ))
    .is_ok());

    // Now we verify that a similae expression with spaces is
    // rejected:
    let input_qy_spaced = "‖-(Q × 2) Y";
    assert_eq!(input_qy_spaced.len(), 14);
    let result = parse_with(input_qy_spaced, tagged_instruction(), no_state_setup);
    dbg!(&result);
    assert!(result.is_err());
}

#[test]
fn test_double_pipe_config_literal() {
    let input = "‖10"; // 10 octal = 8 decimal.
    let got = parse_tagged_instruction(input);
    let expected = TaggedProgramInstruction::single(
        notags(),
        HoldBit::Unspecified,
        span(0..5),
        span(0..5),
        InstructionFragment::Config(ConfigValue {
            already_superscript: false,
            expr: ArithmeticExpression::from(Atom::from((span(3..5), Script::Normal, u36!(8)))),
        }),
    );
    assert_eq!(got, expected);
}

#[test]
fn test_superscript_configuration_literal() {
    let input = "@sup_1@AUX";
    let config = InstructionFragment::Config(ConfigValue {
        already_superscript: true,
        expr: ArithmeticExpression::from(Atom::from((span(0..7), Script::Super, u36!(0o1)))),
    });
    let aux = InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(
        LiteralValue::from((
            span(7..10),
            Script::Normal,
            // AUX is opcode 0o10.
            u36!(0o10 << 24),
        )),
    )));

    assert_eq!(
        parse_untagged_program_instruction(input),
        UntaggedProgramInstruction::from(OneOrMore::with_tail(
            CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(0..7),
                fragment: config,
                trailing_commas: None,
            },
            vec![CommaDelimitedFragment {
                leading_commas: None,
                holdbit: HoldBit::Unspecified,
                span: span(7..10),
                fragment: aux,
                trailing_commas: None,
            },]
        ))
    );
}

#[test]
fn test_superscript_configuration_hash() {
    // TODO: negated hash
    assert_eq!(
        parse_single_instruction_fragment("@sup_hash@"),
        InstructionFragment::Config(ConfigValue {
            already_superscript: true,
            expr: ArithmeticExpression::from(SignedAtom {
                negated: false,
                span: span(0..10),
                magnitude: Atom::SymbolOrLiteral(SymbolOrLiteral::Here(Script::Super, span(0..10))),
            })
        }),
    );
}

#[test]
fn test_pipe_construct() {
    let input = "@sub_alpha@@sub_pipe@@sub_beta@DISPTBL";
    let got = parse_single_instruction_fragment(input);
    let expected = InstructionFragment::PipeConstruct {
        index: SpannedSymbolOrLiteral {
            item: SymbolOrLiteral::Symbol(Script::Sub, SymbolName::from("α"), span(0..11)),
            span: span(0..11),
        },
        rc_word_span: span(21..38),
        rc_word_value: RegisterContaining::from(TaggedProgramInstruction {
            span: span(21..38),
            tags: notags(),
            instruction: UntaggedProgramInstruction::from(OneOrMore::with_tail(
                CommaDelimitedFragment {
                    leading_commas: None,
                    holdbit: HoldBit::Unspecified,
                    span: span(31..38),
                    fragment: InstructionFragment::Arithmetic(ArithmeticExpression {
                        first: SignedAtom {
                            negated: false,
                            span: span(31..38),
                            magnitude: Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(
                                Script::Normal,
                                SymbolName::from("DISPTBL".to_string()),
                                span(31..38),
                            )),
                        },
                        tail: Vec::new(),
                    }),
                    trailing_commas: None,
                },
                vec![CommaDelimitedFragment {
                    leading_commas: None,
                    holdbit: HoldBit::Unspecified,
                    span: span(21..31),
                    fragment: InstructionFragment::Arithmetic(ArithmeticExpression {
                        first: SignedAtom {
                            negated: false,
                            span: span(21..31),
                            magnitude: Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(
                                Script::Sub,
                                SymbolName::from("β"),
                                span(21..31),
                            )),
                        },
                        tail: Vec::new(),
                    }),
                    trailing_commas: None,
                }],
            )),
        }),
    };
    assert_eq!(got, expected, "incorrect parse of input {input}");
}

#[test]
fn test_comments_without_newline_manuscript() {
    assert_eq!(
        parse_successfully_with("** NO NEWLINE AFTER COMMENT", source_file(), no_state_setup),
        SourceFile {
            blocks: Default::default(),
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),
            punch: None,
        }
    )
}

#[test]
fn test_commas_instruction() {
    let input = "200,200,,200,200";
    let got = parse_tagged_instruction(input);
    let expected = TaggedProgramInstruction::multiple(
        notags(),
        span(0..16),
        CommaDelimitedFragment {
            leading_commas: None,
            holdbit: HoldBit::Unspecified,
            span: span(0..4),
            fragment: InstructionFragment::from((
                span(0..3),
                Script::Normal,
                Unsigned36Bit::from(0o200u8),
            )),
            trailing_commas: Some(Commas::One(span(3..4))),
        },
        vec![
            CommaDelimitedFragment {
                leading_commas: Some(Commas::One(span(3..4))),
                holdbit: HoldBit::Unspecified,
                span: span(3..9),
                fragment: InstructionFragment::from((
                    span(4..7),
                    Script::Normal,
                    Unsigned36Bit::from(0o200u8),
                )),
                trailing_commas: Some(Commas::Two(span(7..9))),
            },
            CommaDelimitedFragment {
                leading_commas: Some(Commas::Two(span(7..9))),
                holdbit: HoldBit::Unspecified,
                span: span(7..13),
                fragment: InstructionFragment::from((
                    span(9..12),
                    Script::Normal,
                    Unsigned36Bit::from(0o200u8),
                )),
                trailing_commas: Some(Commas::One(span(12..13))),
            },
            CommaDelimitedFragment {
                leading_commas: Some(Commas::One(span(12..13))),
                holdbit: HoldBit::Unspecified,
                span: span(12..16),
                fragment: InstructionFragment::from((
                    span(13..16),
                    Script::Normal,
                    Unsigned36Bit::from(0o200u8),
                )),
                trailing_commas: None,
            },
        ],
    );
    assert_eq!(got, expected);
}

#[cfg(test)]
mod comma_tests {
    use super::super::super::ast::{
        CommaDelimitedFragment, Commas, CommasOrInstruction, FragmentWithHold, HoldBit,
        InstructionFragment,
    };
    use super::super::super::span::{span, Span, Spanned};
    use super::super::instructions_with_comma_counts as parent_instructions_with_comma_counts;
    use std::fmt::Formatter;

    #[derive(Clone, Eq)]
    struct Briefly(CommaDelimitedFragment);

    impl From<(Option<Commas>, Span, InstructionFragment, Option<Commas>)> for Briefly {
        fn from(
            (leading_commas, span, upi, trailing_commas): (
                Option<Commas>,
                Span,
                InstructionFragment,
                Option<Commas>,
            ),
        ) -> Self {
            Self(CommaDelimitedFragment::new(
                leading_commas,
                FragmentWithHold {
                    span,
                    holdbit: HoldBit::Unspecified,
                    fragment: upi,
                },
                trailing_commas,
            ))
        }
    }

    fn brieflyh(v: Vec<(Option<Commas>, FragmentWithHold, Option<Commas>)>) -> Vec<Briefly> {
        v.into_iter()
            .map(|v| {
                let FragmentWithHold {
                    span,
                    holdbit: _,
                    fragment: frag,
                } = v.1;
                Briefly::from((v.0, span, frag, v.2))
            })
            .collect()
    }

    impl PartialEq<CommaDelimitedFragment> for Briefly {
        fn eq(&self, other: &CommaDelimitedFragment) -> bool {
            &self.0 == other
        }
    }

    impl PartialEq<Briefly> for Briefly {
        fn eq(&self, other: &Briefly) -> bool {
            self.0 == other.0
        }
    }

    fn instructions_with_comma_counts(input: Vec<CommasOrInstruction>) -> Vec<Briefly> {
        dbg!(&input);
        let output = parent_instructions_with_comma_counts(input.into_iter());
        output.into_iter().map(Briefly).collect()
    }

    impl std::fmt::Debug for Briefly {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let u = &self.0.fragment;
            let span = u.span();
            write!(
                f,
                "({0:?},UntaggedProgramInstruction{{span:{1:?},holdbit:{2:?},inst:{3:?}}}{4:?})",
                &self.0.leading_commas, &span, &self.0.holdbit, &u, &self.0.trailing_commas
            )
        }
    }

    fn null_insth(sp: Span) -> FragmentWithHold {
        FragmentWithHold {
            span: sp,
            holdbit: HoldBit::Unspecified,
            fragment: InstructionFragment::Null(sp),
        }
    }

    fn insth(sp: Span, n: u16) -> FragmentWithHold {
        use super::*;
        FragmentWithHold {
            span: sp,
            holdbit: HoldBit::Unspecified,
            fragment: InstructionFragment::from(ArithmeticExpression::from(Atom::from(
                LiteralValue::from((sp, Script::Normal, n.into())),
            ))),
        }
    }

    #[test]
    fn test_instructions_with_comma_counts_len_0_with_0_instructions() {
        assert_eq!(instructions_with_comma_counts(Vec::new()), brieflyh(vec![]))
    }

    #[test]
    fn test_instructions_with_comma_counts_len_1_with_1_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![CommasOrInstruction::I(insth(span(0..1), 1))]),
            brieflyh(vec![(None, insth(span(0..1), 1), None),])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_1_with_0_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![CommasOrInstruction::C(Some(Commas::One(span(
                0..1
            ))))]),
            brieflyh(vec![]),
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_0_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::C(Some(Commas::One(span(0..1)))),
                CommasOrInstruction::C(Some(Commas::Two(span(3..5)))),
            ]),
            brieflyh(vec![(
                Some(Commas::One(span(0..1))),
                null_insth(span(3..3)),
                Some(Commas::Two(span(3..5))),
            )])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_1_instruction_a() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::I(insth(span(0..1), 1)),
                CommasOrInstruction::C(Some(Commas::One(span(1..2)))),
            ]),
            brieflyh(vec![(
                None,
                insth(span(0..1), 1),
                Some(Commas::One(span(1..2))),
            )])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_1_instruction_b() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::C(Some(Commas::Two(span(0..2)))),
                CommasOrInstruction::I(insth(span(2..3), 3)),
            ]),
            brieflyh(vec![(
                Some(Commas::Two(span(0..2))),
                insth(span(2..3), 3),
                None,
            )])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_2_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![I(insth(span(0..1), 1)), I(insth(span(2..3), 2))]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), None),
                (None, insth(span(2..3), 2), None,),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_0_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                C(Some(Commas::Two(span(2..3)))),
                C(Some(Commas::Three(span(4..5)))),
            ]),
            brieflyh(vec![
                (
                    Some(Commas::One(span(0..1))),
                    null_insth(span(2..2)),
                    Some(Commas::Two(span(2..3))),
                ),
                (
                    Some(Commas::Two(span(2..3))),
                    null_insth(span(4..4)),
                    Some(Commas::Three(span(4..5))),
                ),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_1_instructions() {
        use CommasOrInstruction::*;
        // CCI cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                C(Some(Commas::Two(span(2..3)))),
                I(insth(span(3..4), 3))
            ]),
            brieflyh(vec![
                (
                    Some(Commas::One(span(0..1))),
                    null_insth(span(2..2)),
                    Some(Commas::Two(span(2..3))),
                ),
                (Some(Commas::Two(span(2..3))), insth(span(3..4), 3), None,),
            ])
        );

        // CIC cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                I(insth(span(1..2), 2)),
                C(Some(Commas::One(span(2..3)))),
            ]),
            brieflyh(vec![(
                Some(Commas::One(span(0..1))),
                insth(span(1..2), 2),
                Some(Commas::One(span(2..3))),
            )])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                I(insth(span(1..2), 2)),
                C(Some(Commas::Three(span(2..3))))
            ]),
            brieflyh(vec![(
                Some(Commas::One(span(0..1))),
                insth(span(1..2), 2),
                Some(Commas::Three(span(2..3))),
            )])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(None),
                I(insth(span(0..1), 2)),
                C(Some(Commas::Three(span(1..4))))
            ]),
            brieflyh(vec![(
                None,
                insth(span(0..1), 2),
                Some(Commas::Three(span(1..4)))
            )])
        );

        // ICC cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                C(Some(Commas::One(span(1..2)))), // 2..3 is a space
                C(Some(Commas::Two(span(3..4))))
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), Some(Commas::One(span(1..2)))),
                (
                    Some(Commas::One(span(1..2))),
                    null_insth(span(3..3)),
                    Some(Commas::Two(span(3..4)))
                )
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(
                // "1,, ,,,"
                vec![
                    I(insth(span(0..1), 1)),
                    C(Some(Commas::Two(span(1..3)))),
                    C(Some(Commas::Three(span(4..7))))
                ]
            ),
            brieflyh(vec![
                (None, insth(span(0..1), 1), Some(Commas::Two(span(1..3)))),
                (
                    Some(Commas::Two(span(1..3))),
                    null_insth(span(4..4)),
                    Some(Commas::Three(span(4..7)))
                ),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_2_instructions() {
        use CommasOrInstruction::*;
        // IIC cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                I(insth(span(2..3), 2)),
                C(Some(Commas::Two(span(3..5)))),
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), None),
                (None, insth(span(2..3), 2), Some(Commas::Two(span(3..5)))),
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                // span 1..2 is a space.
                I(insth(span(2..3), 2)),
                C(None)
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), None,),
                (None, insth(span(2..3), 2), None,)
            ])
        );

        // ICI cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                C(Some(Commas::Two(span(1..3)))),
                I(insth(span(3..4), 2)),
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), Some(Commas::Two(span(1..3)))),
                (Some(Commas::Two(span(1..3))), insth(span(3..4), 2), None)
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                C(Some(Commas::Three(span(1..4)))),
                I(insth(span(4..5), 2)),
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), Some(Commas::Three(span(1..4)))),
                (Some(Commas::Three(span(1..4))), insth(span(4..5), 2), None)
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                C(Some(Commas::One(span(1..2)))),
                I(insth(span(2..3), 2)),
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), Some(Commas::One(span(1..2)))),
                (Some(Commas::One(span(1..2))), insth(span(2..3), 2), None)
            ])
        );

        // CII cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::Two(span(0..2)))),
                I(insth(span(2..3), 1)),
                I(insth(span(4..5), 2)),
            ]),
            brieflyh(vec![
                (Some(Commas::Two(span(0..2))), insth(span(2..3), 1), None),
                (None, insth(span(4..5), 2), None)
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(None),
                I(insth(span(0..1), 1)),
                I(insth(span(1..3), 2)),
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), None),
                (None, insth(span(1..3), 2), None)
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_3_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(insth(span(0..1), 1)),
                I(insth(span(2..3), 2)),
                I(insth(span(4..5), 3)),
            ]),
            brieflyh(vec![
                (None, insth(span(0..1), 1), None),
                (None, insth(span(2..3), 2), None),
                (None, insth(span(4..5), 3), None),
            ])
        );
    }
}

#[test]
fn test_mnemonic_suz() {
    // SUZ is an alternate mnemonic for SMK (opcode 0o17) which also
    // sets the configuration syllable to 0o12.
    let input = "START -> SUZ 200013";
    dbg!(input.len());
    let insn = parse_tagged_instruction(input);
    assert_eq!(
        insn,
        TaggedProgramInstruction {
            span: span(0..19),
            tags: vec![Tag {
                name: SymbolName {
                    canonical: "START".to_string()
                },
                span: span(0..5),
            }],
            instruction: UntaggedProgramInstruction::from(OneOrMore::with_tail(
                CommaDelimitedFragment {
                    leading_commas: None,
                    holdbit: HoldBit::Unspecified,
                    span: span(9..12),
                    fragment: InstructionFragment::from((
                        span(9..12),
                        Script::Normal,
                        u36!(0o121_700_000_000)
                    )),
                    trailing_commas: None,
                },
                vec![CommaDelimitedFragment {
                    leading_commas: None,
                    holdbit: HoldBit::Unspecified,
                    span: span(13..19),
                    fragment: InstructionFragment::from((
                        span(13..19),
                        Script::Normal,
                        u36!(0o000_000_200_013)
                    )),
                    trailing_commas: None,
                },]
            ))
        }
    );
}

#[test]
fn test_opcode_to_literal() {
    assert_eq!(
        opcode_to_literal(
            u6!(0o17), // SKM
            u5!(0o12), // as if the mnemonic were SUZ
            span(0..3)
        ),
        LiteralValue::from((span(0..3), Script::Normal, u36!(0o121_700_000_000)))
    );
}

#[test]
fn test_bit_designator_example_from_handbook() {
    // The TX-2 Users Handbook states (in the table on page 6-7) that
    // bit designator 2.10 in normal script produces the bit patern
    // 0b0101010, or in octal 0o52.
    let span = span(0..4);
    assert_eq!(
        make_bit_designator_literal(Script::Normal, 2, 10, span),
        BitDesignatorValidation::Suspect(
            2_u8,
            10_u8,
            LiteralValue::from((span, Script::Normal, u36!(0o52)))
        )
    );
}

#[test]
fn test_make_bit_designator_literal() {
    for script in [Script::Sub] {
        const MASK: u64 = 0o77;
        fn makename(q: u8, b: u8) -> String {
            format!("{q}\u{00B7}{b}")
        }
        let mut seen = std::collections::HashMap::new();
        for q in 1..=4 {
            for bit in 1..=10 {
                if bit == 10 && q != 4 {
                    continue;
                }
                let what = makename(q, bit);
                let span: Span = span(0..what.len());
                match make_bit_designator_literal(script, q, bit, span) {
                    BitDesignatorValidation::Good(literal) => {
                        dbg!(&literal);
                        let n = literal.unshifted_value();
                        if (n & (!MASK)) != 0 {
                            panic!("bit designator {what} produced output {n:o} but that has bits set outside the allowed mask {MASK:o}");
                        }
                        if let Some((prevq, prevb)) = seen.insert(n, (q, bit)) {
                            panic!(
                                "two distinct bit designators both evaluate to {n}: {what} and {}",
                                makename(prevq, prevb)
                            );
                        }
                        assert_eq!(literal.span(), span);
                    }
                    do_not_like => {
                        panic!("unexpectedly suspect bit designator {what}: {do_not_like:?}");
                    }
                }
            }
        }
        assert_eq!(seen.len(), 4 * 9 + 1);
    }
}

mod macro_tests {
    use super::super::super::{
        ast::{Atom, HoldBit, InstructionFragment, SourceFile, TaggedProgramInstruction},
        lexer::Token,
        symbol::SymbolName,
    };
    use super::super::*;
    use super::{no_state_setup, notags, parse_successfully_with, span};

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
            params: MacroDummyParameters::Zero(Token::IdenticalTo(Script::Normal)),
            body: InstructionSequence::Scoped {
                local_symbols: SymbolTable::default(),
                instructions: Default::default(),
            },
            span: span(0..30),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn test_macro_definition_with_trivial_body() {
        let got = parse_successfully_with(
            concat!(
                "☛☛DEF JUST|Q\n",
                // This macro definition has a one-line body.
                "Q ** This is the only line in the body.\n",
                "☛☛EMD" // deliberately no terminating newline, see comment in macro_definition().
            ),
            macro_definition(),
            no_state_setup,
        );
        let expected = MacroDefinition {
            name: SymbolName::from("JUST".to_string()),
            params: MacroDummyParameters::OneOrMore(vec![MacroParameter {
                name: SymbolName::from("Q".to_string()),
                span: span(14..16),
                preceding_terminator: Token::Pipe(Script::Normal),
            }]),
            body: InstructionSequence::Scoped {
                local_symbols: SymbolTable::default(),
                instructions: vec![TaggedProgramInstruction::single(
                    notags(),
                    HoldBit::Unspecified,
                    span(17..18),
                    span(17..18),
                    InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(
                            Script::Normal,
                            SymbolName::from("Q"),
                            span(17..18),
                        )),
                    )),
                )],
            },
            span: span(0..66),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn test_macro_definition_as_entire_source_file() {
        let got =
            parse_successfully_with("☛☛DEF JUST|Q\nQ\n☛☛EMD\n", source_file(), no_state_setup);
        let expected = SourceFile {
            blocks: Default::default(),            // empty
            global_equalities: Default::default(), // no equalities
            macros: [(
                SymbolName::from("JUST".to_string()),
                MacroDefinition {
                    name: SymbolName {
                        canonical: "JUST".to_string(),
                    },
                    params: MacroDummyParameters::OneOrMore(vec![MacroParameter {
                        name: SymbolName {
                            canonical: "Q".to_string(),
                        },
                        span: span(14..16),
                        preceding_terminator: Token::Pipe(Script::Normal),
                    }]),
                    body: InstructionSequence::Scoped {
                        local_symbols: SymbolTable::default(),
                        instructions: vec![TaggedProgramInstruction::single(
                            notags(),
                            HoldBit::Unspecified,
                            span(17..18),
                            span(17..18),
                            InstructionFragment::Arithmetic(ArithmeticExpression::from(
                                Atom::from((span(17..18), Script::Normal, SymbolName::from("Q"))),
                            )),
                        )],
                    },
                    span: span(0..28),
                },
            )]
            .into(),
            punch: None,
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn test_macro_invocation() {
        let macro_definition_foo = MacroDefinition {
            name: SymbolName::from("FOO"),
            params: MacroDummyParameters::OneOrMore(vec![MacroParameter {
                name: SymbolName::from("A1"),
                span: span(10..12),
                preceding_terminator: Token::Tilde(Script::Normal),
            }]),
            body: vec![TaggedProgramInstruction {
                span: span(0..24),
                tags: notags(),
                instruction: UntaggedProgramInstruction::from(OneOrMore::new(
                    CommaDelimitedFragment {
                        leading_commas: None,
                        holdbit: HoldBit::Unspecified,
                        span: span(16..20),
                        fragment: InstructionFragment::Config(ConfigValue {
                            already_superscript: false,
                            expr: ArithmeticExpression::from(Atom::from((
                                span(4..5),
                                Script::Normal,
                                SymbolName::from("X"),
                            ))),
                        }),
                        trailing_commas: None,
                    },
                )),
            }]
            .into(),
            span: span(20..40),
        };
        let set_up_macro_definition = |state: &mut State| {
            state.define_macro(macro_definition_foo.clone());
        };
        let got = parse_successfully_with("FOO~X", macro_invocation(), set_up_macro_definition);
        assert_eq!(
            got,
            MacroInvocation {
                macro_def: macro_definition_foo,
                param_values: vec![(
                    SymbolName::from("A1"),
                    Some(ArithmeticExpression::from(Atom::from((
                        span(4..5),
                        Script::Normal,
                        SymbolName::from("X"),
                    ))))
                )]
                .into_iter()
                .collect()
            }
        );
    }
}
