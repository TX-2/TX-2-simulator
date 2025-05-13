use super::super::glyph::Unrecognised;
use super::*;

fn is_error_token(t: &Token) -> bool {
    matches!(t, Token::Error(_))
}

fn scan_slices(input: &str) -> Result<Vec<(Token, &str)>, Unrecognised> {
    dbg!(input);
    dbg!(input.len());

    let mapping =
        |(r, span): (Result<Token, Unrecognised>, Span)| -> Result<(Token, &str), Unrecognised> {
            match r {
                Ok(t) => Ok((t, &input[span])),
                Err(e) => Err(e),
            }
        };

    Lexer::new(input).spanned().map(mapping).collect()
}

fn scan_tokens_only(input: &str) -> Result<Vec<Token>, Unrecognised> {
    Lexer::new(input).collect()
}

#[test]
fn test_lexer_next_newline_rparen() {
    let input = "\n)";
    let mut lex = Lexer::new(input);
    assert_eq!(lex.next(), Some(Ok(Token::Newline)));
    assert_eq!(lex.span(), 0..1);
    assert_eq!(lex.next(), Some(Ok(Token::RightParen(Script::Normal))));
    assert_eq!(lex.span(), 1..2);
    assert_eq!(lex.next(), None);
}

#[test]
fn test_lexer_next_comment() {
    let input = "**X\n";
    let mut lex = Lexer::new(input);
    assert_eq!(lex.next(), Some(Ok(Token::Newline)));
    assert_eq!(lex.span(), 3..4);
    assert_eq!(&input[3..4], "\n");
}

#[test]
fn test_lexer_spanned_next_comment() {
    let input = "**X\n";
    let mut lex = Lexer::new(input).spanned();
    assert_eq!(lex.next(), Some((Ok(Token::Newline), 3..4)));
    assert_eq!(&input[3..4], "\n");
}

#[test]
fn test_empty_input() {
    assert_eq!(scan_slices(""), Ok(Vec::new()));
}

#[test]
fn test_balanced_braces() {
    assert_eq!(
        scan_slices("{}"),
        Ok(vec![
            (Token::LeftBrace(Script::Normal), "{"),
            (Token::RightBrace(Script::Normal), "}")
        ])
    );
}

#[test]
fn test_comment_without_content() {
    assert_eq!(scan_slices("**"), Ok(Vec::new()));
}

#[test]
fn test_comment_with_only_newline() {
    assert_eq!(scan_slices("**\n"), Ok(vec![(Token::Newline, "\n")]));
}

#[test]
fn test_comment_x() {
    assert_eq!(scan_slices("**X\n"), Ok(vec![(Token::Newline, "\n")]));
}

#[test]
fn test_comment_with_unmatched_rbrace() {
    assert_eq!(
        scan_slices("** THIS } {HELLO} IS A } COMMENT\n"),
        Ok(vec![(Token::Newline, "\n")])
    );
}

#[test]
fn test_unmatched_rbrace() {
    assert_eq!(
        scan_slices("}\n"),
        Ok(vec![
            (Token::RightBrace(Script::Normal), "}"),
            (Token::Newline, "\n")
        ])
    );
}

#[test]
fn test_hand_normal() {
    assert_eq!(
        scan_tokens_only("@hand@"),
        Ok(vec![Token::Hand(Script::Normal)])
    );
}

#[test]
fn test_hand_superscript() {
    assert_eq!(
        scan_tokens_only("@sup_hand@"),
        Ok(vec![Token::Hand(Script::Super)])
    );
}

#[test]
fn test_hand_subscript() {
    assert_eq!(
        scan_tokens_only("@sub_hand@"),
        Ok(vec![Token::Hand(Script::Sub)])
    );
}

#[test]
fn test_hand_hand_normal() {
    use Script::Normal;
    let input = "@hand@@hand@";
    assert_eq!(&input[1..5], "hand");
    assert_eq!(&input[7..11], "hand");

    assert_eq!(
        scan_slices(input),
        Ok(vec![
            (Token::Hand(Normal), "@hand@"),
            (Token::Hand(Normal), "@hand@"),
        ])
    );
}

#[test]
fn test_arrow_plain() {
    assert_eq!(
        scan_tokens_only("->"),
        Ok(vec![Token::Arrow(Script::Normal)])
    );
    // Since the user has @arr@, @sup_arr@, etc. we don't actually
    // require @sub_minus@@sub_greater@ to be understood as an arrow
    // (though it likely is).
}

#[test]
fn test_double_arrow_plain() {
    use Script::Normal;
    assert_eq!(
        scan_tokens_only("->->"),
        Ok(vec![Token::Arrow(Normal), Token::Arrow(Normal)])
    );
}

#[test]
fn test_arrow_as_glyph() {
    use Script::*;
    assert_eq!(scan_tokens_only("@arr@"), Ok(vec![Token::Arrow(Normal)]));

    assert_eq!(scan_tokens_only("@sup_arr@"), Ok(vec![Token::Arrow(Super)]));
    assert_eq!(scan_tokens_only("@sub_arr@"), Ok(vec![Token::Arrow(Sub)]));
}

#[test]
fn test_upper_lexer_span() {
    // The purpose of this test is to verify that the lexer
    // returns correct span information for tokens (not starting
    // at position 0) identified by the upper lexer.
    use Script::Normal;
    assert_eq!(
        scan_slices("{->}"),
        Ok(vec![
            (Token::LeftBrace(Normal), "{"),
            (Token::Arrow(Normal), "->"),
            (Token::RightBrace(Normal), "}"),
        ])
    );
}

#[test]
fn test_normal_digits() {
    assert_eq!(
        scan_tokens_only(" 0"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "0".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 1"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "1".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 2"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "2".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 3"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "3".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 4"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "4".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 5"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "5".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 6"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "6".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 7"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "7".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 8"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "8".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only(" 9"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "9".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("10"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "10".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("11"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "11".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("12"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "12".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("13"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "13".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("14"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "14".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("15"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "15".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("16"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "16".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("17"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "17".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("18"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "18".to_string(),
                has_trailing_dot: false
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("19"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "19".to_string(),
                has_trailing_dot: false
            }
        )])
    );
}

#[test]
fn test_arithemetic_expression_plus() {
    // 1+2 should be lexed as having an infix plus operator, not as
    // two numeric literals with nothing in between.
    assert_eq!(
        scan_tokens_only("1+2"),
        Ok(vec![
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "1".to_string(),
                    has_trailing_dot: false
                }
            ),
            Token::Plus(Script::Normal),
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "2".to_string(),
                    has_trailing_dot: false
                }
            )
        ])
    );
}

#[test]
fn test_arithemetic_expression_minus() {
    // 2-1 should be lexed as having an infix minus operator, not as
    // two numeric literals with nothing in between.
    assert_eq!(
        scan_tokens_only("2-1"),
        Ok(vec![
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "2".to_string(),
                    has_trailing_dot: false
                }
            ),
            Token::Minus(Script::Normal),
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "1".to_string(),
                    has_trailing_dot: false
                }
            )
        ])
    );
}

#[test]
fn test_normal_digits_sign() {
    assert_eq!(
        scan_tokens_only("+1"),
        Ok(vec![
            Token::Plus(Script::Normal),
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "1".to_string(),
                    has_trailing_dot: false
                }
            )
        ])
    );
    assert_eq!(
        scan_tokens_only("-209"),
        Ok(vec![
            Token::Minus(Script::Normal),
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "209".to_string(),
                    has_trailing_dot: false
                }
            )
        ])
    );
}

#[test]
fn test_normal_digits_trailing_dot_ascii() {
    assert_eq!(
        scan_tokens_only(" 20@dot@"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "20".to_string(),
                has_trailing_dot: true,
            }
        )])
    );

    assert_eq!(
        scan_tokens_only(" 12."),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "12".to_string(),
                has_trailing_dot: true,
            }
        )])
    );
}

#[test]
fn test_normal_digits_trailing_centre_dot() {
    assert_eq!(
        scan_tokens_only("20·"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "20".to_string(),
                has_trailing_dot: true,
            }
        )])
    );
    assert_eq!(
        scan_tokens_only("20@dot@"),
        Ok(vec![Token::Digits(
            Script::Normal,
            NumericLiteral {
                digits: "20".to_string(),
                has_trailing_dot: true,
            }
        )])
    );
}

fn number_without_dot(n: &str) -> NumericLiteral {
    NumericLiteral {
        digits: n.to_string(),
        has_trailing_dot: false,
    }
}

fn number_with_dot(n: &str) -> NumericLiteral {
    NumericLiteral {
        digits: n.to_string(),
        has_trailing_dot: true,
    }
}

#[test]
fn test_subscript_digits_trailing_dot() {
    let input = "@sub_3@@sub_dot@";
    assert_eq!(&input[0..16], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Digits(Script::Sub, number_with_dot("3"))])
    );
}

#[test]
fn test_subscript_digits() {
    let input = "₀₁₂₃₄₅₆₇₈₉";
    assert_eq!(&input[0..30], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Digits(
            Script::Sub,
            number_without_dot("0123456789")
        )])
    );
    assert_eq!(
        scan_tokens_only("@sub_0@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("0"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_1@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("1"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_2@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("2"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_3@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("3"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_4@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("4"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_5@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("5"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_6@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("6"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_7@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("7"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_8@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("8"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_9@"),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("9"))])
    );

    let input = "@sub_9@@sub_9@";
    assert_eq!(input.len(), 14);
    assert_eq!(&input[0..14], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Digits(Script::Sub, number_without_dot("99"))])
    );
}

#[test]
fn test_subscript_numeric_literal_with_minus_sign() {
    assert_eq!(
        scan_tokens_only("₋₄"),
        Ok(vec![
            Token::Minus(Script::Sub),
            Token::Digits(
                Script::Sub,
                NumericLiteral {
                    digits: "4".to_string(),
                    has_trailing_dot: false,
                }
            )
        ])
    );
}

#[test]
fn test_subscript_numeric_literal_with_plus_sign() {
    assert_eq!(
        scan_tokens_only("₊₄"),
        Ok(vec![
            Token::Plus(Script::Sub),
            Token::Digits(
                Script::Sub,
                NumericLiteral {
                    digits: "4".to_string(),
                    has_trailing_dot: false,
                }
            )
        ])
    );
}

#[test]
fn test_superscript_digits() {
    let input = "\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}";
    assert_eq!(&input[0..27], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Digits(
            Script::Super,
            number_without_dot("0123456789")
        )])
    );
    assert_eq!(
        scan_tokens_only("@sup_0@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("0"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_1@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("1"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_2@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("2"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_3@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("3"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_4@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("4"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_5@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("5"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_6@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("6"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_7@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("7"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_8@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("8"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_9@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("9"))])
    );

    assert_eq!(
        scan_tokens_only("@sup_9@@sup_9@"),
        Ok(vec![Token::Digits(Script::Super, number_without_dot("99"))])
    );
}

#[test]
fn test_superscript_sign_minus() {
    assert_eq!(
        scan_tokens_only("\u{207B}\u{2074}"),
        Ok(vec![
            Token::Minus(Script::Super),
            Token::Digits(
                Script::Super,
                NumericLiteral {
                    digits: "4".to_string(),
                    has_trailing_dot: false,
                }
            )
        ])
    );
}

#[test]
fn test_superscript_sign_plus() {
    assert_eq!(
        scan_tokens_only("\u{207A}\u{2074}"),
        Ok(vec![
            Token::Plus(Script::Super),
            Token::Digits(
                Script::Super,
                NumericLiteral {
                    digits: "4".to_string(),
                    has_trailing_dot: false,
                }
            )
        ])
    );
}

#[test]
fn test_symex_one_syllable_ae_register_names() {
    assert_eq!(
        scan_tokens_only("A"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "A".to_string())])
    );
    assert_eq!(
        scan_tokens_only("B"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "B".to_string())])
    );
    assert_eq!(
        scan_tokens_only("C"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "C".to_string())])
    );
    assert_eq!(
        scan_tokens_only("D"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "D".to_string())])
    );
    assert_eq!(
        scan_tokens_only("E"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "E".to_string())])
    );
}

#[test]
fn test_symex_one_syllable_uppercase_normal() {
    assert_eq!(
        scan_tokens_only("A0"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "A0".to_string())])
    );
    assert_eq!(
        scan_tokens_only("A02"),
        Ok(vec![Token::SymexSyllable(
            Script::Normal,
            "A02".to_string()
        )])
    );
    assert_eq!(
        scan_tokens_only("BB"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "BB".to_string())])
    );
    assert_eq!(
        scan_tokens_only("CX"),
        Ok(vec![Token::SymexSyllable(Script::Normal, "CX".to_string())])
    );
}

#[test]
fn test_symex_one_syllable_lowercase_normal() {
    assert_eq!(
        scan_tokens_only("xyz"),
        Ok(vec![Token::SymexSyllable(
            Script::Normal,
            "xyz".to_string()
        )])
    );
    assert_eq!(
        scan_tokens_only("ijknpqtwxyz"),
        Ok(vec![Token::SymexSyllable(
            Script::Normal,
            "ijknpqtwxyz".to_string()
        )])
    );
}

#[test]
fn test_symex_one_syllable_greek() {
    assert_eq!(
        scan_tokens_only("βαγεΔλ"),
        Ok(vec![Token::SymexSyllable(
            Script::Normal,
            "βαγεΔλ".to_string()
        )])
    );
}

#[test]
fn test_comma() {
    assert_eq!(
        scan_tokens_only(","),
        Ok(vec![Token::Comma(Script::Normal)])
    );
    assert_eq!(
        scan_tokens_only("@sup_comma@"),
        Ok(vec![Token::Comma(Script::Super)])
    );
    assert_eq!(
        scan_tokens_only("@sub_comma@"),
        Ok(vec![Token::Comma(Script::Sub)])
    );
}

#[test]
fn test_equals() {
    let input = "FOO BAR = 1 ** This is an equality\n";
    assert_eq!(&input[10..11], "1");
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![
            Token::SymexSyllable(Script::Normal, "FOO".to_string()),
            Token::SymexSyllable(Script::Normal, "BAR".to_string()),
            Token::Equals(Script::Normal),
            Token::Digits(
                Script::Normal,
                NumericLiteral {
                    digits: "1".to_string(),
                    has_trailing_dot: false
                }
            ),
            Token::Newline,
        ])
    );
}

#[test]
fn test_pipe() {
    assert_eq!(
        scan_tokens_only("    START|"),
        Ok(vec![
            Token::SymexSyllable(Script::Normal, "START".to_string()),
            Token::Pipe(Script::Normal),
        ])
    )
}

#[test]
fn test_hold() {
    assert_eq!(scan_tokens_only("h"), Ok(vec![Token::Hold,]));
    assert_eq!(scan_tokens_only(":"), Ok(vec![Token::Hold,]));
}

#[test]
fn test_nothold() {
    assert_eq!(scan_tokens_only("\u{0305}h"), Ok(vec![Token::NotHold,]));
    assert_eq!(scan_tokens_only("ℏ"), Ok(vec![Token::NotHold,]));
}

#[test]
fn test_hold_does_not_combine_with_symex() {
    assert_eq!(
        scan_tokens_only("whx"),
        Ok(vec![
            Token::SymexSyllable(Script::Normal, "w".to_string()),
            Token::Hold, // the h
            Token::SymexSyllable(Script::Normal, "x".to_string()),
        ])
    );
}

#[test]
fn test_left_paren() {
    assert_eq!(
        scan_tokens_only("("),
        Ok(vec![Token::LeftParen(Script::Normal),])
    );
    assert_eq!(
        scan_tokens_only("@lparen@"),
        Ok(vec![Token::LeftParen(Script::Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sub_lparen@"),
        Ok(vec![Token::LeftParen(Script::Sub),])
    );
    assert_eq!(
        scan_tokens_only("@sup_lparen@"),
        Ok(vec![Token::LeftParen(Script::Super),])
    );
}

#[test]
fn test_right_paren() {
    let input = ")";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::RightParen(Script::Normal)]),
        "failed to correctly parse '{input}'",
    );

    let input = "@rparen@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::RightParen(Script::Normal),]),
        "failed to correctly parse '{input}'",
    );

    let input = "@sub_rparen@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::RightParen(Script::Sub),]),
        "failed to correctly parse '{input}'",
    );

    let input = "@sup_rparen@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::RightParen(Script::Super),]),
        "failed to correctly parse '{input}'",
    );
}

#[test]
fn test_proper_superset() {
    use Script::*;
    assert_eq!(
        scan_tokens_only("⊃"),
        Ok(vec![Token::ProperSuperset(Normal),])
    );
    // @sup@ is an important corner case, since it is distinct from
    // (say) @sup_sup@
    assert_eq!(
        scan_tokens_only("@sup@"),
        Ok(vec![Token::ProperSuperset(Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sup_sup@"),
        Ok(vec![Token::ProperSuperset(Super),])
    );
    assert_eq!(
        scan_tokens_only("@sub_sup@"),
        Ok(vec![Token::ProperSuperset(Sub),])
    );
}

#[test]
fn test_subset_of() {
    use Script::*;
    assert_eq!(scan_tokens_only("⊂"), Ok(vec![Token::SubsetOf(Normal),]));
    // @sup@ is an important corner case, since it is distinct from
    // (say) @sup_sup@
    assert_eq!(
        scan_tokens_only("@subsetof@"),
        Ok(vec![Token::SubsetOf(Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sup_subsetof@"),
        Ok(vec![Token::SubsetOf(Super),])
    );
    assert_eq!(
        scan_tokens_only("@sub_subsetof@"),
        Ok(vec![Token::SubsetOf(Sub),])
    );
}

#[test]
fn test_identical_to() {
    use Script::*;
    assert_eq!(scan_tokens_only("≡"), Ok(vec![Token::IdenticalTo(Normal),]));
    assert_eq!(
        scan_tokens_only("@hamb@"),
        Ok(vec![Token::IdenticalTo(Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sup_hamb@"),
        Ok(vec![Token::IdenticalTo(Super),])
    );
    assert_eq!(
        scan_tokens_only("@sub_hamb@"),
        Ok(vec![Token::IdenticalTo(Sub),])
    );
}

#[test]
fn test_tilde() {
    assert_eq!(
        scan_tokens_only("~"),
        Ok(vec![Token::Tilde(Script::Normal),])
    );
    assert_eq!(
        scan_tokens_only("@tilde@"),
        Ok(vec![Token::Tilde(Script::Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sup_tilde@"),
        Ok(vec![Token::Tilde(Script::Super),])
    );
    assert_eq!(
        scan_tokens_only("@sub_tilde@"),
        Ok(vec![Token::Tilde(Script::Sub),])
    );
}

#[test]
fn test_less_than() {
    use Script::*;
    assert_eq!(scan_tokens_only("<"), Ok(vec![Token::LessThan(Normal),]));
    assert_eq!(
        scan_tokens_only("@lessthan@"),
        Ok(vec![Token::LessThan(Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sub_lessthan@"),
        Ok(vec![Token::LessThan(Sub),])
    );
    assert_eq!(
        scan_tokens_only("@sup_lessthan@"),
        Ok(vec![Token::LessThan(Super),])
    );
}

#[test]
fn test_greater_than() {
    use Script::*;
    assert_eq!(scan_tokens_only(">"), Ok(vec![Token::GreaterThan(Normal),]));
    assert_eq!(
        scan_tokens_only("@greaterthan@"),
        Ok(vec![Token::GreaterThan(Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sub_greaterthan@"),
        Ok(vec![Token::GreaterThan(Sub),])
    );
    assert_eq!(
        scan_tokens_only("@sup_greaterthan@"),
        Ok(vec![Token::GreaterThan(Super),])
    );
}

#[test]
fn test_intersection() {
    use Script::*;
    assert_eq!(scan_tokens_only("∩"), Ok(vec![Token::Intersection(Normal)]));
    assert_eq!(
        scan_tokens_only("@sup_intersection@"),
        Ok(vec![Token::Intersection(Super)])
    );
    assert_eq!(
        scan_tokens_only("@intersection@"),
        Ok(vec![Token::Intersection(Normal)])
    );
    assert_eq!(
        scan_tokens_only("@sub_intersection@"),
        Ok(vec![Token::Intersection(Sub)])
    );
}

#[test]
fn test_union() {
    use Script::*;
    assert_eq!(scan_tokens_only("∪"), Ok(vec![Token::Union(Normal)]));
    assert_eq!(
        scan_tokens_only("@sup_union@"),
        Ok(vec![Token::Union(Super)])
    );
    assert_eq!(scan_tokens_only("@union@"), Ok(vec![Token::Union(Normal)]));
    assert_eq!(scan_tokens_only("@sub_union@"), Ok(vec![Token::Union(Sub)]));
}

#[test]
fn test_solidus() {
    assert_eq!(
        scan_tokens_only("/"),
        Ok(vec![Token::Solidus(Script::Normal)])
    );
    assert_eq!(
        scan_tokens_only("@solidus@"),
        Ok(vec![Token::Solidus(Script::Normal)])
    );
    assert_eq!(
        scan_tokens_only("@sup_solidus@"),
        Ok(vec![Token::Solidus(Script::Super)])
    );
    assert_eq!(
        scan_tokens_only("@sub_solidus@"),
        Ok(vec![Token::Solidus(Script::Sub)])
    );
}

#[test]
fn test_times() {
    assert_eq!(
        scan_tokens_only("×"),
        Ok(vec![Token::Times(Script::Normal),])
    );
    assert_eq!(
        scan_tokens_only("@times@"),
        Ok(vec![Token::Times(Script::Normal),])
    );
    assert_eq!(
        scan_tokens_only("@sup_times@"),
        Ok(vec![Token::Times(Script::Super),])
    );
    assert_eq!(
        scan_tokens_only("@sub_times@"),
        Ok(vec![Token::Times(Script::Sub),])
    );
}

#[test]
fn test_logical_or() {
    assert_eq!(
        scan_tokens_only("∨"),
        Ok(vec![Token::LogicalOr(Script::Normal),])
    );
}

#[test]
fn test_logical_and() {
    assert_eq!(
        scan_tokens_only("∧"),
        Ok(vec![Token::LogicalAnd(Script::Normal),])
    );
}

#[test]
fn test_plus() {
    assert_eq!(
        scan_tokens_only("+"),
        Ok(vec![Token::Plus(Script::Normal),])
    );
}

#[test]
fn test_subscript_plus_unicode() {
    assert_eq!(
        scan_tokens_only("\u{208A}"),
        Ok(vec![Token::Plus(Script::Sub),])
    );
}

#[test]
fn test_subscript_plus_named_glyph() {
    assert_eq!(
        scan_tokens_only("@sub_add@"), // @sub_plus@ is not a valid glyph name
        Ok(vec![Token::Plus(Script::Sub),])
    );
}

#[test]
fn test_superscript_plus_unicode() {
    assert_eq!(
        scan_tokens_only("\u{207A}"),
        Ok(vec![Token::Plus(Script::Super),])
    );
}

#[test]
fn test_normal_minus() {
    assert_eq!(
        scan_tokens_only("-"),
        Ok(vec![Token::Minus(Script::Normal),])
    );
}

#[test]
fn test_subscript_minus() {
    assert_eq!(
        scan_tokens_only("@sub_minus@"),
        Ok(vec![Token::Minus(Script::Sub),])
    );
}

#[test]
fn test_subscript_named_glyph() {
    assert_eq!(
        scan_tokens_only("\u{208B}"),
        Ok(vec![Token::Minus(Script::Sub),])
    );
}

#[test]
fn test_superscript_minus_named_glyph() {
    assert_eq!(
        scan_tokens_only("@sup_minus@"),
        Ok(vec![Token::Minus(Script::Super),])
    );
}

#[test]
fn test_superscript_minus_unicode() {
    assert_eq!(
        scan_tokens_only("\u{207B}"),
        Ok(vec![Token::Minus(Script::Super),])
    );
}

#[test]
fn test_annotations_are_ignored() {
    use Script::Normal;
    assert_eq!(
        scan_tokens_only("->[THIS IS AN ANNOTATION]->"),
        Ok(vec![Token::Arrow(Normal), Token::Arrow(Normal),])
    );
}

#[test]
fn test_superscript_symex_short() {
    for (input, normal) in [
        ("ᴬ", "A"),
        ("@sup_A@", "A"),
        ("ᴮ", "B"),
        ("@sup_B@", "B"),
        ("ꟲ", "C"), // U+A7F2
        ("@sup_C@", "C"),
        ("ᴰ", "D"),
        ("@sup_D@", "D"),
        ("@sup_E@", "E"),
        ("ᴱ", "E"),
        ("ꟳ", "F"),
        ("@sup_F@", "F"),
        ("@sup_G@", "G"),
        ("ᴳ", "G"),
        ("@sup_G@", "G"),
        ("ᴴ", "H"),
        ("@sup_H@", "H"),
        ("ᴵ", "I"),
        ("@sup_I@", "I"),
        ("ᴶ", "J"),
        ("@sup_J@", "J"),
        ("ᴷ", "K"),
        ("@sup_K@", "K"),
        ("ᴸ", "L"),
        ("@sup_L@", "L"),
        ("ᴹ", "M"),
        ("@sup_M@", "M"),
        ("ᴺ", "N"),
        ("@sup_N@", "N"),
        ("ᴼ", "O"),
        ("@sup_O@", "O"),
        ("ᴾ", "P"),
        ("@sup_P@", "P"),
        ("ꟴ", "Q"),
        ("@sup_Q@", "Q"),
        ("ᴿ", "R"),
        ("@sup_R@", "R"),
        ("@sup_S@", "S"),
        ("ᵀ", "T"),
        ("@sup_T@", "T"),
        ("ᵁ", "U"),
        ("ⱽ", "V"),
        ("@sup_V@", "V"),
        ("ᵂ", "W"),
        ("@sup_W@", "W"),
        // We put a letter before digits so they don't get matched as
        // numeric literals.
        ("@sup_X@\u{2070}", "X0"),
        ("@sup_X@@sup_0@", "X0"),
        ("@sup_X@\u{00B9}", "X1"),
        ("@sup_X@@sup_1@", "X1"),
        ("@sup_X@\u{00B2}", "X2"),
        ("@sup_X@@sup_2@", "X2"),
        ("@sup_X@\u{00B3}", "X3"),
        ("@sup_X@@sup_3@", "X3"),
        ("@sup_X@\u{2074}", "X4"),
        ("@sup_X@@sup_4@", "X4"),
        ("@sup_X@\u{2075}", "X5"),
        ("@sup_X@@sup_5@", "X5"),
        ("@sup_X@\u{2076}", "X6"),
        ("@sup_X@@sup_6@", "X6"),
        ("@sup_X@\u{2077}", "X7"),
        ("@sup_X@@sup_7@", "X7"),
        ("@sup_X@\u{2078}", "X8"),
        ("@sup_X@@sup_8@", "X8"),
        ("@sup_X@\u{2079}", "X9"),
        ("@sup_X@@sup_9@", "X9"),
        ("@sup_i@", "i"),
        ("@sup_j@", "j"),
        ("@sup_k@", "k"),
        ("@sup_n@", "n"),
        ("@sup_p@", "p"),
        ("@sup_q@", "q"),
        ("@sup_t@", "t"),
        ("@sup_w@", "w"),
        ("@sup_x@", "x"),
        ("@sup_y@", "y"),
        ("@sup_z@", "z"),
        ("@sup_alpha@", "α"),
        ("@sup_beta@", "β"),
        ("@sup_gamma@", "γ"),
        ("@sup_delta@", "Δ"),
        ("@sup_eps@", "ε"),
        ("@sup_lambda@", "λ"),
    ] {
        let expected = normal.to_string();
        assert_eq!(
            scan_tokens_only(input),
            Ok(vec![Token::SymexSyllable(Script::Super, expected)]),
            "lexical analysis is incorrect for input '{input}'",
        );
    }
}

#[test]
fn test_xdot() {
    let input = "@sup_X@@sup_dot@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![
            // Dot can actually be part of a symex, so in principle,
            // these should not be separate tokens.
            //
            // However, we handle dot specially (i.e. in the parser)
            // because it can also be a macro terminator.
            //
            // See Users Handbook, section 6-2.3, "RULES FOR SYMEX
            // FORMATION".
            Token::SymexSyllable(Script::Super, "X".to_string()),
            Token::Dot(Script::Super)
        ]),
        "lexical analysis is incorrect for input '{input}'",
    );
}

#[test]
fn test_foo3() {
    let input = "FOO=₃";
    let mut lex = Lexer::new(input);

    dbg!(&input[0..3]);
    assert_eq!(
        lex.next(),
        Some(Ok(Token::SymexSyllable(Script::Normal, "FOO".to_string())))
    );
    assert_eq!(lex.span(), 0..3);

    dbg!(&input[3..4]);
    assert_eq!(lex.next(), Some(Ok(Token::Equals(Script::Normal))));
    assert_eq!(lex.span(), 3..4);

    dbg!(&input[4..7]);
    assert_eq!(
        lex.next(),
        Some(Ok(Token::Digits(
            Script::Sub,
            NumericLiteral {
                digits: "3".to_string(),
                has_trailing_dot: false
            }
        )))
    );
    // The key point about the next assertion is that slice indices
    // and spans are both byte positins, not character indexes.
    assert_eq!(lex.span(), 4..7);
    assert_eq!(lex.next(), None);
}

#[test]
fn test_xhash() {
    let input = "@sup_X@@sup_hash@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![
            Token::SymexSyllable(Script::Super, "X".to_string()),
            Token::Hash(Script::Super)
        ]),
        "lexical analysis is incorrect for input '{input}'",
    );
}

#[test]
fn test_sup_dot() {
    let input = "@sup_dot@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Dot(Script::Super)]),
        "lexical analysis is incorrect for input '{input}'",
    );

    assert_eq!(
        scan_tokens_only("@sup_dot@"),
        Ok(vec![Token::Dot(Script::Super),])
    );
}

#[test]
fn test_sub_dot() {
    let input = "@sub_dot@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Dot(Script::Sub)]),
        "lexical analysis is incorrect for input '{input}'",
    );
    assert_eq!(
        scan_tokens_only("@sub_dot@"),
        Ok(vec![Token::Dot(Script::Sub),])
    );
}

#[test]
fn test_normal_dot_1() {
    assert_eq!(scan_tokens_only("."), Ok(vec![Token::Dot(Script::Normal),]));
    assert_eq!(scan_tokens_only("·"), Ok(vec![Token::Dot(Script::Normal)]));
    assert_eq!(
        scan_tokens_only("@dot@"),
        Ok(vec![Token::Dot(Script::Normal)])
    );
}

#[test]
fn test_normal_dot_2() {
    let input = "@dot@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::Dot(Script::Normal)]),
        "lexical analysis is incorrect for input '{input}'",
    );
}

#[test]
fn test_superscript_symex_long() {
    // We don't include a @sup_dot@ here because that is handled in
    // the parser (we return it as a separate token).
    assert_eq!(
        scan_tokens_only(concat!(
            "ᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁⱽᵂ⁰¹²³⁴⁵⁶⁷⁸⁹",
            "@sup_alpha@",
            "@sup_beta@",
            "@sup_gamma@",
            "@sup_delta@",
            "@sup_eps@",
            "@sup_lambda@",
            "ꟲꟳꟴ",
            "@sup_A@",
            "@sup_B@",
            "@sup_C@",
            "@sup_D@",
            "@sup_E@",
            "@sup_F@",
            "@sup_G@",
            "@sup_H@",
            "@sup_I@",
            "@sup_J@",
            "@sup_K@",
            "@sup_L@",
            "@sup_M@",
            "@sup_N@",
            "@sup_O@",
            "@sup_P@",
            "@sup_Q@",
            "@sup_R@",
            "@sup_S@",
            "@sup_T@",
            "@sup_U@",
            "@sup_V@",
            "@sup_W@",
            "@sup_X@",
            "@sup_Y@",
            "@sup_Z@",
            "@sup_0@",
            "@sup_1@",
            "@sup_2@",
            "@sup_3@",
            "@sup_4@",
            "@sup_5@",
            "@sup_6@",
            "@sup_7@",
            "@sup_8@",
            "@sup_9@",
            "@sup_i@",
            "@sup_j@",
            "@sup_k@",
            "@sup_n@",
            "@sup_p@",
            "@sup_q@",
            "@sup_t@",
            "@sup_w@",
            "@sup_x@",
            "@sup_y@",
            "@sup_z@",
            "ⁱʲᵏⁿᵖᵗʷˣʸᶻ",
            "@sup_apostrophe@",
            // Missing: underbar, overbar, square, circle (watch out
            // for the fact that some of those are part of a compound
            // character).  Space is not missing (this is a syllable,
            // not the whole symex).
        )),
        Ok(vec![Token::SymexSyllable(
            Script::Super,
            concat!(
                "ABDEGHIJKLMNOPRTUVW",
                "0123456789",
                "αβγΔελ",
                "CFQ",
                "ABCDEFGHIJKLMNOPQRSTUVWXYZ",
                "0123456789",
                "ijknpqtwxyz",
                "ijknptwxyz",
                "'"
            )
            .to_string()
        )])
    );
}

#[test]
fn test_superscript_symex_bad() {
    let result = scan_tokens_only("@sup_sps@");
    dbg!(&result);
    if let Ok(tokens) = result {
        assert!(tokens.iter().any(is_error_token));
    }
}

#[test]
fn test_subscript_symex_short() {
    // @sub_dot@ isn't in here.  We handle it in the parser because it
    // has multiple possible meanings (as a macro terminator, as a
    // component of a symex).
    for (input, normal) in [
        ("@sub_A@", "A"),
        ("@sub_A@@sub_A@", "AA"),
        ("@sub_B@", "B"),
        ("@sub_C@", "C"),
        ("@sub_D@", "D"),
        ("@sub_E@", "E"),
        ("@sub_F@", "F"),
        ("@sub_G@", "G"),
        ("@sub_G@", "G"),
        ("@sub_H@", "H"),
        ("@sub_I@", "I"),
        ("@sub_J@", "J"),
        ("@sub_K@", "K"),
        ("@sub_L@", "L"),
        ("@sub_M@", "M"),
        ("@sub_N@", "N"),
        ("@sub_O@", "O"),
        ("@sub_P@", "P"),
        ("@sub_Q@", "Q"),
        ("@sub_R@", "R"),
        ("@sub_S@", "S"),
        ("@sub_T@", "T"),
        ("@sub_U@", "U"),
        ("@sub_V@", "V"),
        ("@sub_W@", "W"),
        ("@sub_i@", "i"),
        ("@sub_j@", "j"),
        ("@sub_k@", "k"),
        ("@sub_n@", "n"),
        ("@sub_p@", "p"),
        ("@sub_q@", "q"),
        ("@sub_t@", "t"),
        ("@sub_w@", "w"),
        ("@sub_x@", "x"),
        ("@sub_y@", "y"),
        ("@sub_z@", "z"),
        ("@sub_alpha@", "α"),
        ("@sub_beta@", "β"),
        ("@sub_gamma@", "γ"),
        ("@sub_delta@", "Δ"),
        ("@sub_eps@", "ε"),
        ("@sub_lambda@", "λ"),
        // Prefix digits with something else so that the input doesn't
        // get matches as a literal.
        // Prefix digits with a letter to avoid lexing as
        // SubscriptDigits instead.
        ("@sub_X@@sub_0@", "X0"),
        ("@sub_X@@sub_1@", "X1"),
        ("@sub_X@@sub_2@", "X2"),
        ("@sub_X@@sub_3@", "X3"),
        ("@sub_X@@sub_4@", "X4"),
        ("@sub_X@@sub_5@", "X5"),
        ("@sub_X@@sub_6@", "X6"),
        ("@sub_X@@sub_7@", "X7"),
        ("@sub_X@@sub_8@", "X8"),
        ("@sub_X@@sub_9@", "X9"),
        ("@sub_alpha@₀", "α0"),
        ("@sub_alpha@₁", "α1"),
        ("@sub_alpha@₂", "α2"),
        ("@sub_alpha@₃", "α3"),
        ("@sub_alpha@₄", "α4"),
        ("@sub_alpha@₅", "α5"),
        ("@sub_alpha@₆", "α6"),
        ("@sub_alpha@₇", "α7"),
        ("@sub_alpha@₈", "α8"),
        ("@sub_alpha@₉", "α9"),
        ("@sub_gamma@\u{2080}", "γ0"),
        ("@sub_gamma@\u{2081}", "γ1"),
        ("@sub_gamma@\u{2082}", "γ2"),
        ("@sub_gamma@\u{2083}", "γ3"),
        ("@sub_gamma@\u{2084}", "γ4"),
        ("@sub_gamma@\u{2085}", "γ5"),
        ("@sub_gamma@\u{2086}", "γ6"),
        ("@sub_gamma@\u{2087}", "γ7"),
        ("@sub_gamma@\u{2088}", "γ8"),
        ("@sub_gamma@\u{2089}", "γ9"),
    ] {
        let expected = normal.to_string();
        assert_eq!(
            scan_tokens_only(input),
            Ok(vec![Token::SymexSyllable(Script::Sub, expected)]),
            "Incorrect tokenization of '{input}'"
        );
    }
}

#[test]
fn test_subscript_symex_long() {
    // We don't include a @sub_dot@ here because that is handled in
    // the parser (we return it as a separate token).
    assert_eq!(
        scan_tokens_only(concat!(
            "@sub_A@",
            "@sub_B@",
            "@sub_C@",
            "@sub_D@",
            "@sub_E@",
            "@sub_F@",
            "@sub_G@",
            "@sub_H@",
            "@sub_I@",
            "@sub_J@",
            "@sub_K@",
            "@sub_L@",
            "@sub_M@",
            "@sub_N@",
            "@sub_O@",
            "@sub_P@",
            "@sub_Q@",
            "@sub_R@",
            "@sub_S@",
            "@sub_T@",
            "@sub_U@",
            "@sub_V@",
            "@sub_W@",
            "@sub_X@",
            "@sub_Y@",
            "@sub_Z@",
            "@sub_0@",
            "@sub_1@",
            "@sub_2@",
            "@sub_3@",
            "@sub_4@",
            "@sub_5@",
            "@sub_6@",
            "@sub_7@",
            "@sub_8@",
            "@sub_9@",
            "@sub_alpha@",
            "@sub_beta@",
            "@sub_gamma@",
            "@sub_delta@",
            "@sub_eps@",
            "@sub_lambda@",
        )),
        Ok(vec![Token::SymexSyllable(
            Script::Sub,
            concat!("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789", "αβγΔελ",).to_string()
        )])
    );
}

#[test]
fn test_subscript_symex_bad() {
    let result = scan_tokens_only("@sub_sps@");
    dbg!(&result);
    if let Ok(tokens) = result {
        assert!(tokens.iter().any(is_error_token));
    }
}

#[test]
fn merge_makes_bit_selector() {
    let input = "@sub_4@@sub_dot@@sub_1@";
    assert_eq!(input.len(), 23);

    let left = Token::Digits(
        Script::Sub,
        NumericLiteral {
            digits: "4".to_string(),
            has_trailing_dot: true,
        },
    );
    let right = Token::Digits(
        Script::Sub,
        NumericLiteral {
            digits: "1".to_string(),
            has_trailing_dot: false,
        },
    );
    assert_eq!(
        merge_tokens((Ok(left), 0..16), (Ok(right), 16..23)),
        TokenMergeResult::Merged(
            Token::BitPosition(Script::Sub, "4".to_string(), "1".to_string()),
            0..23
        )
    )
}

#[test]
fn merge_another_dot_onto_bit_selector() {
    let input = "@sub_4@@sub_dot@@sub_1@@sub_dot@";
    assert_eq!(input.len(), 32);

    let left = Token::BitPosition(Script::Sub, "4".to_string(), "1".to_string());
    let right = Token::Dot(Script::Sub);
    assert_eq!(
        merge_tokens((Ok(left), 0..23), (Ok(right), 23..32)),
        TokenMergeResult::Merged(Token::SymexSyllable(Script::Sub, "4·1·".to_string()), 0..32)
    )
}

#[test]
fn merge_letter_onto_bit_selector() {
    let input = "@sub_4@@sub_dot@@sub_1@@sub_C@";
    assert_eq!(input.len(), 30);

    let left = Token::BitPosition(Script::Sub, "4".to_string(), "1".to_string());
    let right = Token::SymexSyllable(Script::Sub, "C".to_string());
    assert_eq!(
        merge_tokens((Ok(left), 0..23), (Ok(right), 23..30)),
        TokenMergeResult::Merged(Token::SymexSyllable(Script::Sub, "4·1C".to_string()), 0..30)
    )
}
