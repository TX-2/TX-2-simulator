use super::*;

fn scan_slices(input: &str) -> Result<Vec<(Token, &str)>, Unrecognised> {
    dbg!(input);
    dbg!(input.len());
    Lexer::new(input)
        .spanned()
        .map(|result| {
            dbg!(match result {
                Ok((tok, span)) => Ok((tok, &input[span])),
                Err(e) => Err(e),
            })
        })
        .collect()
}

fn scan_tokens_only<'a>(input: &'a str) -> Result<Vec<Token>, Unrecognised<'a>> {
    Lexer::new(input).collect()
}

#[test]
fn test_empty_input() {
    assert_eq!(scan_slices(""), Ok(Vec::new()));
}

#[test]
fn test_balanced_braces() {
    assert_eq!(
        scan_slices("{}"),
        Ok(vec![(Token::LeftBrace, "{"), (Token::RightBrace, "}")])
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
        Ok(vec![(Token::RightBrace, "}"), (Token::Newline, "\n")])
    );
}

#[test]
fn test_hand_normal() {
    assert_eq!(scan_tokens_only("@hand@"), Ok(vec![Token::Hand]));
}

#[test]
fn test_hand_hand_normal() {
    let input = "@hand@@hand@";
    assert_eq!(&input[1..5], "hand");
    assert_eq!(&input[7..11], "hand");

    assert_eq!(
        scan_slices(input),
        Ok(vec![(Token::Hand, "@hand@"), (Token::Hand, "@hand@"),])
    );
}

#[test]
fn test_arrow_plain() {
    assert_eq!(scan_tokens_only("->"), Ok(vec![Token::Arrow]));
}

#[test]
fn test_double_arrow_plain() {
    assert_eq!(
        scan_tokens_only("->->"),
        Ok(vec![Token::Arrow, Token::Arrow])
    );
}

#[test]
fn test_arrow_as_glyph() {
    assert_eq!(scan_tokens_only("@arr@"), Ok(vec![Token::Arrow]));
}

#[test]
fn test_upper_lexer_span() {
    // The purpose of this test is to verify that the lexer
    // returns correct span information for tokens (not starting
    // at position 0) identified by the upper lexer.
    assert_eq!(
        scan_slices("{->}"),
        Ok(vec![
            (Token::LeftBrace, "{"),
            (Token::Arrow, "->"),
            (Token::RightBrace, "}"),
        ])
    );
}

#[test]
fn test_normal_digits() {
    assert_eq!(
        scan_tokens_only(" 0"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "0".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 1"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "1".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 2"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "2".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 3"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "3".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 4"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "4".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 5"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "5".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 6"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "6".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 7"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "7".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 8"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "8".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only(" 9"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "9".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("10"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "10".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("11"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "11".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("12"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "12".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("13"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "13".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("14"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "14".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("15"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "15".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("16"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "16".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("17"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "17".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("18"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "18".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("19"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "19".to_string(),
            has_trailing_dot: false
        })])
    );
}

#[test]
fn test_normal_digits_sign() {
    assert_eq!(
        scan_tokens_only("+1"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: Some(Sign::Positive),
            digits: "1".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("-209"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: Some(Sign::Negative),
            digits: "209".to_string(),
            has_trailing_dot: false
        })])
    );
}

#[test]
fn test_normal_digits_trailing_dot_ascii() {
    assert_eq!(
        scan_tokens_only(" 20@dot@"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "20".to_string(),
            has_trailing_dot: true,
        })])
    );

    assert_eq!(
        scan_tokens_only(" 12."),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: None,
            digits: "12".to_string(),
            has_trailing_dot: true,
        })])
    );
}

#[test]
fn test_normal_digits_trailing_centre_dot() {
    assert_eq!(
        scan_tokens_only("-20·"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: Some(Sign::Negative),
            digits: "20".to_string(),
            has_trailing_dot: true,
        })])
    );
}

fn number_without_dot(n: &str) -> NumericLiteral {
    NumericLiteral {
        sign: None,
        digits: n.to_string(),
        has_trailing_dot: false,
    }
}

fn number_with_dot(n: &str) -> NumericLiteral {
    NumericLiteral {
        sign: None,
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
        Ok(vec![Token::SubscriptDigits(number_with_dot("3"))])
    );
}

#[test]
fn test_subscript_digits() {
    let input = "₀₁₂₃₄₅₆₇₈₉";
    assert_eq!(&input[0..30], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::SubscriptDigits(number_without_dot(
            "0123456789"
        ))])
    );
    assert_eq!(
        scan_tokens_only("@sub_0@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("0"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_1@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("1"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_2@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("2"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_3@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("3"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_4@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("4"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_5@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("5"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_6@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("6"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_7@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("7"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_8@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("8"))])
    );
    assert_eq!(
        scan_tokens_only("@sub_9@"),
        Ok(vec![Token::SubscriptDigits(number_without_dot("9"))])
    );

    let input = "@sub_9@@sub_9@";
    assert_eq!(input.len(), 14);
    assert_eq!(&input[0..14], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::SubscriptDigits(number_without_dot("99"))])
    );
}

#[test]
fn test_subscript_sign_minus() {
    assert_eq!(
        scan_tokens_only("₋₄"),
        Ok(vec![Token::SubscriptDigits(NumericLiteral {
            sign: Some(Sign::Negative),
            digits: "4".to_string(),
            has_trailing_dot: false,
        })])
    );
}

#[test]
fn test_subscript_sign_plus() {
    assert_eq!(
        scan_tokens_only("₊₄"),
        Ok(vec![Token::SubscriptDigits(NumericLiteral {
            sign: Some(Sign::Positive),
            digits: "4".to_string(),
            has_trailing_dot: false,
        })])
    );
}

#[test]
fn test_superscript_digits() {
    let input = "\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}";
    assert_eq!(&input[0..27], input);
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![Token::SuperscriptDigits(number_without_dot(
            "0123456789"
        ))])
    );
    assert_eq!(
        scan_tokens_only("@super_0@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("0"))])
    );
    assert_eq!(
        scan_tokens_only("@super_1@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("1"))])
    );
    assert_eq!(
        scan_tokens_only("@super_2@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("2"))])
    );
    assert_eq!(
        scan_tokens_only("@super_3@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("3"))])
    );
    assert_eq!(
        scan_tokens_only("@super_4@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("4"))])
    );
    assert_eq!(
        scan_tokens_only("@super_5@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("5"))])
    );
    assert_eq!(
        scan_tokens_only("@super_6@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("6"))])
    );
    assert_eq!(
        scan_tokens_only("@super_7@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("7"))])
    );
    assert_eq!(
        scan_tokens_only("@super_8@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("8"))])
    );
    assert_eq!(
        scan_tokens_only("@super_9@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("9"))])
    );

    assert_eq!(
        scan_tokens_only("@super_9@@super_9@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("99"))])
    );
}

#[test]
fn test_superscript_sign_minus() {
    assert_eq!(
        scan_tokens_only("\u{207B}\u{2074}"),
        Ok(vec![Token::SuperscriptDigits(NumericLiteral {
            sign: Some(Sign::Negative),
            digits: "4".to_string(),
            has_trailing_dot: false,
        })])
    );
}

#[test]
fn test_superscript_sign_plus() {
    assert_eq!(
        scan_tokens_only("\u{207A}\u{2074}"),
        Ok(vec![Token::SuperscriptDigits(NumericLiteral {
            sign: Some(Sign::Positive),
            digits: "4".to_string(),
            has_trailing_dot: false,
        })])
    );
}

#[test]
fn test_symex_one_syllable_ae_register_names() {
    assert_eq!(
        scan_tokens_only("A"),
        Ok(vec![Token::NormalSymexSyllable("A".to_string())])
    );
    assert_eq!(
        scan_tokens_only("B"),
        Ok(vec![Token::NormalSymexSyllable("B".to_string())])
    );
    assert_eq!(
        scan_tokens_only("C"),
        Ok(vec![Token::NormalSymexSyllable("C".to_string())])
    );
    assert_eq!(
        scan_tokens_only("D"),
        Ok(vec![Token::NormalSymexSyllable("D".to_string())])
    );
    assert_eq!(
        scan_tokens_only("E"),
        Ok(vec![Token::NormalSymexSyllable("E".to_string())])
    );
}

#[test]
fn test_symex_one_syllable_uppercase_normal() {
    assert_eq!(scan_tokens_only("A0"), Ok(vec![Token::NormalSymexSyllable]));
    assert_eq!(
        scan_tokens_only("A02"),
        Ok(vec![Token::NormalSymexSyllable("A02".to_string())])
    );
    assert_eq!(
        scan_tokens_only("BB"),
        Ok(vec![Token::NormalSymexSyllable("BB".to_string())])
    );
    assert_eq!(
        scan_tokens_only("CX"),
        Ok(vec![Token::NormalSymexSyllable("CX".to_string())])
    );
}

#[test]
fn test_symex_one_syllable_lowercase_normal() {
    assert_eq!(
        scan_tokens_only("xyz"),
        Ok(vec![Token::NormalSymexSyllable("xyz".to_string())])
    );
    assert_eq!(
        scan_tokens_only("ijknpqtwxyz"),
        Ok(vec![Token::NormalSymexSyllable("ijknpqtwxyz".to_string())])
    );
}

#[test]
fn test_symex_one_syllable_greek() {
    assert_eq!(
        scan_tokens_only("βαγεΔλ"),
        Ok(vec![Token::NormalSymexSyllable("βαγεΔλ".to_string())])
    );
}

#[test]
fn test_comma() {
    assert_eq!(scan_tokens_only(","), Ok(vec![Token::Comma]));
}

#[test]
fn test_equals() {
    let input = "FOO BAR = 1 ** This is an equality\n";
    assert_eq!(&input[10..11], "1");
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![
            Token::NormalSymexSyllable("FOO".to_string()),
            Token::NormalSymexSyllable("BAR".to_string()),
            Token::Equals,
            Token::NormalDigits(NumericLiteral {
                sign: None,
                digits: "1".to_string(),
                has_trailing_dot: false
            }),
            Token::Newline,
        ])
    );
}

#[test]
fn test_pipe() {
    assert_eq!(
        scan_tokens_only("    START|"),
        Ok(vec![
            Token::NormalSymexSyllable("START".to_string()),
            Token::Pipe,
        ])
    )
}

#[test]
fn test_dot() {
    assert_eq!(scan_tokens_only("."), Ok(vec![Token::Dot,]));
    assert_eq!(scan_tokens_only("·"), Ok(vec![Token::Dot,]));
    assert_eq!(scan_tokens_only("@dot@"), Ok(vec![Token::Dot,]));
}

#[test]
fn test_hold() {
    assert_eq!(scan_tokens_only("h"), Ok(vec![Token::Hold,]));
    assert_eq!(scan_tokens_only(":"), Ok(vec![Token::Hold,]));
}

#[test]
fn test_nothold() {
    assert_eq!(scan_tokens_only("@hbar@"), Ok(vec![Token::NotHold,]));
    // U+0305 is combining overline.
    assert_eq!(scan_tokens_only("\u{0305}h"), Ok(vec![Token::NotHold,]));
    assert_eq!(scan_tokens_only("ℏ"), Ok(vec![Token::NotHold,]));
}

#[test]
fn test_hold_does_not_combine_with_symex() {
    assert_eq!(
        scan_tokens_only("whx"),
        Ok(vec![
            Token::NormalSymexSyllable("w".to_string()),
            Token::Hold, // the h
            Token::NormalSymexSyllable("x".to_string()),
        ])
    );
}

#[test]
fn test_left_paren() {
    assert_eq!(scan_tokens_only("("), Ok(vec![Token::LeftParen,]));
}

#[test]
fn test_right_paren() {
    assert_eq!(scan_tokens_only(")"), Ok(vec![Token::RightParen,]));
}

#[test]
fn test_proper_superset() {
    assert_eq!(scan_tokens_only("⊃"), Ok(vec![Token::ProperSuperset,]));
    // @sup@ is an important corner case, since it is distinct from
    // (say) @sup_sup@
    assert_eq!(scan_tokens_only("@sup@"), Ok(vec![Token::ProperSuperset,]));
}

#[test]
fn test_identical_to() {
    assert_eq!(scan_tokens_only("≡"), Ok(vec![Token::IdenticalTo,]));
    assert_eq!(scan_tokens_only("@hamb@"), Ok(vec![Token::IdenticalTo,]));
}

#[test]
fn test_tilde() {
    assert_eq!(scan_tokens_only("~"), Ok(vec![Token::Tilde,]));
}

#[test]
fn test_less_than() {
    assert_eq!(scan_tokens_only("<"), Ok(vec![Token::LessThan,]));
}

#[test]
fn test_greater_than() {
    assert_eq!(scan_tokens_only(">"), Ok(vec![Token::GreaterThan,]));
}

#[test]
fn test_intersection() {
    assert_eq!(scan_tokens_only("∩"), Ok(vec![Token::Intersection,]));
}

#[test]
fn test_union() {
    assert_eq!(scan_tokens_only("∪"), Ok(vec![Token::Union,]));
}

#[test]
fn test_solidus() {
    assert_eq!(scan_tokens_only("/"), Ok(vec![Token::Solidus,]));
}

#[test]
fn test_times() {
    assert_eq!(scan_tokens_only("×"), Ok(vec![Token::Times,]));
    assert_eq!(scan_tokens_only("@times@"), Ok(vec![Token::Times,]));
}

#[test]
fn test_logical_or() {
    assert_eq!(scan_tokens_only("∨"), Ok(vec![Token::LogicalOr,]));
}

#[test]
fn test_logical_and() {
    assert_eq!(scan_tokens_only("∧"), Ok(vec![Token::LogicalAnd,]));
}

#[test]
fn test_plus() {
    assert_eq!(scan_tokens_only("+"), Ok(vec![Token::Plus,]));
}

#[test]
fn test_minus() {
    assert_eq!(scan_tokens_only("-"), Ok(vec![Token::Minus,]));
}

#[test]
fn test_annotations_are_ignored() {
    assert_eq!(
        scan_tokens_only("->[THIS IS AN ANNOTATION]->"),
        Ok(vec![Token::Arrow, Token::Arrow,])
    );
}
