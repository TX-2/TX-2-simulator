use super::*;

fn is_error_token(t: &Token) -> bool {
    matches!(t, Token::Error(_))
}

fn scan_slices<'a>(input: &'a str) -> Result<Vec<(Token, &'a str)>, Unrecognised<'a>> {
    dbg!(input);
    dbg!(input.len());

    let mapping =
        |(r, span): (Result<Token, Unrecognised<'a>>, Span)| -> Result<(Token, &str), Unrecognised<'a>> {
            match r {
                Ok(t) => Ok((t, &input[span])),
                Err(e) => Err(e),
            }
        };

    Lexer::new(input).spanned().map(mapping).collect()
}

fn scan_tokens_only<'a>(input: &'a str) -> Result<Vec<Token>, Unrecognised<'a>> {
    Lexer::new(input).collect()
}

#[test]
fn test_lexer_next_newline_rparen() {
    let input = "\n)";
    let mut lex = Lexer::new(input);
    assert_eq!(lex.next(), Some(Ok(Token::Newline)));
    assert_eq!(lex.span(), 0..1);
    assert_eq!(lex.next(), Some(Ok(Token::RightParen)));
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
            sign: Some(Sign::Plus),
            digits: "1".to_string(),
            has_trailing_dot: false
        })])
    );
    assert_eq!(
        scan_tokens_only("-209"),
        Ok(vec![Token::NormalDigits(NumericLiteral {
            sign: Some(Sign::Minus),
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
            sign: Some(Sign::Minus),
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
fn test_subscript_numeric_literal_with_minus_sign() {
    assert_eq!(
        scan_tokens_only("₋₄"),
        Ok(vec![Token::SubscriptDigits(NumericLiteral {
            sign: Some(Sign::Minus),
            digits: "4".to_string(),
            has_trailing_dot: false,
        })])
    );
}

#[test]
fn test_subscript_numeric_literal_with_plus_sign() {
    assert_eq!(
        scan_tokens_only("₊₄"),
        Ok(vec![Token::SubscriptDigits(NumericLiteral {
            sign: Some(Sign::Plus),
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
        scan_tokens_only("@sup_0@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("0"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_1@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("1"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_2@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("2"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_3@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("3"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_4@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("4"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_5@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("5"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_6@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("6"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_7@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("7"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_8@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("8"))])
    );
    assert_eq!(
        scan_tokens_only("@sup_9@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("9"))])
    );

    assert_eq!(
        scan_tokens_only("@sup_9@@sup_9@"),
        Ok(vec![Token::SuperscriptDigits(number_without_dot("99"))])
    );
}

#[test]
fn test_superscript_sign_minus() {
    assert_eq!(
        scan_tokens_only("\u{207B}\u{2074}"),
        Ok(vec![Token::SuperscriptDigits(NumericLiteral {
            sign: Some(Sign::Minus),
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
            sign: Some(Sign::Plus),
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
    assert_eq!(
        scan_tokens_only("A0"),
        Ok(vec![Token::NormalSymexSyllable("A0".to_string())])
    );
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
        scan_tokens_only("@sub_plus@"),
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
    assert_eq!(
        scan_tokens_only("->[THIS IS AN ANNOTATION]->"),
        Ok(vec![Token::Arrow, Token::Arrow,])
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
            Ok(vec![Token::SuperscriptSymexSyllable(expected)]),
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
            Token::SuperscriptSymexSyllable("X".to_string()),
            Token::Dot(Script::Super)
        ]),
        "lexical analysis is incorrect for input '{input}'",
    );
}

#[test]
fn test_xhash() {
    let input = "@sup_X@@sup_hash@";
    assert_eq!(
        scan_tokens_only(input),
        Ok(vec![
            Token::SuperscriptSymexSyllable("X".to_string()),
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
        Ok(vec![Token::SuperscriptSymexSyllable(
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
    match result {
        Ok(tokens) => {
            assert!(tokens.iter().any(is_error_token));
        }
        Err(_) => (),
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
            Ok(vec![Token::SubscriptSymexSyllable(expected)]),
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
        Ok(vec![Token::SubscriptSymexSyllable(
            concat!("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789", "αβγΔελ",).to_string()
        )])
    );
}

#[test]
fn test_subscript_symex_bad() {
    let result = scan_tokens_only("@sub_sps@");
    dbg!(&result);
    match result {
        Ok(tokens) => {
            assert!(tokens.iter().any(is_error_token));
        }
        Err(_) => (),
    }
}

#[test]
fn test_unsubscript_char() {
    assert_eq!(unsubscript_char('₁'), Some('1'));
    assert_eq!(unsubscript_char('₂'), Some('2'));
    assert_eq!(unsubscript_char('₃'), Some('3'));
    assert_eq!(unsubscript_char('₄'), Some('4'));
    assert_eq!(unsubscript_char('₅'), Some('5'));
    assert_eq!(unsubscript_char('₆'), Some('6'));
    assert_eq!(unsubscript_char('₇'), Some('7'));
    assert_eq!(unsubscript_char('₈'), Some('8'));
    assert_eq!(unsubscript_char('₈'), Some('8'));
    assert_eq!(unsubscript_char('₉'), Some('9'));

    assert_eq!(unsubscript_char('\u{208A}'), Some('+'));
    assert_eq!(unsubscript_char('\u{208B}'), Some('-'));
    assert_eq!(unsubscript_char('\u{208C}'), Some('='));
    assert_eq!(unsubscript_char('\u{208D}'), Some('('));
    assert_eq!(unsubscript_char('\u{208E}'), Some(')'));

    assert_eq!(unsubscript_char('\u{2090}'), Some('a'));
    assert_eq!(unsubscript_char('\u{2091}'), Some('e'));
    assert_eq!(unsubscript_char('\u{1D62}'), Some('i'));
    assert_eq!(unsubscript_char('\u{2C7C}'), Some('j'));
    assert_eq!(unsubscript_char('\u{2092}'), Some('o'));
    assert_eq!(unsubscript_char('\u{2093}'), Some('x'));

    assert_eq!(unsubscript_char('\u{2095}'), Some('h'));
    assert_eq!(unsubscript_char('\u{2096}'), Some('k'));
    assert_eq!(unsubscript_char('\u{2097}'), Some('l'));
    assert_eq!(unsubscript_char('\u{2098}'), Some('m'));
    assert_eq!(unsubscript_char('\u{2099}'), Some('n'));
    assert_eq!(unsubscript_char('\u{209A}'), Some('p'));
    assert_eq!(unsubscript_char('\u{209B}'), Some('s'));
    assert_eq!(unsubscript_char('\u{209C}'), Some('t'));
    assert_eq!(unsubscript_char('\u{2093}'), Some('x'));

    // Characters which actually aren't subscripts should result in
    // None.
    assert_eq!(unsubscript_char('x'), None);
}

#[test]
fn test_unsuperscript_char() {
    assert_eq!(unsuperscript_char('⁰'), Some('0'));
    assert_eq!(unsuperscript_char('¹'), Some('1'));
    assert_eq!(unsuperscript_char('²'), Some('2'));
    assert_eq!(unsuperscript_char('³'), Some('3'));
    assert_eq!(unsuperscript_char('⁴'), Some('4'));
    assert_eq!(unsuperscript_char('⁵'), Some('5'));
    assert_eq!(unsuperscript_char('⁶'), Some('6'));
    assert_eq!(unsuperscript_char('⁷'), Some('7'));
    assert_eq!(unsuperscript_char('⁸'), Some('8'));
    assert_eq!(unsuperscript_char('⁹'), Some('9'));
    assert_eq!(unsuperscript_char('ᴬ'), Some('A'));
    assert_eq!(unsuperscript_char('ᴮ'), Some('B'));
    assert_eq!(unsuperscript_char('ᶜ'), Some('C'));
    assert_eq!(unsuperscript_char('ᴰ'), Some('D'));
    assert_eq!(unsuperscript_char('ᴱ'), Some('E'));
    // No F
    assert_eq!(unsuperscript_char('ᴳ'), Some('G'));
    assert_eq!(unsuperscript_char('ᴴ'), Some('H'));
    assert_eq!(unsuperscript_char('ᴵ'), Some('I'));
    assert_eq!(unsuperscript_char('ᴶ'), Some('J'));
    assert_eq!(unsuperscript_char('ᴷ'), Some('K'));
    assert_eq!(unsuperscript_char('ᴸ'), Some('L'));
    assert_eq!(unsuperscript_char('ᴹ'), Some('M'));
    assert_eq!(unsuperscript_char('ᴺ'), Some('N'));
    assert_eq!(unsuperscript_char('ᴼ'), Some('O'));
    assert_eq!(unsuperscript_char('ᴾ'), Some('P'));
    assert_eq!(unsuperscript_char('ᴿ'), Some('R'));
    assert_eq!(unsuperscript_char('ˢ'), Some('S'));
    assert_eq!(unsuperscript_char('ᵀ'), Some('T'));
    assert_eq!(unsuperscript_char('ᵁ'), Some('U'));
    assert_eq!(unsuperscript_char('ⱽ'), Some('V'));
    assert_eq!(unsuperscript_char('ᵂ'), Some('W'));
    // No XYZ
    assert_eq!(unsuperscript_char('ⁱ'), Some('i'));
    assert_eq!(unsuperscript_char('ʲ'), Some('j'));
    assert_eq!(unsuperscript_char('ᵏ'), Some('k'));
    assert_eq!(unsuperscript_char('ⁿ'), Some('n'));
    assert_eq!(unsuperscript_char('ᵖ'), Some('p'));
    assert_eq!(unsuperscript_char('ᵗ'), Some('t'));
    assert_eq!(unsuperscript_char('ʷ'), Some('w'));
    assert_eq!(unsuperscript_char('ˣ'), Some('x'));
    assert_eq!(unsuperscript_char('ʸ'), Some('y'));
    assert_eq!(unsuperscript_char('ᶻ'), Some('z'));
}
