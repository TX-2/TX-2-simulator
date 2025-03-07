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
    assert_eq!(
        scan_tokens_only("@hand@"),
        Ok(vec![Token::AtGlyphNormal(1..5)])
    );
}

#[test]
fn test_hand_sub() {
    assert_eq!(
        scan_tokens_only("@sub_hand@"),
        Ok(vec![Token::AtGlyphSub(5..9)])
    );
}

#[test]
fn test_hand_hand_normal() {
    let input = "@hand@@hand@";
    assert_eq!(&input[1..5], "hand");
    assert_eq!(&input[7..11], "hand");

    assert_eq!(
        scan_slices(input),
        Ok(vec![
            (Token::AtGlyphNormal(1..5), "@hand@"),
            (Token::AtGlyphNormal(7..11), "@hand@"),
        ])
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
