#![allow(dead_code)]
// TODO: once the lexer is in use, allow the dead_code warning again.

use std::ops::Range;

use logos::Logos;

type Span = Range<usize>;

mod lower {
    use std::ops::Range;

    use logos::Logos;

    /// InnerToken is the result of a "partial" lexer which only
    /// identifies enough tokens to determine whether we're inside an
    /// RC-block or a comment.  We do this in order to handle
    /// differing interpretations of '}' within a comment; if the
    /// comment is inside an RC-block, then '}' terminates the
    /// RC-block.  But if the comment is not inside an RC-block, then
    /// '}' is not special and forms part of the comment.
    #[derive(Debug, Logos, PartialEq, Clone, Copy)]
    pub(super) enum InnerToken {
        #[regex("[*][*][^}\n]*")]
        CommentStart,

        #[token("\n")]
        Newline,

        // There is no @..@ syntax for left-brace, but if there were,
        // we would need to match it here also.
        #[token("{")]
        LeftBrace,

        #[token("}")]
        RightBrace,

        #[regex("[^ \t{}\n]+", priority = 3)]
        Text,

        #[regex("[ \t]+")]
        Spaces,
    }

    /// State keeps track of whether we are in an RC-block or in a
    /// comment (or both).  Since RC-blocks next, we have to use a
    /// count in order to determine whether a '}' means we're no
    /// longer in an RC-block.
    #[derive(Debug, Default, Clone, Copy)]
    struct State {
        in_comment: bool,
        lbrace_count: usize,
    }

    impl State {
        fn check_set_up_for_start_of_line(&self) {
            assert!(!self.in_comment);
            assert_eq!(self.lbrace_count, 0);
        }
    }

    /// This is the output of LowerLexer.
    pub(super) enum Lexeme<'a> {
        EndOfInput,
        Tok(super::Token),
        Text(&'a str),
    }

    /// LowerLexer uses a Logos-generated scanner to identify braces
    /// and comments, and keeps track of whether we are in an RC-block
    /// or a comment.  Other text is returned as-is.
    #[derive(Debug, Clone)]
    pub(super) struct LowerLexer<'a> {
        inner: logos::Lexer<'a, InnerToken>,
        state: State,
    }

    impl<'a> LowerLexer<'a> {
        pub(super) fn new(input: &'a str) -> LowerLexer<'a> {
            let result = LowerLexer {
                inner: InnerToken::lexer(input),
                state: Default::default(),
            };
            result.state.check_set_up_for_start_of_line();
            result
        }

        pub(crate) fn span(&self) -> Range<usize> {
            self.inner.span()
        }

        pub(super) fn next(&mut self) -> Lexeme<'a> {
            use super::Token;
            use Lexeme::*;

            loop {
                let tok = match dbg!(self.inner.next()) {
                    None => {
                        return EndOfInput;
                    }
                    Some(Err(_)) => {
                        if self.state.in_comment {
                            // Skip.
                            continue;
                        } else {
                            unimplemented!(
                                "pass through text not matched by the lower scanner? '{}'",
                                self.inner.slice()
                            )
                        }
                    }
                    Some(Ok(tok)) => tok,
                };
                match tok {
                    InnerToken::Spaces => {
                        // Skip.
                    }
                    InnerToken::CommentStart => {
                        self.state.in_comment = true;
                    }
                    InnerToken::LeftBrace => {
                        if self.state.in_comment {
                            // Left brace inside a comment is not special,
                            // so we continue skipping the comment text.
                            continue;
                        }
                        self.state.lbrace_count = self.state.lbrace_count.checked_add(1).expect(
                            "the number of '{' on one line should be countable without overflow",
                        );
                        return Tok(Token::LeftBrace);
                    }
                    InnerToken::RightBrace => {
                        match self.state.lbrace_count.checked_sub(1) {
                            None => {
                                if self.state.in_comment {
                                    // Right brace inside a comment, but
                                    // there was no previous left brace.
                                    // Hence the } doesn't terminate an
                                    // RC-block.  So we continue skipping
                                    // the comment text.
                                    continue;
                                }
                                return Tok(Token::RightBrace);
                            }
                            Some(reduced_count) => {
                                self.state.lbrace_count = reduced_count;
                                self.state.in_comment = false;
                                return Tok(Token::RightBrace);
                            }
                        }
                    }
                    InnerToken::Newline => {
                        self.state.lbrace_count = 0;
                        self.state.in_comment = false;
                        self.state.check_set_up_for_start_of_line();
                        return Tok(Token::Newline);
                    }
                    InnerToken::Text => {
                        if self.state.in_comment {
                            continue;
                        }
                        return Text(self.inner.slice());
                    }
                }
            }
        }
    }
}

fn glyph_name(span: Span, prefix_len: usize) -> Span {
    (span.start + 1 + prefix_len)..(span.end - 1)
}

fn normal_glyph_name(lex: &mut logos::Lexer<Token>) -> Span {
    dbg!(lex.slice());
    glyph_name(lex.span(), 0)
}

fn sub_glyph_name(lex: &mut logos::Lexer<Token>) -> Span {
    dbg!(lex.slice());
    glyph_name(lex.span(), 4)
}

fn super_glyph_name(lex: &mut logos::Lexer<Token>) -> Span {
    dbg!(lex.slice());
    glyph_name(lex.span(), 6)
}

#[test]
fn test_glyph_name() {
    assert_eq!(glyph_name(0..6, 0), 1..5);
    assert_eq!(glyph_name(0..10, 4), 5..9);
}

/// The parser consumes these tokens.
#[derive(Debug, PartialEq, Eq, Logos, Clone)]
enum Token {
    LeftBrace,
    RightBrace,
    Newline,

    // Needs to be higher priority than AtGlyph*.
    #[regex("@arr@|->", priority = 20)]
    Arrow,

    #[regex("@super_[^@]*@", super_glyph_name, priority = 10)]
    AtGlyphSuper(Span),

    #[regex("@sub_[^@]*@", sub_glyph_name, priority = 10)]
    AtGlyphSub(Span),

    #[regex("@[^@]*@", normal_glyph_name, priority = 5)]
    AtGlyphNormal(Span),
}

/// This is the primary lexer (and the only one accessible outside
/// this module).  It delegates the task of keeping track of whether
/// we're in an RC-block to a stateful "lower" lexer.  The "lower"
/// lexer's output is an enum, one of whose variants represents a
/// sequence of characters which we know don't contain an RC-block or
/// a comment.  These sequences are scanned by the "upper" lexer
/// (which is generated by Logos).
#[derive(Debug, Clone)]
struct Lexer<'a> {
    lower: lower::LowerLexer<'a>,
    upper: Option<logos::Lexer<'a, Token>>,
}

impl<'a> Lexer<'a> {
    pub(crate) fn new(input: &'a str) -> Lexer<'a> {
        Lexer {
            lower: lower::LowerLexer::new(input),
            upper: None,
        }
    }

    fn span(&self) -> Range<usize> {
        match self.upper.as_ref() {
            None => self.lower.span(),
            Some(upper) => {
                let offset = self.lower.span().start;
                let upper_span = upper.span();
                dbg!(offset);
                dbg!(&upper_span);
                dbg!((upper_span.start + offset)..(upper_span.end + offset))
            }
        }
    }

    fn next_upper(upper: &mut logos::Lexer<'a, Token>) -> Option<Token> {
        match upper.next() {
            None => None,
            Some(Ok(token_from_upper)) => Some(dbg!(token_from_upper)),
            Some(Err(_)) => {
                unimplemented!(
                    "extend upper lexer to handle this text ('{}')",
                    upper.slice(),
                )
            }
        }
    }

    fn spanned(&self) -> SpannedIter<'a> {
        SpannedIter {
            lexer: self.clone(),
        }
    }

    fn get_next(&mut self) -> Option<Token> {
        use lower::Lexeme;
        if let Some(upper_lexer) = self.upper.as_mut() {
            if let Some(t) = Lexer::next_upper(upper_lexer) {
                return Some(t);
            }
        }

        // Fetch more text from the lower lexer.
        self.upper = None;
        match self.lower.next() {
            Lexeme::EndOfInput => None,
            Lexeme::Tok(tok) => Some(tok),
            Lexeme::Text(text) => {
                let lexer = logos::Lexer::new(text);
                self.upper = Some(lexer);
                Lexer::next_upper(
                    self.upper
                        .as_mut()
                        .expect("the option cannot be empty, we just filled it"),
                )
            }
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.get_next()
    }
}

#[derive(Debug, Clone)]
struct SpannedIter<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Iterator for SpannedIter<'a> {
    type Item = (Token, Span);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next().map(|t| (t, self.lexer.span()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan_slices(input: &str) -> Vec<(Token, &str)> {
        dbg!(input);
        dbg!(input.len());
        Lexer::new(input)
            .spanned()
            .map(|(tok, span)| (tok, &input[span]))
            .collect()
    }

    fn scan_tokens_only<'a>(input: &'a str) -> Vec<Token> {
        Lexer::new(input).collect()
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(scan_slices(""), Vec::new());
    }

    #[test]
    fn test_balanced_braces() {
        assert_eq!(
            scan_slices("{}"),
            vec![(Token::LeftBrace, "{"), (Token::RightBrace, "}")]
        );
    }

    #[test]
    fn test_comment_without_content() {
        assert_eq!(scan_slices("**"), Vec::new());
    }

    #[test]
    fn test_comment_with_only_newline() {
        assert_eq!(scan_slices("**\n"), vec![(Token::Newline, "\n")]);
    }

    #[test]
    fn test_comment_x() {
        assert_eq!(scan_slices("**X\n"), vec![(Token::Newline, "\n")]);
    }

    #[test]
    fn test_comment_with_unmatched_rbrace() {
        assert_eq!(
            scan_slices("** THIS } {HELLO} IS A } COMMENT\n"),
            vec![(Token::Newline, "\n")]
        );
    }

    #[test]
    fn test_unmatched_rbrace() {
        assert_eq!(
            scan_slices("}\n"),
            vec![(Token::RightBrace, "}"), (Token::Newline, "\n")]
        );
    }

    #[test]
    fn test_hand_normal() {
        assert_eq!(scan_tokens_only("@hand@"), vec![Token::AtGlyphNormal(1..5)]);
    }

    #[test]
    fn test_hand_sub() {
        assert_eq!(
            scan_tokens_only("@sub_hand@"),
            vec![Token::AtGlyphSub(5..9)]
        );
    }

    #[test]
    fn test_hand_hand_normal() {
        let input = "@hand@@hand@";
        assert_eq!(&input[1..5], "hand");
        assert_eq!(&input[7..11], "hand");

        assert_eq!(
            scan_slices(input),
            vec![
                (Token::AtGlyphNormal(1..5), "@hand@"),
                (Token::AtGlyphNormal(7..11), "@hand@"),
            ]
        );
    }

    #[test]
    fn test_arrow_plain() {
        assert_eq!(scan_tokens_only("->"), vec![Token::Arrow]);
    }

    #[test]
    fn test_double_arrow_plain() {
        assert_eq!(scan_tokens_only("->->"), vec![Token::Arrow, Token::Arrow]);
    }

    #[test]
    fn test_arrow_as_glyph() {
        assert_eq!(scan_tokens_only("@arr@"), vec![Token::Arrow]);
    }

    #[test]
    fn test_upper_lexer_span() {
        // The purpose of this test is to verify that the lexer
        // returns correct span information for tokens (not starting
        // at position 0) identified by the upper lexer.
        assert_eq!(
            scan_slices("{->}"),
            vec![
                (Token::LeftBrace, "{"),
                (Token::Arrow, "->"),
                (Token::RightBrace, "}"),
            ]
        );
    }
}
