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
    Err(super::Unrecognised<'a>),
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
            let tok = match self.inner.next() {
                None => {
                    return EndOfInput;
                }
                Some(Result::Err(())) => {
                    if self.state.in_comment {
                        // Skip.
                        continue;
                    } else {
                        let e: super::Unrecognised = super::Unrecognised {
                            content: self.inner.slice(),
                            span: self.span(),
                        };
                        return Lexeme::Err(e);
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
