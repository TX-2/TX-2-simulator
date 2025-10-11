//! A "partial" lexer which determines whether we're inside an
//! RC-block or a comment.
use std::ops::Range;

use logos::Logos;

use base::charset::Script;

use super::super::glyph::Unrecognised;

/// `InnerToken` is the result of a "partial" lexer which only
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

    /// We use annotations in source files where we want a comment which isn't part of
    // the assembler syntax.  The interpretations of annotations may
    // change in the future (but comments will not) so you should
    // generally prefer to use a comment.
    //
    // Should be higher-priority than Text.
    #[regex(r"\[[^]]*\]", priority = 5)]
    Annotation,

    // There is no @..@ syntax for left-brace, but if there were,
    // we would need to match it here also.
    #[token("{")]
    LeftBrace,

    #[token("}")]
    RightBrace,

    // The Regex crate allows escaping in character classes, which is
    // something we need to do to use '[' in a (negated in this case)
    // character class.
    #[regex("[^ \\[\t{}\n]+", priority = 3)]
    Text,

    // We distinguish tab from spaces because they are handled
    // differently.  Space is allowed inside symexes while tab is not.
    #[token("\t")]
    Tab,

    #[regex("[ ]+")]
    Spaces,
}

/// Keep track of whether we are in an RC-block, in a comment, or
/// both.
///
/// RC-blocks nest, so we have to use a count in order to determine
/// whether a '}' means we're no longer in an RC-block.
#[derive(Debug, Default, Clone, Copy)]
struct State {
    /// Are we in a comment?
    in_comment: bool,

    /// Count of open braces.
    lbrace_count: usize,
}

impl State {
    fn check_set_up_for_start_of_line(&self) {
        assert!(!self.in_comment);
        assert_eq!(self.lbrace_count, 0);
    }
}

/// This is the output of `LowerLexer`.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum Lexeme<'a> {
    EndOfInput,
    Tok(super::Token),
    Text(&'a str),
    Err(Unrecognised),
}

/// `LowerLexer` uses a Logos-generated scanner to identify braces
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

        loop {
            let tok = match self.inner.next() {
                None => {
                    return Lexeme::EndOfInput;
                }
                Some(Result::Err(())) => {
                    if self.state.in_comment {
                        // Skip.
                        continue;
                    }
                    match self.inner.slice().chars().next() {
                        Some(ch) => {
                            return Lexeme::Err(Unrecognised::InvalidChar(ch));
                        }
                        None => {
                            panic!("LowerLexer::next(): got error on zero-length content");
                        }
                    }
                }
                Some(Ok(tok)) => tok,
            };
            match tok {
                InnerToken::Spaces | InnerToken::Annotation => {
                    // Skip.
                }
                InnerToken::Tab => {
                    // Parse tab differently to avoid joining symex
                    // symbols across a space.  Per section 6-2.3 of
                    // the User Handbook, tab is not allowed inside a
                    // symex.
                    return Lexeme::Tok(Token::Tab);
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
                    return Lexeme::Tok(Token::LeftBrace(Script::Normal));
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
                            return Lexeme::Tok(Token::RightBrace(Script::Normal));
                        }
                        Some(reduced_count) => {
                            self.state.lbrace_count = reduced_count;
                            self.state.in_comment = false;
                            return Lexeme::Tok(Token::RightBrace(Script::Normal));
                        }
                    }
                }
                InnerToken::Newline => {
                    self.state.lbrace_count = 0;
                    self.state.in_comment = false;
                    self.state.check_set_up_for_start_of_line();
                    return Lexeme::Tok(Token::Newline);
                }
                InnerToken::Text => {
                    if self.state.in_comment {
                        continue;
                    }
                    return Lexeme::Text(self.inner.slice());
                }
            }
        }
    }
}

#[test]
fn test_annotations_are_ignored() {
    let input = "->[THIS IS AN ANNOTATION]";
    let mut lex = LowerLexer::new(input);
    assert_eq!(lex.next(), Lexeme::Text("->"));
    assert_eq!(lex.next(), Lexeme::EndOfInput);
}

#[test]
fn test_span() {
    let input = "XZ Y";
    let mut lex = LowerLexer::new(input);
    assert_eq!(lex.next(), Lexeme::Text("XZ"));
    assert_eq!(&input[lex.span()], "XZ");
    assert_eq!(lex.next(), Lexeme::Text("Y"));
    assert_eq!(&input[lex.span()], "Y");
}
