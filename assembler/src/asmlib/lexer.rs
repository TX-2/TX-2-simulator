use std::ops::Range;

use logos::Logos;

//#[logos(extras = ExtrasType)]

mod implementation {
    use logos::Logos;

    #[derive(Debug, Logos, PartialEq)]
    pub(super) enum InnerToken {
        #[regex("[*][*][^}\n]*")]
        CommentStart,

        #[token("\n")]
        Newline,

        #[token("{")]
        LeftBrace,

        #[token("}")]
        RightBrace,

        #[regex("[^ \t{}\n]+")]
        Text,

        #[regex("[ \t]+")]
        Spaces,
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Token {
    LeftBrace,
    RightBrace,
    Newline,
    Text,
}

#[derive(Debug)]
struct Lexer<'a> {
    inner: logos::Lexer<'a, implementation::InnerToken>,
    in_comment: bool,
    lbrace_count: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Lexer<'a> {
        let lex = Lexer {
            inner: implementation::InnerToken::lexer(input),
            in_comment: false,
            lbrace_count: 0,
        };
        lex.check_set_up_for_start_of_line();
        lex
    }

    fn span(&self) -> Range<usize> {
        self.inner.span()
    }

    fn check_set_up_for_start_of_line(&self) {
        assert!(!self.in_comment);
        assert_eq!(self.lbrace_count, 0);
    }

    fn next(&mut self) -> Option<Token> {
        use implementation::InnerToken;

        loop {
            let tok = match dbg!(self.inner.next()) {
                None => {
                    return None;
                }
                Some(Err(_)) => {
                    todo!()
                }
                Some(Ok(tok)) => tok,
            };
            match tok {
                InnerToken::Spaces => {
                    // Skip.
                }
                InnerToken::CommentStart => {
                    self.in_comment = true;
                }
                InnerToken::LeftBrace => {
                    if self.in_comment {
                        // Left brace inside a comment is not special,
                        // so we continue skipping the comment text.
                        continue;
                    }
                    self.lbrace_count = self.lbrace_count.checked_add(1).expect(
                        "the number of '{' on one line should be countable without overflow",
                    );
                    return Some(Token::LeftBrace);
                }
                InnerToken::RightBrace => {
                    match self.lbrace_count.checked_sub(1) {
                        None => {
                            if self.in_comment {
                                // Right brace inside a comment, but
                                // there was no previous left brace.
                                // Hence the } doesn't terminate an
                                // RC-block.  So we continue skipping
                                // the comment text.
                                continue;
                            }
                            return Some(Token::RightBrace);
                        }
                        Some(reduced_count) => {
                            self.lbrace_count = reduced_count;
                            self.in_comment = false;
                            return Some(Token::RightBrace);
                        }
                    }
                }
                InnerToken::Newline => {
                    self.lbrace_count = 0;
                    self.in_comment = false;
                    self.check_set_up_for_start_of_line();
                    return Some(Token::Newline);
                }
                InnerToken::Text => {
                    if !self.in_comment {
                        return Some(Token::Text);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan_spans<'a>(input: &'a str) -> Vec<(Token, &'a str)> {
        let mut scanner = Lexer::new(input);
        let mut result = Vec::new();
        while let Some(token) = scanner.next() {
            let fragment: &'a str = &input[scanner.span()];
            result.push((token, fragment));
        }
        result
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(scan_spans(""), Vec::new());
    }

    #[test]
    fn test_balanced_braces() {
        assert_eq!(
            scan_spans("{}"),
            vec![(Token::LeftBrace, "{"), (Token::RightBrace, "}")]
        );
    }

    #[test]
    fn test_comment_without_content() {
        assert_eq!(scan_spans("**"), Vec::new());
    }

    #[test]
    fn test_comment_with_only_newline() {
        assert_eq!(scan_spans("**\n"), vec![(Token::Newline, "\n")]);
    }

    #[test]
    fn test_comment_x() {
        assert_eq!(scan_spans("**X\n"), vec![(Token::Newline, "\n")]);
    }

    #[test]
    fn test_comment_with_unmatched_rbrace() {
        assert_eq!(
            scan_spans("** THIS } {HELLO} IS A } COMMENT\n"),
            vec![(Token::Newline, "\n")]
        );
    }

    #[test]
    fn test_unmatched_rbrace() {
        assert_eq!(
            scan_spans("}\n"),
            vec![(Token::RightBrace, "}"), (Token::Newline, "\n")]
        );
    }
}
