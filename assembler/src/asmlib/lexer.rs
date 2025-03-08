#![allow(dead_code)]
// TODO: once the lexer is in use, allow the dead_code warning again.

use std::{
    error::Error,
    fmt::Display,
    ops::{Deref, Range},
    sync::OnceLock,
};

use logos::Logos;
use regex::Regex;

#[cfg(test)]
mod input_file_tests;
mod lower;
#[cfg(test)]
mod tests;

type Span = Range<usize>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct Unrecognised<'a> {
    content: &'a str,
    span: Span,
}

impl Display for Unrecognised<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "'{}' is not part of the TX-2 assembler's character set",
            self.content
        )
    }
}

impl Error for Unrecognised<'_> {}

struct LazyRegex {
    once: OnceLock<Regex>,
    pattern: &'static str,
}

impl LazyRegex {
    const fn new(pattern: &'static str) -> Self {
        LazyRegex {
            once: OnceLock::new(),
            pattern,
        }
    }
}

impl Deref for LazyRegex {
    type Target = Regex;

    fn deref(&self) -> &Regex {
        self.once.get_or_init(|| match Regex::new(self.pattern) {
            Ok(r) => r,
            Err(e) => {
                panic!("'{}' is not a valid regular expression: {e}", self.pattern,);
            }
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct NumericLiteral {
    /// The digits comprising the literal. We don't know whether the
    /// base is decimal or octal yet.
    digits: String,
    has_trailing_dot: bool,
}

fn capture_normal_digits(lex: &mut logos::Lexer<Token>) -> NumericLiteral {
    let mut digits: String = String::with_capacity(lex.slice().len());
    let mut has_dot = false;
    for ch in lex.slice().chars() {
        if ch.is_ascii_digit() {
            digits.push(ch);
        } else {
            // Here we take advantage of the fact that however the dot
            // is represented, it is at the end and is the only
            // non-digit.  IOW, we rely on the correctness of the
            // lexer's regexp for this token.
            has_dot = true;
            digits.shrink_to_fit();
            break;
        }
    }
    NumericLiteral {
        digits,
        has_trailing_dot: has_dot,
    }
}

fn capture_subscript_digits(lex: &mut logos::Lexer<Token>) -> NumericLiteral {
    let internal_error = |msg: String| -> ! {
        panic!(
            "internal error: inconsistency in numeric subscript literal decoding for {}: {msg}",
            lex.slice()
        );
    };
    const RX_PARTS: LazyRegex = LazyRegex::new(concat!(
        "(?<digits>",
        "([₀₁₂₃₄₅₆₇₈₉]",
        "|",
        "(@sub_[0-9]@)",
        ")+)",
        "(?<dot>@sub_dot@)?",
    ));
    const RX_DIGIT: LazyRegex = LazyRegex::new(concat!(
        "(?<sub>[₀₁₂₃₄₅₆₇₈₉])",
        "|",
        "(@sub_(?<markup_digit>[0-9])@)",
    ));
    let parts_cap = match (*RX_PARTS).captures(lex.slice()) {
        Some(cap) => cap,
        None => {
            internal_error(format!(
                "token {} does not match parts regex {}",
                lex.slice(),
                RX_PARTS.as_str()
            ));
        }
    };
    dbg!(&parts_cap);
    let digits_part = &parts_cap["digits"];
    let has_trailing_dot: bool = parts_cap.name("dot").is_some();
    let mut digits: String = String::with_capacity(lex.slice().len());
    for cap in (*RX_DIGIT).captures_iter(digits_part) {
        if let Some(got) = cap.name("sub") {
            match got.as_str() {
                "₀" => {
                    digits.push('0');
                }
                "₁" => {
                    digits.push('1');
                }
                "₂" => {
                    digits.push('2');
                }
                "₃" => {
                    digits.push('3');
                }
                "₄" => {
                    digits.push('4');
                }
                "₅" => {
                    digits.push('5');
                }
                "₆" => {
                    digits.push('6');
                }
                "₇" => {
                    digits.push('7');
                }
                "₈" => {
                    digits.push('8');
                }
                "₉" => {
                    digits.push('9');
                }
                other => {
                    internal_error(format!(
                        "did not recognise captured group {other} for group 'sub' in {}",
                        RX_DIGIT.as_str()
                    ));
                }
            }
        } else {
            match cap.name("markup_digit") {
                Some(digit) => {
                    digits.push_str(digit.as_str());
                }
                None => {
                    internal_error(format!(
                        "did not capture a digit from '{digits_part}' with regex '{}'",
                        RX_DIGIT.as_str()
                    ));
                }
            }
        }
    }
    NumericLiteral {
        digits,
        has_trailing_dot,
    }
}

fn capture_superscript_digits(lex: &mut logos::Lexer<Token>) -> NumericLiteral {
    let internal_error = |msg: String| -> ! {
        panic!(
            "internal error: inconsistency in numeric superscript literal decoding for {}: {msg}",
            lex.slice()
        );
    };
    const RX_PARTS: LazyRegex = LazyRegex::new(concat!(
        "(?<digits>",
        "([\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}]",
        "|",
        "(@super_[0-9]@)",
        ")+)",
        "(?<dot>@super_dot@)?",
    ));
    const RX_DIGIT: LazyRegex = LazyRegex::new(concat!(
        "(?<sub>[\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}])",
        "|",
        "(@super_(?<markup_digit>[0-9])@)",
    ));
    let parts_cap = match (*RX_PARTS).captures(lex.slice()) {
        Some(cap) => cap,
        None => {
            internal_error(format!(
                "token {} does not match parts regex {}",
                lex.slice(),
                RX_PARTS.as_str()
            ));
        }
    };
    dbg!(&parts_cap);
    let digits_part = &parts_cap["digits"];
    let has_trailing_dot: bool = parts_cap.name("dot").is_some();
    let mut digits: String = String::with_capacity(lex.slice().len());
    for cap in (*RX_DIGIT).captures_iter(digits_part) {
        if let Some(got) = cap.name("sub") {
            match got.as_str() {
                "\u{2070}" => {
                    digits.push('0');
                }
                "\u{00B9}" => {
                    digits.push('1');
                }
                "\u{00B2}" => {
                    digits.push('2');
                }
                "\u{00B3}" => {
                    digits.push('3');
                }
                "\u{2074}" => {
                    digits.push('4');
                }
                "\u{2075}" => {
                    digits.push('5');
                }
                "\u{2076}" => {
                    digits.push('6');
                }
                "\u{2077}" => {
                    digits.push('7');
                }
                "\u{2078}" => {
                    digits.push('8');
                }
                "\u{2079}" => {
                    digits.push('9');
                }
                other => {
                    internal_error(format!(
                        "did not recognise captured group {other} for group 'sub' in {}",
                        RX_DIGIT.as_str()
                    ));
                }
            }
        } else {
            match cap.name("markup_digit") {
                Some(digit) => {
                    digits.push_str(digit.as_str());
                }
                None => {
                    internal_error(format!(
                        "did not capture a digit from '{digits_part}' with regex '{}'",
                        RX_DIGIT.as_str()
                    ));
                }
            }
        }
    }
    NumericLiteral {
        digits,
        has_trailing_dot,
    }
}

/// The parser consumes these tokens.
#[derive(Debug, PartialEq, Eq, Logos, Clone)]
pub(crate) enum Token {
    LeftBrace,
    RightBrace,
    Newline,

    #[regex("@arr@|->", priority = 20)]
    Arrow,

    #[regex("@hand@|☛", priority = 20)]
    Hand,

    #[token("=")]
    Equals,

    #[token("|")]
    Pipe,

    // Needs to be higher priority than NormalSymexSyllable.
    #[regex("[0-9]+([.]|@dot@)?", capture_normal_digits, priority = 20)]
    NormalDigits(NumericLiteral),

    // Needs to be higher priority than SubscriptSymexSyllable (when that's introduced).
    #[regex(
        "([₀₁₂₃₄₅₆₇₈₉]|(@sub_([0-9])@))+(@sub_dot@)?",
        capture_subscript_digits,
        priority = 20
    )]
    SubscriptDigits(NumericLiteral),

    // Needs to be higher priority than SuperscriptSymexSyllable (when that's introduced).
    #[regex("([\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}]|(@super_([0-9])@))+(@super_dot@)?", capture_superscript_digits, priority = 20)]
    SuperscriptDigits(NumericLiteral),

    // TODO: missing from this are: overbar, square, circle.
    #[regex(
        "([0-9A-ZαβγΔελijknpqtwxyz.'_]|(@(alpha|beta|gamma|delta|eps|lambda)@))+",
        priority = 15
    )]
    NormalSymexSyllable,

    #[token(",")]
    Comma,
}

/// This is the primary lexer (and the only one accessible outside
/// this module).  It delegates the task of keeping track of whether
/// we're in an RC-block to a stateful "lower" lexer.  The "lower"
/// lexer's output is an enum, one of whose variants represents a
/// sequence of characters which we know don't contain an RC-block or
/// a comment.  These sequences are scanned by the "upper" lexer
/// (which is generated by Logos).
#[derive(Debug, Clone)]
pub(crate) struct Lexer<'a> {
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

    fn adjust_span(&self, span: Range<usize>) -> Range<usize> {
        match self.upper.as_ref() {
            None => span,
            Some(upper) => {
                let offset = span.start;
                let upper_span = upper.span();
                dbg!(offset);
                dbg!(&upper_span);
                dbg!((upper_span.start + offset)..(upper_span.end + offset))
            }
        }
    }

    fn span(&self) -> Range<usize> {
        self.adjust_span(self.lower.span())
    }

    fn adjust_token_span(&self, t: Token) -> Token {
        // TODO: remove?
        t
    }

    fn next_upper(upper: &mut logos::Lexer<'a, Token>) -> Option<Result<Token, Unrecognised<'a>>> {
        match upper.next() {
            None => None,
            Some(Ok(token_from_upper)) => Some(Ok(token_from_upper)),
            Some(Err(_)) => Some(Err(Unrecognised {
                content: upper.slice(),
                span: upper.span(),
            })),
        }
    }

    fn spanned(&self) -> SpannedIter<'a> {
        SpannedIter {
            lexer: self.clone(),
        }
    }

    fn get_next(&mut self) -> Option<Result<Token, Unrecognised<'a>>> {
        let mut get_next_without_span_adjustment = || -> Option<Result<Token, Unrecognised<'a>>> {
            use lower::Lexeme;
            if let Some(upper_lexer) = self.upper.as_mut() {
                match Lexer::next_upper(upper_lexer) {
                    Some(r) => {
                        return Some(r);
                    }
                    None => {
                        // We have no more input from the upper lexer,
                        // fetch more from the lower one.
                    }
                }
            }

            // Fetch more text from the lower lexer.
            self.upper = None;
            match self.lower.next() {
                Lexeme::EndOfInput => None,
                Lexeme::Tok(tok) => Some(Ok(tok)),
                // If the lower lexer actually returns Unrecognised, the
                // slice in `content` is likely very short (a single
                // character perhaps) and that is unlikely to be
                // tokenizable.  So the upper lexer will likely also
                // return an error for that text too.
                Lexeme::Text(text)
                | Lexeme::Err(Unrecognised {
                    content: text,
                    span: _,
                }) => {
                    let lexer = logos::Lexer::new(text);
                    self.upper = Some(lexer);
                    Lexer::next_upper(
                        self.upper
                            .as_mut()
                            .expect("the option cannot be empty, we just filled it"),
                    )
                }
            }
        };

        get_next_without_span_adjustment().map(|result| result.map(|t| self.adjust_token_span(t)))
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, Unrecognised<'a>>;

    fn next(&mut self) -> Option<Result<Token, Unrecognised<'a>>> {
        self.get_next()
    }
}

#[derive(Debug, Clone)]
struct SpannedIter<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Iterator for SpannedIter<'a> {
    type Item = Result<(Token, Span), Unrecognised<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lexer.next() {
            Some(Ok(tok)) => Some(Ok((tok, self.lexer.span()))),
            Some(Err(e)) => Some(Err(e)),
            None => None,
        }
    }
}
