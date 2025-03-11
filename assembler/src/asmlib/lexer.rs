#![allow(dead_code)]
// TODO: once the lexer is in use, allow the dead_code warning again.

use std::{
    error::Error,
    fmt::{Display, Write},
    ops::{Deref, Range},
    sync::OnceLock,
};

use logos::Logos;
use regex::{Captures, Regex};

use super::{
    ast::{elevate, elevate_normal, elevate_sub, elevate_super},
    parser::helpers::{self, Sign},
    state::NumeralMode,
};
use base::{charset::Script, error::StringConversionFailed, Unsigned36Bit};

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
    sign: Option<Sign>,
    /// The digits comprising the literal. We don't know whether the
    /// base is decimal or octal yet.
    digits: String,
    has_trailing_dot: bool,
}

impl Display for NumericLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(sign) = self.sign.as_ref() {
            write!(f, "{}", sign)?;
        }
        f.write_str(self.digits.as_str())?;
        if self.has_trailing_dot {
            f.write_char('·')?;
        }
        Ok(())
    }
}

impl NumericLiteral {
    pub(crate) fn make_num(
        &self,
        mode: &NumeralMode,
    ) -> Result<Unsigned36Bit, StringConversionFailed> {
        helpers::make_num(self.sign, self.digits.as_str(), self.has_trailing_dot, mode)
    }
}

fn capture_glyph_script(lex: &mut logos::Lexer<Token>) -> Script {
    let s = lex.slice();
    if s.starts_with("@sup_") {
        Script::Super
    } else if s.starts_with("@sub_") {
        Script::Sub
    } else {
        Script::Normal
    }
}

fn capture_normal_digits(lex: &mut logos::Lexer<Token>) -> NumericLiteral {
    let mut digits: String = String::with_capacity(lex.slice().len());
    let mut has_trailing_dot = false;
    let mut sign: Option<Sign> = None;
    let internal_error = |msg: String| -> ! {
        panic!(
            "internal error: inconsistency in numeric literal decoding for {}: {msg}",
            lex.slice()
        );
    };
    for ch in lex.slice().chars() {
        match ch {
            '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => {
                digits.push(ch);
            }
            '+' | '-' if sign.is_some() => {
                internal_error("numeric literal has more than one sign symbol".to_string());
            }
            '+' => {
                sign = Some(Sign::Plus);
            }
            '-' => {
                sign = Some(Sign::Minus);
            }
            '·' | '.' | '@' => {
                // Here we take advantage of the fact that however the dot
                // is represented, it is at the end and is the only
                // non-digit.  IOW, we rely on the correctness of the
                // lexer's regexp for this token.
                has_trailing_dot = true;
                digits.shrink_to_fit();
                break;
            }
            other => {
                internal_error(format!("did not expect to see '{other}'"));
            }
        }
    }
    NumericLiteral {
        sign,
        digits,
        has_trailing_dot,
    }
}

fn extract_sign(cap: &Captures) -> Result<Option<Sign>, String> {
    match (cap.name("plus").is_some(), cap.name("minus").is_some()) {
        (false, false) => Ok(None),
        (false, true) => Ok(Some(Sign::Minus)),
        (true, false) => Ok(Some(Sign::Plus)),
        (true, true) => Err(format!(
            "expected to find a single optional leading sign in a numeric literal but found both + and -"
        )),
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
        "((?<plus>\u{208A})|(?<minus>\u{208B}))?",
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
    let sign: Option<Sign> = extract_sign(&parts_cap).expect("sign should be valid if present");
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
        sign,
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
        "((?<plus>\u{207A})|(?<minus>\u{207B}))?",
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
    let sign: Option<Sign> = extract_sign(&parts_cap).expect("sign should be valid if present");
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
        sign,
        digits,
        has_trailing_dot,
    }
}

fn capture_name(lex: &mut logos::Lexer<Token>) -> String {
    const RX_GREEK_GLYPHS: LazyRegex =
        LazyRegex::new("(@(?<glyph>alpha|beta|gamma|delta|eps|lambda)@|[^@]+");
    let slice = lex.slice();
    let mut name: String = String::with_capacity(slice.len());
    for cap in (*RX_GREEK_GLYPHS).captures_iter(slice) {
        if let Some(got) = cap.name("glyph") {
            let glyph_name = got.as_str();
            match helpers::at_glyph(Script::Normal, glyph_name) {
                None => {
                    panic!("lexer matched glyph {glyph_name} but this is not a known glyph");
                }
                Some(representation) => {
                    name.push(representation);
                }
            }
        } else if let Some(m) = cap.get(0) {
            name.push_str(m.as_str());
        } else {
            // If there is a match, cap.get(0) is never None (per the
            // Regex crate documentation).
            unreachable!()
        }
    }
    name
}

/// The parser consumes these tokens.
#[derive(Debug, PartialEq, Eq, Logos, Clone)]
pub(crate) enum Token {
    // In order for the parser to recover from tokenization errors, we
    // need to be able to emit an error token.
    Error(String),

    LeftBrace,
    RightBrace,
    Newline,

    /// The parser currently only handled parenthesised expressions in
    /// normal script.
    #[token("(")]
    LeftParen,

    /// The parser currently only handled parenthesised expressions in
    /// normal script.
    #[token(")")]
    RightParen,

    /// Accept either 'h' or ':' signalling the hold bit (of the
    /// instruction word) should be set.  The documentation seems to
    /// use both, though perhaps ':' is the older usage.
    ///
    /// While h is indeed a letter, it is not one of the letters which
    /// can form part of a symex.  See the TX-2 Users Handbook,
    /// section 6-3.2, "RULES FOR SYMEX FORMATION".
    #[regex("h|:")]
    Hold,

    #[regex("\u{0305}h|ℏ|@hbar@")] // U+0305 is combining overline.
    NotHold,

    #[regex("@arr@|->", priority = 20)]
    Arrow,

    #[regex("@hand@|☛", priority = 20)]
    Hand,

    #[regex("[.·]|@dot@")]
    Dot,

    #[regex(
        "#|@hash@|@sub_hash@|@super_hash@",
        capture_glyph_script,
        priority = 20
    )]
    Hash(Script),

    #[token("=")]
    Equals,

    #[token("|")]
    Pipe,

    #[regex("⊃|@sup@")]
    ProperSuperset,

    #[regex("≡|@hamb@")]
    IdenticalTo,

    #[token("~")]
    Tilde,

    #[token("<")]
    LessThan,

    #[token(">")]
    GreaterThan,

    #[token("∩")]
    Intersection,

    #[token("∪")]
    Union,

    /// Solidus is often called "slash" but people often confuse slash
    /// and backslash.  So we don't call it either.
    #[token("/")]
    Solidus,

    #[token("+")]
    Plus,

    #[token("-")]
    Minus,

    #[regex("×|@times@")]
    Times,

    #[token("∨")]
    LogicalOr,

    #[token("∧")]
    LogicalAnd,

    // Needs to be higher priority than NormalSymexSyllable.
    #[regex("[-+]?[0-9]+([.·]|@dot@)?", capture_normal_digits, priority = 20)]
    NormalDigits(NumericLiteral),

    // Needs to be higher priority than SubscriptSymexSyllable (when that's introduced).
    #[regex(
        "([₋₊]?[₀₁₂₃₄₅₆₇₈₉]|(@sub_([0-9])@))+(@sub_dot@)?",
        capture_subscript_digits,
        priority = 20
    )]
    SubscriptDigits(NumericLiteral),

    // Needs to be higher priority than SuperscriptSymexSyllable (when that's introduced).
    #[regex("([\u{207A}\u{207B}])?([\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}]|(@super_([0-9])@))+(@super_dot@)?", capture_superscript_digits, priority = 20)]
    SuperscriptDigits(NumericLiteral),

    // TODO: missing from this are: overbar, square, circle.
    /// The rules concerning which characters can be part of a symex
    /// are given in the TX-2 Users Handbook, section 6-3.2, "RULES
    /// FOR SYMEX FORMATION".
    #[regex(
        "([0-9A-ZαβγΔελijknpqtwxyz.'_]|(@(alpha|beta|gamma|delta|eps|lambda)@))+",
        capture_name,
        priority = 15
    )]
    NormalSymexSyllable(String),

    #[token(",")]
    Comma,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Error(msg) => write!(f, "(error: {msg})"),
            Token::LeftBrace => f.write_char('{'),
            Token::RightBrace => f.write_char('}'),
            Token::Newline => f.write_char('\n'),
            Token::LeftParen => f.write_char('('),
            Token::RightParen => f.write_char(')'),
            Token::Hold => f.write_char('h'),
            Token::NotHold => f.write_char('ℏ'),
            Token::Arrow => f.write_str("->"),
            Token::Hand => f.write_char('☛'),
            Token::Dot => f.write_char('·'),
            Token::Hash(script) => {
                let el = elevate(*script, "#");
                write!(f, "{el}")
            }
            Token::Equals => f.write_char('='),
            Token::Pipe => f.write_char('|'),
            Token::ProperSuperset => f.write_char('⊃'),
            Token::IdenticalTo => f.write_char('≡'),
            Token::Tilde => f.write_char('~'),
            Token::LessThan => f.write_char('<'),
            Token::GreaterThan => f.write_char('>'),
            Token::Intersection => f.write_char('∩'),
            Token::Union => f.write_char('∪'),
            Token::Solidus => f.write_char('/'),
            Token::Plus => f.write_char('+'),
            Token::Minus => f.write_char('-'),
            Token::Times => f.write_char('×'),
            Token::LogicalOr => f.write_char('∨'),
            Token::LogicalAnd => f.write_char('∧'),
            Token::NormalDigits(numeric_literal) => {
                write!(f, "{}", elevate_normal(numeric_literal.to_string()))
            }
            Token::SubscriptDigits(numeric_literal) => {
                write!(f, "{}", elevate_sub(numeric_literal.to_string()))
            }
            Token::SuperscriptDigits(numeric_literal) => {
                write!(f, "{}", elevate_super(numeric_literal.to_string()))
            }
            Token::NormalSymexSyllable(s) => f.write_str(s),
            Token::Comma => f.write_char(','),
        }
    }
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

    // TODO: now that we return an error token to report a problem, We
    // no longer need the return type to be Option<Result<...>>.
    fn next_upper(upper: &mut logos::Lexer<'a, Token>) -> Option<Result<Token, Unrecognised<'a>>> {
        match upper.next() {
            None => None,
            Some(Ok(token_from_upper)) => Some(Ok(token_from_upper)),
            Some(Err(_)) => {
                // Instead of returning Err we return an error token
                // in order to allow the parser to attempt recovery.
                let msg: String = Unrecognised {
                    content: upper.slice(),
                    span: upper.span(),
                }
                .to_string();
                Some(Ok(Token::Error(msg)))
            }
        }
    }

    pub(crate) fn spanned(&self) -> SpannedIter<'a> {
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
    type Item = (Result<Token, Unrecognised<'a>>, Span);

    fn next(&mut self) -> Option<Self::Item> {
        let span = self.lexer.span();
        match self.lexer.next() {
            Some(result) => Some((result, span)),
            None => None,
        }
    }
}
