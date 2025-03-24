#![allow(dead_code)]
// TODO: once the lexer is in use, allow the dead_code warning again.

use std::{
    fmt::{Display, Write},
    ops::Range,
};

use logos::Logos;
use regex::{Captures, Regex};

use super::{
    glyph::{
        self, elevate, elevate_normal, elevate_sub, elevate_super, glyph_of_char, unsubscript_char,
        unsuperscript_char, Unrecognised,
    },
    parser::helpers::{self, Sign},
    state::NumeralMode,
};
use base::{
    charset::{subscript_char, superscript_char, Script},
    error::StringConversionFailed,
    Unsigned36Bit,
};

#[cfg(test)]
mod input_file_tests;
mod lower;
mod rx;
#[cfg(test)]
mod tests;

use rx::LazyRegex;
type Span = Range<usize>;

pub(crate) const DOT_CHAR: char = '·';
pub(crate) const DOT_STR: &str = "·";

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct NumericLiteral {
    /// The digits comprising the literal. We don't know whether the
    /// base is decimal or octal yet.
    digits: String,
    has_trailing_dot: bool,
}

impl Display for NumericLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.digits.as_str())?;
        if self.has_trailing_dot {
            f.write_char(DOT_CHAR)?;
        }
        Ok(())
    }
}

impl NumericLiteral {
    pub(crate) fn make_num(
        &self,
        maybe_sign: Option<Sign>,
        mode: &NumeralMode,
    ) -> Result<Unsigned36Bit, StringConversionFailed> {
        helpers::make_num(
            maybe_sign,
            self.digits.as_str(),
            self.has_trailing_dot,
            mode,
        )
    }

    pub(crate) fn append_digits_of_literal(&mut self, other: NumericLiteral) {
        assert!(!other.has_trailing_dot);
        self.digits.extend(other.digits.chars());
    }

    pub(crate) fn has_trailing_dot(&self) -> bool {
        self.has_trailing_dot
    }

    pub(crate) fn take_digits(self) -> String {
        self.digits
    }
}

fn determine_string_script(s: &str) -> Result<Script, ()> {
    fn combine(first: Option<Script>, second: Script) -> Result<Script, ()> {
        match first {
            Some(f) if f != second => Err(()),
            _ => Ok(second),
        }
    }
    let mut decision: Option<Script> = None;
    for ch in s.chars() {
        match glyph_of_char(ch) {
            Ok(elevated) => {
                decision = Some(combine(decision, elevated.script())?);
            }
            Err(_) => {
                return Err(());
            }
        };
    }
    match decision {
        Some(d) => Ok(d),
        None => Err(()), // e.g. empty string
    }
}

fn capture_glyph_script(lex: &mut logos::Lexer<Token>) -> Script {
    let s = lex.slice();
    if s.starts_with("@sup_") {
        Script::Super
    } else if s.starts_with("@sub_") {
        Script::Sub
    } else if s.starts_with("@") {
        Script::Normal
    } else {
        // It's not a glyph.  So we need to figure it out by examining
        // the string.
        match determine_string_script(s) {
            Ok(script) => script,
            Err(_) => {
                panic!("token matching should only include characters with a consistent script, but '{s}' wasn't like that");
            }
        }
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
            DOT_CHAR | '.' | '@' => {
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
        digits,
        has_trailing_dot,
    }
}

fn extract_sign(cap: &Captures) -> Result<Option<Sign>, String> {
    match (cap.name("plus").is_some(), cap.name("minus").is_some()) {
        (false, false) => Ok(None),
        (false, true) => Ok(Some(Sign::Minus)),
        (true, false) => Ok(Some(Sign::Plus)),
        (true, true) => Err(
            "expected to find a single optional leading sign in a numeric literal but found both + and -"
                .to_string()),
    }
}

fn capture_subscript_digits(lex: &mut logos::Lexer<Token>) -> NumericLiteral {
    let internal_error = |msg: String| -> ! {
        panic!(
            "internal error: inconsistency in numeric subscript literal decoding for {}: {msg}",
            lex.slice()
        );
    };
    static CAPTURE_SUBSCRIPT_DIGITS_RX_PARTS: LazyRegex = LazyRegex::new(concat!(
        "((?<plus>\u{208A})|(?<minus>\u{208B}))?",
        "(?<digits>",
        "([₀₁₂₃₄₅₆₇₈₉]",
        "|",
        "(@sub_[0-9]@)",
        ")+)",
        "(?<dot>@sub_dot@)?",
    ));
    static RX_DIGIT: LazyRegex = LazyRegex::new(concat!(
        "(?<sub>[₀₁₂₃₄₅₆₇₈₉])",
        "|",
        "(@sub_(?<markup_digit>[0-9])@)",
    ));
    let parts_cap = match (*CAPTURE_SUBSCRIPT_DIGITS_RX_PARTS).captures(lex.slice()) {
        Some(cap) => cap,
        None => {
            internal_error(format!(
                "token {} does not match parts regex {}",
                lex.slice(),
                CAPTURE_SUBSCRIPT_DIGITS_RX_PARTS.as_str()
            ));
        }
    };

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
    static RX_PARTS: LazyRegex = LazyRegex::new(concat!(
        "((?<plus>\u{207A})|(?<minus>\u{207B}))?",
        "(?<digits>",
        "([\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}]",
        "|",
        "(@sup_[0-9]@)",
        ")+)",
        "(?<dot>@sup_dot@)?",
    ));
    static RX_DIGIT: LazyRegex = LazyRegex::new(concat!(
        "(?<sup>[\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}])",
        "|",
        "(@sup_(?<markup_digit>[0-9])@)",
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
    let digits_part = &parts_cap["digits"];
    let has_trailing_dot: bool = parts_cap.name("dot").is_some();
    let mut digits: String = String::with_capacity(lex.slice().len());
    for cap in (*RX_DIGIT).captures_iter(digits_part) {
        if let Some(got) = cap.name("sup") {
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

fn capture_name(lex: &mut logos::Lexer<Token>) -> String {
    static RX_GREEK_GLYPHS: LazyRegex =
        LazyRegex::new("(@(?<glyph>alpha|beta|gamma|delta|eps|lambda|apostrophe)@|[^@])+");
    let slice = lex.slice();
    let mut name: String = String::with_capacity(slice.len());
    for cap in (*RX_GREEK_GLYPHS).captures_iter(slice) {
        if let Some(got) = cap.name("glyph") {
            let glyph_name = got.as_str();
            match glyph::at_glyph(Script::Normal, glyph_name) {
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

fn decode_glyphs_by_regex(tokname: &'static str, rx: &Regex, text: &str, script: Script) -> String {
    fn identity_char(ch: char) -> Option<char> {
        Some(ch)
    }

    let mut name: String = String::with_capacity(text.len());
    let transformer = match script {
        Script::Sub => unsubscript_char,
        Script::Super => unsuperscript_char,
        Script::Normal => identity_char,
    };

    let mut tail = text;
    while let Some(cap) = rx.captures(tail) {
        let m0 = cap.get(0).expect("regex capture group 0 always succeeds");
        let prefix = &tail[0..(m0.start())];
        if !prefix.is_empty() {
            panic!(
                "while scanning token '{tokname}', failed to decode '{tail}' in script {script:?}: the initial prefix '{prefix}' of it did not match {rx}; original input was '{text}'"
            );
        }

        if let Some(got) = cap.name("glyphname") {
            let glyph_name = got.as_str();
            match glyph::at_glyph(Script::Normal, glyph_name) {
                None => {
                    panic!("lexer matched glyph {glyph_name} but this is not a known glyph");
                }
                Some(representation) => {
                    name.push(representation);
                }
            }
        } else if let Some(m) = cap.get(0) {
            let fragment = m.as_str();
            for (i, ch) in fragment.chars().enumerate() {
                match transformer(ch) {
                    Some(ch) => {
                        name.push(ch);
                    }
                    None => {
                        panic!("while decoding '{text}' as token {tokname}, the lexer accepts '{ch}' at offset {i} in '{fragment}' but the lexer's decoder doesn't know what to do with it (so the lexer token matching rule is probably wrong)");
                    }
                }
            }
        } else {
            // If there is a match, cap.get(0) is never None (per the
            // Regex crate documentation).
            unreachable!()
        }
        tail = &tail[(m0.end())..];
    }
    if !tail.is_empty() {
        panic!("failed to decode '{tail}': it did not match {rx}");
    } else {
        name
    }
}

fn capture_possible_subscript_glyphs(lex: &mut logos::Lexer<Token>) -> String {
    static RX_GLYPHS: LazyRegex = LazyRegex::new("(@sub_(?<glyphname>[^@]+)@)|(?<asis>[^@])");
    decode_glyphs_by_regex(
        "SubscriptSymexSyllable",
        &RX_GLYPHS,
        lex.slice(),
        Script::Sub,
    )
}

fn capture_possible_superscript_glyphs(lex: &mut logos::Lexer<Token>) -> String {
    static RX_GLYPHS: LazyRegex = LazyRegex::new("(@sup_(?<glyphname>[^@]+)@)|(?<asis>[^@])");
    decode_glyphs_by_regex(
        "SuperscriptSymexSyllable",
        &RX_GLYPHS,
        lex.slice(),
        Script::Super,
    )
}

fn capture_possible_normal_glyphs(lex: &mut logos::Lexer<Token>) -> String {
    static RX_GLYPHS: LazyRegex = LazyRegex::new("(@(?<glyphname>[^@]+)@)|(?<asis>[^@])");
    decode_glyphs_by_regex(
        "NormalSymexSyllable",
        &RX_GLYPHS,
        lex.slice(),
        Script::Normal,
    )
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
    #[regex(r"\(|@lparen@|@sub_lparen@|@sup_lparen@", capture_glyph_script)]
    LeftParen(Script),

    /// The parser currently only handled parenthesised expressions in
    /// normal script.
    #[regex(r"\)|@rparen@|@sub_rparen@|@sup_rparen@", capture_glyph_script)]
    RightParen(Script),

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

    #[regex("@arr@|->|\u{2192}", priority = 20)]
    Arrow,

    #[regex("@hand@|☛", priority = 20)]
    Hand,

    #[regex("#|@hash@|@sub_hash@|@sup_hash@", capture_glyph_script, priority = 20)]
    Hash(Script),

    #[token("=")]
    Equals,

    /// Asterisk is used quite heavily (indicating deferred addressing)
    /// but while the TX-2 supports superscript and subscript
    /// asterisks, they don't seem to be used.  They are not valid as
    /// part of a symex (see User handbook, section 6-2.3) and are not
    /// macro terminators (6-4.5).  However, they are valid as part of
    /// a superposed character sequence making up a compound-character
    /// macro name.
    #[token("*")]
    Asterisk,

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

    #[regex("[₊+⁺]|@plus@|@sub_plus@|@sup_plus@", capture_glyph_script)]
    Plus(Script),

    #[regex("[-₋⁻]|@minus@|@sub_minus@|@sup_minus@", capture_glyph_script)]
    Minus(Script),

    #[regex("×|@times@")]
    Times,

    #[regex("∨|@sub_or@|@or@|@sup_or@", capture_glyph_script)]
    LogicalOr(Script),

    #[regex("∧|@sub_and|@and@|@sup_and@", capture_glyph_script)]
    LogicalAnd(Script),

    // Needs to be higher priority than NormalSymexSyllable.  If you
    // change the representation of the dot in the token definition,
    // please also change both DOT_CHAR and the definition of the Dot
    // token.  Any unary "-" is handled in the parser.
    #[regex("[0-9]+([.·]|@dot@)?", capture_normal_digits, priority = 20)]
    NormalDigits(NumericLiteral),

    // Needs to be higher priority than SubscriptSymexSyllable.
    // Any unary "-" is handled in the parser.
    #[regex(
        "([₀₁₂₃₄₅₆₇₈₉]|(@sub_([0-9])@))+(@sub_dot@)?",
        capture_subscript_digits,
        priority = 20
    )]
    SubscriptDigits(NumericLiteral),

    // Needs to be higher priority than SuperscriptSymexSyllable.
    // Any unary "-" is handled in the parser.
    #[regex("([\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}]|(@sup_([0-9])@))+(@sup_dot@)?", capture_superscript_digits, priority = 20)]
    SuperscriptDigits(NumericLiteral),

    // TODO: missing from this are: overbar, square, circle.
    /// The rules concerning which characters can be part of a symex
    /// are given in the TX-2 Users Handbook, section 6-3.2, "RULES
    /// FOR SYMEX FORMATION".
    ///
    /// We so not accept dot as part of this token becuase it behaves
    /// differently in some circumstances (it is a macro terminator).
    /// However it is part of a valid symex also, and so we will need
    /// to parse it as such.
    #[regex(
        "([0-9A-ZαβγΔελijknpqtwxyz'_]|(@(alpha|beta|gamma|delta|eps|lambda|apostrophe)@))+",
        capture_possible_normal_glyphs,
        priority = 15
    )]
    NormalSymexSyllable(String),

    // No support for superscript apostrophe, underscore.
    #[regex(
        "([ᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁⱽᵂ⁰¹²³⁴⁵⁶⁷⁸⁹ⁱʲᵏⁿᵖᵗʷˣʸᶻ]|ꟲ|ꟳ|ꟴ|(@sup_([0-9A-Zijknpqtwxyz]|alpha|beta|gamma|delta|eps|lambda|apostrophe)@))+",
        capture_possible_superscript_glyphs,
        priority = 15
    )]
    SuperscriptSymexSyllable(String),

    // No support for superscript apostrophe, underscore.
    #[regex(
        "([₀₁₂₃₄₅₆₇₈₉]|(@sub_([0-9A-Zijknpqtwxyz]|alpha|beta|gamma|delta|eps|lambda|apostrophe)@))+",
        capture_possible_subscript_glyphs,
        priority = 15
    )]
    SubscriptSymexSyllable(String),

    // If change the representation of the dot in the token
    // definition, please also change DOT_CHAR.
    #[regex("[.·̇]|@sub_dot@|@sup_dot@|@dot@", capture_glyph_script, priority = 13)]
    Dot(Script),

    #[token(",")]
    Comma,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut write_elevated = |script: &Script, s: &str| -> std::fmt::Result {
            let el = elevate(*script, s);
            write!(f, "{el}")
        };

        match self {
            Token::Error(msg) => write!(f, "(error: {msg})"),
            Token::LeftBrace => f.write_char('{'),
            Token::RightBrace => f.write_char('}'),
            Token::Newline => f.write_char('\n'),
            Token::LeftParen(script) => write_elevated(script, "("),
            Token::RightParen(script) => write_elevated(script, ")"),
            Token::Hold => f.write_char('h'),
            Token::NotHold => f.write_char('ℏ'),
            Token::Arrow => f.write_str("->"),
            Token::Hand => f.write_char('☛'),
            Token::Asterisk => f.write_char('*'),
            Token::Dot(script) => write_elevated(script, DOT_STR),
            Token::Hash(script) => write_elevated(script, "#"),
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
            Token::Plus(script) => write_elevated(script, "+"),
            Token::Minus(script) => write_elevated(script, "-"),
            Token::Times => f.write_char('×'),
            Token::LogicalOr(script) => write_elevated(script, "∨"),
            Token::LogicalAnd(script) => write_elevated(script, "∧"),
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
            Token::SuperscriptSymexSyllable(s) => {
                for ch in s.chars() {
                    match superscript_char(ch) {
                        Ok(sup_ch) => f.write_char(sup_ch),
                        Err(_) => match ch {
                            'α' => f.write_str("@sup_alpha@"),
                            'β' => f.write_str("@sup_beta@"),
                            'γ' => f.write_str("@sup_gamma@"),
                            'Δ' => f.write_str("@sup_delta@"),
                            'ε' => f.write_str("@sup_eps@"),
                            'λ' => f.write_str("@sup_lambda@"),
                            _ => write!(f, "@sup_{ch}@"),
                        },
                    }?;
                }
                Ok(())
            }
            Token::SubscriptSymexSyllable(s) => {
                for ch in s.chars() {
                    match subscript_char(ch) {
                        Ok(sup_ch) => f.write_char(sup_ch),
                        Err(_) => match ch {
                            'α' => f.write_str("@sub_alpha@"),
                            'β' => f.write_str("@sub_beta@"),
                            'γ' => f.write_str("@sub_gamma@"),
                            'Δ' => f.write_str("@sub_delta@"),
                            'ε' => f.write_str("@sub_eps@"),
                            'λ' => f.write_str("@sub_lambda@"),
                            _ => write!(f, "@sub_{ch}@"),
                        },
                    }?;
                }
                Ok(())
            }
            Token::Comma => f.write_char(','),
        }
    }
}

//ub(crate) use lexer_impl_old::*;
pub(crate) use lexer_impl_old::*;
pub(crate) type Lexer<'a> = OldLexer<'a>;

mod lexer_impl_old {
    use std::ops::Range;

    use super::lower;
    use super::Span;
    use super::Token;
    use super::Unrecognised;

    /// This is the primary lexer (and the only one accessible outside
    /// this module).  It delegates the task of keeping track of whether
    /// we're in an RC-block to a stateful "lower" lexer.  The "lower"
    /// lexer's output is an enum, one of whose variants represents a
    /// sequence of characters which we know don't contain an RC-block or
    /// a comment.  These sequences are scanned by the "upper" lexer
    /// (which is generated by Logos).
    #[derive(Debug, Clone)]
    pub(crate) struct OldLexer<'a> {
        lower: lower::LowerLexer<'a>,
        upper: Option<logos::Lexer<'a, Token>>,
    }
    impl<'a> OldLexer<'a> {
        pub(crate) fn new(input: &'a str) -> OldLexer<'a> {
            OldLexer {
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
                    (upper_span.start + offset)..(upper_span.end + offset)
                }
            }
        }

        pub(crate) fn span(&self) -> Range<usize> {
            self.adjust_span(self.lower.span())
        }

        // TODO: now that we return an error token to report a problem, We
        // no longer need the return type to be Option<Result<...>>.
        fn next_upper(upper: &mut logos::Lexer<'a, Token>) -> Option<Result<Token, Unrecognised>> {
            match upper.next() {
                None => None,
                Some(Ok(token_from_upper)) => Some(Ok(token_from_upper)),
                Some(Err(())) => {
                    // Instead of returning Err we return an error token
                    // in order to allow the parser to attempt recovery.
                    let error = super::Unrecognised::InvalidChar(
                        upper
                            .slice()
                            .chars()
                            .next()
                            .expect("for the input to be invalid it has to be nonempty"),
                    );
                    Some(Ok(Token::Error(error.to_string())))
                }
            }
        }

        pub(crate) fn spanned(&self) -> SpannedIter<'a> {
            let lexer: OldLexer<'a> = self.clone();
            SpannedIter::new(lexer)
        }

        fn get_next(&mut self) -> Option<Result<Token, Unrecognised>> {
            let mut get_next_without_span_adjustment = || -> Option<Result<Token, Unrecognised>> {
                use lower::Lexeme;
                if let Some(upper_lexer) = self.upper.as_mut() {
                    match OldLexer::next_upper(upper_lexer) {
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
                    Lexeme::Text(text) => {
                        let lexer = logos::Lexer::new(text);
                        self.upper = Some(lexer);
                        OldLexer::next_upper(
                            self.upper
                                .as_mut()
                                .expect("the option cannot be empty, we just filled it"),
                        )
                    }
                    Lexeme::Err(e) => Some(Err(e)),
                }
            };

            get_next_without_span_adjustment()
        }
    }

    impl<'a> Iterator for OldLexer<'a> {
        type Item = Result<Token, Unrecognised>;

        fn next(&mut self) -> Option<Result<Token, Unrecognised>> {
            self.get_next()
        }
    }

    #[derive(Debug, Clone)]
    pub(crate) struct SpannedIter<'a> {
        lexer: OldLexer<'a>,
    }

    impl<'a> SpannedIter<'a> {
        pub(crate) fn new(lexer: OldLexer<'a>) -> SpannedIter<'a> {
            SpannedIter { lexer }
        }
    }

    impl<'a> Iterator for SpannedIter<'a> {
        type Item = (Result<Token, Unrecognised>, Span);

        fn next(&mut self) -> Option<Self::Item> {
            let token = self.lexer.next();
            token.map(|t| (t, self.lexer.span()))
        }
    }
}

mod lexer_impl_new {
    use super::glyph::{glyph_from_name, glyph_of_char, Elevated, Glyph, GlyphShape, Unrecognised};
    use super::{NumericLiteral, DOT_CHAR};
    use base::charset::Script;
    use std::iter::Enumerate;
    use std::ops::Range;
    use std::str::Chars;

    use super::{Span, Token};

    #[derive(Debug, Clone)]
    struct SpannedToken {
        tok: Token,
        span: Span,
    }

    #[derive(Debug, Clone)]
    struct GlyphRecognizer<'a> {
        it: Enumerate<Chars<'a>>,
        pos: usize,
        glyph_start: usize,
    }

    impl<'a> GlyphRecognizer<'a> {
        fn new(input: &'a str) -> GlyphRecognizer<'a> {
            Self {
                it: input.chars().enumerate(),
                pos: 0,
                glyph_start: 0,
            }
        }

        fn get_next_char(&mut self) -> Option<char> {
            match self.it.next() {
                None => None,
                Some((i, ch)) => {
                    self.pos = i;
                    Some(ch)
                }
            }
        }

        fn span(&self) -> Span {
            self.glyph_start..(self.pos + 1)
        }

        fn next_named_glyph(&mut self) -> Option<Result<Elevated<&'static Glyph>, Unrecognised>> {
            let mut name: String = String::with_capacity(10);
            let mut got_anything = false;
            loop {
                match self.get_next_char() {
                    Some(ch) => {
                        got_anything = true;
                        if ch == '@' {
                            break;
                        } else {
                            name.push(ch);
                        }
                    }
                    None => {
                        break;
                    }
                }
            }
            // If the input was @@, (that is, the glyph name is
            // zero-length) name is empty but got_anything is
            // (correctly) true.
            if got_anything {
                Some(match glyph_from_name(name.as_str()) {
                    Some(g) => Ok(g),
                    None => Err(Unrecognised::UnrecognisedGlyph(name)),
                })
            } else {
                None
            }
        }
    }

    impl<'a> Iterator for GlyphRecognizer<'a> {
        type Item = Result<Elevated<&'static Glyph>, Unrecognised>;

        fn next(&mut self) -> Option<Self::Item> {
            let ch = self.get_next_char()?;
            self.glyph_start = self.pos;
            match ch {
                '@' => match self.next_named_glyph() {
                    None => {
                        // There actually was input, but it was only a
                        // single '@'.  That is not in the Lincoln
                        // Writer character set.
                        Some(Err(Unrecognised::InvalidChar('@')))
                    }
                    something => something,
                },
                ch => Some(glyph_of_char(ch)),
            }
        }
    }

    #[test]
    fn test_glyph_recognizer_next() {
        let mut gr = GlyphRecognizer::new("W");
        match gr.next() {
            Some(Ok(elev)) => {
                assert_eq!(elev.script(), Script::Normal);
                assert_eq!(elev.get().name, "W");
            }
            bad => {
                panic!("glyph should not have been recognised as {bad:?}");
            }
        }
        assert_eq!(gr.next(), None);
    }

    fn build_numeric_literal(
        has_trailing_dot: bool,
        (digits, script): (String, Script),
    ) -> super::Token {
        let mapper = match script {
            Script::Normal => super::Token::NormalDigits,
            Script::Sub => super::Token::SubscriptDigits,
            Script::Super => super::Token::SuperscriptDigits,
        };
        mapper(NumericLiteral {
            digits,
            has_trailing_dot,
        })
    }

    #[cfg(test)]
    fn scan_string<'a>(s: &'a str) -> Vec<Result<Elevated<&'static Glyph>, Unrecognised>> {
        GlyphRecognizer::new(s).collect()
    }

    #[cfg(test)]
    fn assert_glyph(
        got: Elevated<&'static Glyph>,
        expected_shape: GlyphShape,
        expected_script: Script,
    ) {
        assert_eq!(got.script(), expected_script, "wrong script for {got:?}");
        assert_eq!(got.get().shape(), expected_shape, "wrong shape for {got:?}");
    }

    #[test]
    fn test_glyph_scanning() {
        let mut scanner = GlyphRecognizer::new("hs@sub_eps@@hamb@@sup_add@@nosuch@ ");
        // h is in the Lincoln Writer character set.
        assert_glyph(
            scanner.next().expect("input").expect("in character set"),
            GlyphShape::h,
            Script::Normal,
        );
        // s is not in the Lincoln Writer character set.
        assert_eq!(scanner.next(), Some(Err(Unrecognised::InvalidChar('s'))),);
        assert_glyph(
            scanner.next().expect("input").expect("in character set"),
            GlyphShape::Epsilon,
            Script::Sub,
        );
        assert_glyph(
            scanner.next().expect("input").expect("in character set"),
            GlyphShape::IdenticalTo,
            Script::Normal,
        );
        assert_glyph(
            scanner.next().expect("input").expect("in character set"),
            GlyphShape::Add,
            Script::Super,
        );
        assert_eq!(
            scanner.next(),
            Some(Err(Unrecognised::UnrecognisedGlyph("nosuch".to_string())))
        );
        assert_glyph(
            scanner.next().expect("input").expect("in character set"),
            GlyphShape::Space,
            Script::Normal,
        );
        assert_eq!(scanner.next(), None);
        // Verify that detection of end-of-input is sticky.
        assert_eq!(scanner.next(), None);
    }

    fn tokenise_single_glyph(g: Elevated<&'static Glyph>) -> Option<super::Token> {
        use super::Token;
        let script: Script = g.script();

        let make_num = |ch: char| {
            let literal = NumericLiteral {
                digits: {
                    let mut s = String::with_capacity(12);
                    s.push(ch);
                    s
                },
                has_trailing_dot: false,
            };
            let f = match script {
                Script::Super => super::Token::SuperscriptDigits,
                Script::Normal => super::Token::NormalDigits,
                Script::Sub => super::Token::SubscriptDigits,
            };
            f(literal)
        };
        let make_symex = || -> Option<Token> {
            let f = match script {
                Script::Super => Token::SuperscriptSymexSyllable,
                Script::Normal => Token::NormalSymexSyllable,
                Script::Sub => Token::SubscriptSymexSyllable,
            };
            // The symex token always gives the characters in normal
            // script.  The superscript/subscript information is
            // carried in the token variant
            // (e.g. SuperscriptSymexsyllable).
            let name: String = g.get().get_char(Script::Normal).iter().collect();
            // We do not use name.len() here because the number of
            // bytes in the name is not relevant, only the number of
            // Unicode code points.
            match name.chars().count() {
                0 => {
                    panic!("incoming token '{g:?}' was assigned as part of a symex syllable, but we don't have a character for it in script {script:?}");
                }
                1 => (),
                n => {
                    panic!("incoming token '{g:?}' was assigned as part of a symex syllable, but the resuting initial token body unexpectedly has more than one character (specifically, {n}): {name:?}");
                }
            }
            Some(f(name))
        };
        let only_normal = |t: Token| -> Option<Token> {
            match script {
                Script::Super | Script::Sub => {
                    unimplemented!(
                        "only normal script is supported for {t:?} but input is {script:?}"
                    );
                }
                Script::Normal => Some(t),
            }
        };

        match g.get().shape() {
            GlyphShape::Space | GlyphShape::Tab => None,
            GlyphShape::Digit0 => Some(make_num('0')),
            GlyphShape::Digit1 => Some(make_num('1')),
            GlyphShape::Digit2 => Some(make_num('2')),
            GlyphShape::Digit3 => Some(make_num('3')),
            GlyphShape::Digit4 => Some(make_num('4')),
            GlyphShape::Digit5 => Some(make_num('5')),
            GlyphShape::Digit6 => Some(make_num('6')),
            GlyphShape::Digit7 => Some(make_num('7')),
            GlyphShape::Digit8 => Some(make_num('8')),
            GlyphShape::Digit9 => Some(make_num('9')),
            GlyphShape::Underscore
            | GlyphShape::Circle
            | GlyphShape::A
            | GlyphShape::B
            | GlyphShape::C
            | GlyphShape::D
            | GlyphShape::E
            | GlyphShape::F
            | GlyphShape::G
            | GlyphShape::H
            | GlyphShape::I
            | GlyphShape::J
            | GlyphShape::K
            | GlyphShape::L
            | GlyphShape::M
            | GlyphShape::N
            | GlyphShape::O
            | GlyphShape::P
            | GlyphShape::Q
            | GlyphShape::R
            | GlyphShape::S
            | GlyphShape::T
            | GlyphShape::U
            | GlyphShape::V
            | GlyphShape::W
            | GlyphShape::X
            | GlyphShape::Y
            | GlyphShape::Z => make_symex(),
            GlyphShape::LeftParen => Some(Token::LeftParen(script)),
            GlyphShape::RightParen => Some(Token::RightParen(script)),
            GlyphShape::Add => Some(Token::Plus(script)),
            GlyphShape::Minus => Some(Token::Minus(script)),
            GlyphShape::Comma => only_normal(Token::Comma),
            GlyphShape::Dot => Some(Token::Dot(script)),
            GlyphShape::Backspace => unimplemented!("compound characters are not yet supported"),
            GlyphShape::Hand => Some(match script {
                Script::Super | Script::Sub => unimplemented!(),
                Script::Normal => Token::Hand,
            }),
            GlyphShape::Sigma => {
                todo!("Sigma (which is a symex terminator) does not yet have a token")
            }
            GlyphShape::Pipe => only_normal(Token::Pipe),
            GlyphShape::DoublePipe => {
                todo!("double-pipe (which is a symex terminator) does not yet have a token")
            }
            GlyphShape::Solidus => only_normal(Token::Solidus),
            GlyphShape::Times => only_normal(Token::Times),
            GlyphShape::Hash => Some(Token::Hash(script)),
            GlyphShape::Arrow => Some(match script {
                Script::Super | Script::Sub => unimplemented!(),
                Script::Normal => Token::Arrow,
            }),
            GlyphShape::LessThan => only_normal(Token::LessThan),
            GlyphShape::GreaterThan => only_normal(Token::GreaterThan),
            GlyphShape::Overbar | GlyphShape::Square | GlyphShape::n => make_symex(),
            GlyphShape::SubsetOf => {
                todo!("'⊂' (subset-of) is a symex terminator but does not yet have a token")
            }
            GlyphShape::Or => Some(Token::LogicalOr(script)),
            GlyphShape::q
            | GlyphShape::Gamma
            | GlyphShape::t
            | GlyphShape::w
            | GlyphShape::x
            | GlyphShape::i
            | GlyphShape::y
            | GlyphShape::z => make_symex(),
            GlyphShape::Query => {
                todo!("'?' (question-mark) is a symex terminator but does not yet have a token")
            }
            GlyphShape::Union => only_normal(Token::Union),
            GlyphShape::Intersection => only_normal(Token::Intersection),
            GlyphShape::j | GlyphShape::k => make_symex(),
            GlyphShape::Alpha => make_symex(),
            GlyphShape::Delta => make_symex(),
            GlyphShape::p => make_symex(),
            GlyphShape::Epsilon => make_symex(),
            GlyphShape::h => Some(match script {
                // h cannot be part of a symex (see Users Handbook,
                // section 6-2.3).
                Script::Super | Script::Sub => unimplemented!(),
                Script::Normal => Token::Hold,
            }),
            // Todo: Token::NotHold.
            GlyphShape::SupersetOf => only_normal(Token::ProperSuperset),
            GlyphShape::Beta => make_symex(),
            GlyphShape::And => Some(Token::LogicalAnd(script)),
            GlyphShape::Lambda => make_symex(),
            GlyphShape::Tilde => only_normal(Token::Tilde),
            GlyphShape::LeftBrace => only_normal(Token::LeftBrace),
            GlyphShape::RightBrace => only_normal(Token::RightBrace),
            GlyphShape::IdenticalTo => only_normal(Token::IdenticalTo),
            GlyphShape::Equals => only_normal(Token::Equals),
            GlyphShape::Apostrophe => make_symex(),
            GlyphShape::Asterisk => only_normal(Token::Asterisk),
        }
    }

    #[derive(Debug)]
    enum TokenMergeResult {
        Merged(Token, Span),
        Failed {
            current: Result<Token, Unrecognised>,
            current_span: Span,
            incoming: Result<Token, Unrecognised>,
            incoming_span: Span,
        },
    }

    fn merge_tokens(
        current: (Result<Token, Unrecognised>, Span),
        incoming: (Result<Token, Unrecognised>, Span),
    ) -> TokenMergeResult {
        dbg!(&current);
        dbg!(&incoming);
        // We never merge errors with non-errors, so eliminate those
        // cases and, when both inputs are Ok variants, unwrap.
        let ((current, current_span), (incoming, incoming_span)) = match (current, incoming) {
            ((Ok(cur), cur_span), (Ok(inc), inc_span)) => ((cur, cur_span), (inc, inc_span)),
            ((cur, cur_span), (inc, inc_span)) => {
                return TokenMergeResult::Failed {
                    current: cur,
                    current_span: cur_span,
                    incoming: inc,
                    incoming_span: inc_span,
                };
            }
        };
        let merged_span = current_span.start..incoming_span.end;
        match current {
            Token::SuperscriptSymexSyllable(mut existing) => match incoming {
                Token::SuperscriptSymexSyllable(incoming) => {
                    existing.push_str(&incoming);
                    TokenMergeResult::Merged(Token::SuperscriptSymexSyllable(existing), merged_span)
                }
                Token::SuperscriptDigits(literal) => {
                    existing.push_str(&literal.digits);
                    if literal.has_trailing_dot {
                        existing.push(DOT_CHAR);
                    }
                    TokenMergeResult::Merged(Token::SuperscriptSymexSyllable(existing), merged_span)
                }
                Token::Dot(Script::Super) => {
                    existing.push(DOT_CHAR);
                    TokenMergeResult::Merged(Token::SuperscriptSymexSyllable(existing), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::SuperscriptSymexSyllable(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::SuperscriptDigits(mut existing) => match incoming {
                Token::SuperscriptDigits(incoming) => {
                    existing.append_digits_of_literal(incoming);
                    TokenMergeResult::Merged(Token::SuperscriptDigits(existing), merged_span)
                }
                Token::Dot(Script::Super) if !existing.has_trailing_dot => {
                    existing.has_trailing_dot = true;
                    TokenMergeResult::Merged(Token::SuperscriptDigits(existing), merged_span)
                }
                Token::SuperscriptSymexSyllable(sym) => {
                    let mut s: String = existing.digits;
                    s.extend(sym.chars());
                    TokenMergeResult::Merged(Token::SuperscriptSymexSyllable(s), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::SuperscriptDigits(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::NormalSymexSyllable(mut existing) => match incoming {
                Token::NormalSymexSyllable(incoming) => {
                    existing.push_str(&incoming);
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(existing), merged_span)
                }
                Token::NormalDigits(literal) => {
                    existing.push_str(&literal.digits);
                    if literal.has_trailing_dot {
                        existing.push(DOT_CHAR);
                    }
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(existing), merged_span)
                }
                Token::Dot(Script::Normal) => {
                    existing.push(DOT_CHAR);
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(existing), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::NormalSymexSyllable(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::NormalDigits(mut existing) => match incoming {
                Token::NormalDigits(incoming) => {
                    existing.append_digits_of_literal(incoming);
                    TokenMergeResult::Merged(Token::NormalDigits(existing), merged_span)
                }
                Token::Dot(Script::Normal) if !existing.has_trailing_dot => {
                    existing.has_trailing_dot = true;
                    TokenMergeResult::Merged(Token::SuperscriptDigits(existing), merged_span)
                }
                Token::NormalSymexSyllable(sym) => {
                    let mut s: String = existing.digits;
                    s.extend(sym.chars());
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(s), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::NormalDigits(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::SubscriptSymexSyllable(mut existing) => match incoming {
                Token::SubscriptSymexSyllable(incoming) => {
                    existing.push_str(&incoming);
                    TokenMergeResult::Merged(Token::SubscriptSymexSyllable(existing), merged_span)
                }
                Token::SubscriptDigits(literal) => {
                    existing.push_str(&literal.digits);
                    if literal.has_trailing_dot {
                        existing.push(DOT_CHAR);
                    }
                    TokenMergeResult::Merged(Token::SubscriptSymexSyllable(existing), merged_span)
                }
                Token::Dot(Script::Sub) => {
                    existing.push(DOT_CHAR);
                    TokenMergeResult::Merged(Token::SubscriptSymexSyllable(existing), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::SubscriptSymexSyllable(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::SubscriptDigits(mut existing) => match incoming {
                Token::SubscriptDigits(incoming) => {
                    existing.append_digits_of_literal(incoming);
                    TokenMergeResult::Merged(Token::SubscriptDigits(existing), merged_span)
                }
                Token::Dot(Script::Sub) if !existing.has_trailing_dot => {
                    existing.has_trailing_dot = true;
                    TokenMergeResult::Merged(Token::SuperscriptDigits(existing), merged_span)
                }
                Token::SubscriptSymexSyllable(sym) => {
                    let mut s: String = existing.digits;
                    s.extend(sym.chars());
                    TokenMergeResult::Merged(Token::SubscriptSymexSyllable(s), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::SubscriptDigits(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            existing => TokenMergeResult::Failed {
                current: Ok(existing),
                current_span,
                incoming: Ok(incoming),
                incoming_span,
            },
        }
    }

    #[derive(Debug, Clone)]
    struct GlyphTokenizer<'a> {
        current: Option<(Result<super::Token, Unrecognised>, Span)>,
        inner: GlyphRecognizer<'a>,
    }

    impl<'a> GlyphTokenizer<'a> {
        fn new(input: &'a str) -> GlyphTokenizer<'a> {
            GlyphTokenizer {
                current: None,
                inner: GlyphRecognizer::new(input),
            }
        }

        pub(crate) fn get_next_spanned_token(
            &mut self,
        ) -> Option<(Result<super::Token, Unrecognised>, Span)> {
            use super::Token;
            loop {
                let maybe_spanned_new_token: Option<(Result<Token, Unrecognised>, Span)> =
                    match dbg!(self.inner.next()) {
                        None => None,
                        Some(Err(e)) => Some((Err(e), self.inner.span())),
                        Some(Ok(g)) => {
                            if matches!(g.get().shape(), GlyphShape::Space | GlyphShape::Tab) {
                                match self.current.take() {
                                    Some(r) => {
                                        return Some(r);
                                    }
                                    None => {
                                        continue;
                                    }
                                }
                            } else {
                                let tok_start = self.inner.span().start;
                                match tokenise_single_glyph(g) {
                                    Some(token) => {
                                        let span = tok_start..self.inner.span().end;
                                        Some((Ok(token), span))
                                    }
                                    None => {
                                        unimplemented!("unable to convert glyph '{g:?}' to a token")
                                    }
                                }
                            }
                        }
                    };
                if let Some((newtoken, newtoken_span)) = maybe_spanned_new_token {
                    if let Some((current, current_span)) = self.current.take() {
                        match merge_tokens((current, current_span), (newtoken, newtoken_span)) {
                            TokenMergeResult::Merged(merged, merged_span) => {
                                self.current = Some((Ok(merged), merged_span));
                                continue;
                            }
                            TokenMergeResult::Failed {
                                current,
                                current_span,
                                incoming: newtoken,
                                incoming_span: newtoken_span,
                            } => {
                                let result = (current, current_span);
                                self.current = Some((newtoken, newtoken_span));
                                return Some(result);
                            }
                        }
                    } else {
                        // There is a new token but no existing token.
                        self.current = Some((newtoken, newtoken_span));
                    }
                } else {
                    // There is no new token.
                    return self.current.take();
                }
            }
        }
    }

    #[test]
    fn test_glyph_tokenizer_simple_multi_token() {
        use super::Token;
        let mut lex = GlyphTokenizer::new("hx");
        assert_eq!(lex.get_next_spanned_token(), Some((Ok(Token::Hold), 0..1)));
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::NormalSymexSyllable("x".to_string())), 1..2))
        );
        assert_eq!(lex.get_next_spanned_token(), None);
    }

    #[test]
    fn test_glyph_tokenizer_glyph_names() {
        use super::Token;
        let mut lex = GlyphTokenizer::new("@sup_eps@");
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::SuperscriptSymexSyllable("ε".to_string())), 0..9))
        );
        assert_eq!(lex.get_next_spanned_token(), None);
    }

    #[test]
    fn test_glyph_tokenizer_multi_glyph_token() {
        use super::Token;
        // These glyphs are a single token because they are both valid
        // in a symex and are both in superscript.
        let mut lex = GlyphTokenizer::new("@sup_eps@ᵂ");
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::SuperscriptSymexSyllable("εW".to_string())), 0..10))
        );
        assert_eq!(lex.get_next_spanned_token(), None);
    }

    #[test]
    fn test_glyph_tokenizer_script_change_breaks_tokens() {
        // Verify that a change from superscript to normal script
        // causes two immediately adjoining letters to be considereed
        // separate tokens.
        use super::Token;
        let mut lex = GlyphTokenizer::new("@sup_eps@W");
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::SuperscriptSymexSyllable("ε".to_string())), 0..9))
        );
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::NormalSymexSyllable("W".to_string())), 9..10))
        );
        assert_eq!(lex.get_next_spanned_token(), None);
    }

    #[test]
    fn test_glyph_tokenizer_space_breaks_tokens() {
        // Verify that a space breaks tokens.  For symexes, the parser
        // will join the syllables together into a single name, but
        // they are scanned as separate tokens.
        use super::Token;
        let mut lex = GlyphTokenizer::new("W Q");
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::NormalSymexSyllable("W".to_string())), 0..1))
        );
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::NormalSymexSyllable("Q".to_string())), 2..3))
        );
        assert_eq!(lex.get_next_spanned_token(), None);
    }

    #[derive(Debug, Clone)]
    pub(crate) struct NewLexer<'a> {
        lower: super::lower::LowerLexer<'a>,
        upper: Option<GlyphTokenizer<'a>>,
        upper_span: Option<Span>,
    }

    impl<'a> NewLexer<'a> {
        pub(crate) fn new(input: &'a str) -> NewLexer<'a> {
            NewLexer {
                lower: super::lower::LowerLexer::new(input),
                upper: None,
                upper_span: None,
            }
        }

        fn adjust_span(&self, span: Range<usize>) -> Range<usize> {
            match self.upper_span.as_ref() {
                None => span,
                Some(upper_span) => {
                    let offset = span.start;
                    (upper_span.start + offset)..(upper_span.end + offset)
                }
            }
        }

        pub(crate) fn span(&self) -> Range<usize> {
            self.adjust_span(self.lower.span())
        }

        // TODO: now that we return an error token to report a problem, We
        // no longer need the return type to be Option<Result<...>>.
        fn next_upper(
            upper: &mut GlyphTokenizer<'a>,
        ) -> Option<(Result<Token, Unrecognised>, Span)> {
            let (tok, span) = upper.get_next_spanned_token()?;
            Some(match tok {
                Ok(token_from_upper) => (Ok(token_from_upper), span),
                Err(e) => (Ok(Token::Error(e.to_string())), span),
            })
        }

        pub(crate) fn spanned(&self) -> SpannedIter<'a> {
            let lexer: NewLexer<'a> = self.clone();
            SpannedIter::new(lexer)
        }

        fn get_next(&mut self) -> Option<Result<Token, Unrecognised>> {
            use super::lower::Lexeme;
            if let Some(upper_lexer) = self.upper.as_mut() {
                match NewLexer::next_upper(upper_lexer) {
                    Some((r, span)) => {
                        self.upper_span = Some(span);
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
            self.upper_span = None;
            match self.lower.next() {
                Lexeme::EndOfInput => None,
                Lexeme::Tok(tok) => Some(Ok(tok)),
                // If the lower lexer actually returns Unrecognised, the
                // slice in `content` is likely very short (a single
                // character perhaps) and that is unlikely to be
                // tokenizable.  So the upper lexer will likely also
                // return an error for that text too.
                Lexeme::Text(text) => {
                    let upper = GlyphTokenizer::new(text);
                    self.upper = Some(upper);
                    match NewLexer::next_upper(
                        self.upper
                            .as_mut()
                            .expect("the option cannot be empty, we just filled it"),
                    ) {
                        Some((r, span)) => {
                            self.upper_span = Some(span);
                            Some(r)
                        }
                        None => None,
                    }
                }
                Lexeme::Err(e) => Some(Err(e)),
            }
        }
    }

    impl<'a> Iterator for NewLexer<'a> {
        type Item = Result<Token, Unrecognised>;

        fn next(&mut self) -> Option<Result<Token, Unrecognised>> {
            self.get_next()
        }
    }

    #[derive(Debug, Clone)]
    pub(crate) struct SpannedIter<'a> {
        lexer: NewLexer<'a>,
    }

    impl<'a> SpannedIter<'a> {
        pub(crate) fn new(lexer: NewLexer<'a>) -> SpannedIter<'a> {
            SpannedIter { lexer }
        }
    }

    impl<'a> Iterator for SpannedIter<'a> {
        type Item = (Result<Token, Unrecognised>, Span);

        fn next(&mut self) -> Option<Self::Item> {
            let token = self.lexer.next();
            token.map(|t| (t, self.lexer.span()))
        }
    }
}
