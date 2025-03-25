use std::{
    fmt::{Display, Write},
    ops::Range,
};

use super::{
    glyph::{self, elevate},
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
#[cfg(test)]
mod tests;

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
        self.digits.push_str(&other.digits);
    }

    pub(crate) fn has_trailing_dot(&self) -> bool {
        self.has_trailing_dot
    }

    pub(crate) fn take_digits(self) -> String {
        self.digits
    }
}

/// The parser consumes these tokens.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum Token {
    // In order for the parser to recover from tokenization errors, we
    // need to be able to emit an error token.
    Error(String),

    LeftBrace,
    RightBrace,
    Newline,

    /// The parser currently only handled parenthesised expressions in
    /// normal script.
    LeftParen(Script),

    /// The parser currently only handled parenthesised expressions in
    /// normal script.
    RightParen(Script),

    /// Accept either 'h' or ':' signalling the hold bit (of the
    /// instruction word) should be set.  The documentation seems to
    /// use both, though perhaps ':' is the older usage.
    ///
    /// While h is indeed a letter, it is not one of the letters which
    /// can form part of a symex.  See the TX-2 Users Handbook,
    /// section 6-3.2, "RULES FOR SYMEX FORMATION".
    Hold,

    NotHold,

    Arrow,

    Hand,

    Hash(Script),

    Equals,

    /// Asterisk is used quite heavily (indicating deferred addressing)
    /// but while the TX-2 supports superscript and subscript
    /// asterisks, they don't seem to be used.  They are not valid as
    /// part of a symex (see User handbook, section 6-2.3) and are not
    /// macro terminators (6-4.5).  However, they are valid as part of
    /// a superposed character sequence making up a compound-character
    /// macro name.
    Asterisk,

    Pipe,

    ProperSuperset,

    IdenticalTo,

    Tilde,

    LessThan,

    GreaterThan,

    Intersection,

    Union,

    /// Solidus is often called "slash" but people often confuse slash
    /// and backslash.  So we don't call it either.
    Solidus,

    // @plus@ is actually not the correct glyph name, following sub.py.
    Plus(Script),

    Minus(Script),

    Times,

    LogicalOr(Script),

    LogicalAnd(Script),

    // Any unary "-" is handled in the parser.
    Digits(Script, NumericLiteral),

    // TODO: missing from this are: overbar, square, circle.
    /// The rules concerning which characters can be part of a symex
    /// are given in the TX-2 Users Handbook, section 6-3.2, "RULES
    /// FOR SYMEX FORMATION".
    ///
    /// We so not accept dot as part of this token becuase it behaves
    /// differently in some circumstances (it is a macro terminator).
    /// However it is part of a valid symex also, and so we will need
    /// to parse it as such.
    NormalSymexSyllable(String),

    // No support for superscript apostrophe, underscore.
    SuperscriptSymexSyllable(String),

    // No support for superscript apostrophe, underscore.
    SubscriptSymexSyllable(String),

    // If change the representation of the dot in the token
    // definition, please also change DOT_CHAR.
    //
    // The Dot token requires care in handling.  It is valid at the
    // end of a numeric literal (where it signals use of the alternate
    // base).  It is also valid in a symex.  But, it is also a macro
    // terminator.  To handle these complexities, we include the dot
    // in numeric literals (inside which spaces are not allowed).  But
    // we do not allow Dot inside Symex syllables - with the idea that
    // this will help us to correctly process them when used as macro
    // terminators.
    Dot(Script),

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
            Token::Digits(script, numeric_literal) => {
                write!(f, "{}", elevate(*script, numeric_literal.to_string()))
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

pub(crate) use lexer_impl_new::*;
pub(crate) type Lexer<'a> = NewLexer<'a>;

mod lexer_impl_new {
    use super::glyph::{glyph_from_name, glyph_of_char, Elevated, Glyph, GlyphShape, Unrecognised};
    use super::{NumericLiteral, DOT_CHAR};
    use base::charset::Script;
    use std::ops::Range;
    use std::str::CharIndices;

    use super::{Span, Token};

    #[derive(Debug, Clone)]
    struct GlyphRecognizer<'a> {
        it: CharIndices<'a>,
        pos: usize,
        glyph_start: usize,
    }

    impl<'a> GlyphRecognizer<'a> {
        fn new(input: &'a str) -> GlyphRecognizer<'a> {
            Self {
                it: input.char_indices(),
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
            self.glyph_start..(self.it.offset())
        }

        fn next_named_glyph(&mut self) -> Option<Result<Elevated<&'static Glyph>, Unrecognised>> {
            let mut name: String = String::with_capacity(10);
            let mut got_anything = false;
            while let Some(ch) = self.get_next_char() {
                got_anything = true;
                if ch == '@' {
                    break;
                } else {
                    name.push(ch);
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

    impl Iterator for GlyphRecognizer<'_> {
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
            super::Token::Digits(script, literal)
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
            Token::Minus(Script::Normal) if incoming == Token::GreaterThan => {
                TokenMergeResult::Merged(Token::Arrow, merged_span)
            }
            Token::SuperscriptSymexSyllable(mut existing) => match incoming {
                Token::SuperscriptSymexSyllable(incoming) => {
                    existing.push_str(&incoming);
                    TokenMergeResult::Merged(Token::SuperscriptSymexSyllable(existing), merged_span)
                }
                Token::Digits(Script::Super, literal) => {
                    existing.push_str(&literal.digits);
                    if literal.has_trailing_dot {
                        existing.push(DOT_CHAR);
                    }
                    TokenMergeResult::Merged(Token::SuperscriptSymexSyllable(existing), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::SuperscriptSymexSyllable(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::NormalSymexSyllable(mut existing) => match incoming {
                Token::Hold => {
                    // overbar followed by h means not-hold, and we handle this case specially.
                    if existing == "\u{0305}" {
                        TokenMergeResult::Merged(Token::NotHold, merged_span)
                    } else {
                        TokenMergeResult::Failed {
                            current: Ok(Token::NormalSymexSyllable(existing)),
                            current_span,
                            incoming: Ok(Token::Hold),
                            incoming_span,
                        }
                    }
                }
                Token::NormalSymexSyllable(incoming) => {
                    existing.push_str(&incoming);
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(existing), merged_span)
                }
                Token::Digits(Script::Normal, literal) => {
                    existing.push_str(&literal.digits);
                    if literal.has_trailing_dot {
                        existing.push(DOT_CHAR);
                    }
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(existing), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::NormalSymexSyllable(existing)),
                    current_span,
                    incoming: Ok(other),
                    incoming_span,
                },
            },
            Token::Digits(left_script, mut existing) => match incoming {
                Token::Digits(right_script, incoming) if left_script == right_script => {
                    existing.append_digits_of_literal(incoming);
                    TokenMergeResult::Merged(Token::Digits(left_script, existing), merged_span)
                }
                Token::Dot(right_script)
                    if left_script == right_script && !existing.has_trailing_dot =>
                {
                    existing.has_trailing_dot = true;
                    TokenMergeResult::Merged(Token::Digits(left_script, existing), merged_span)
                }
                Token::NormalSymexSyllable(sym) if left_script == Script::Normal => {
                    let mut s: String = existing.digits;
                    s.push_str(&sym);
                    TokenMergeResult::Merged(Token::NormalSymexSyllable(s), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::Digits(left_script, existing)),
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
                Token::Digits(Script::Sub, literal) => {
                    existing.push_str(&literal.digits);
                    if literal.has_trailing_dot {
                        existing.push(DOT_CHAR);
                    }
                    TokenMergeResult::Merged(Token::SubscriptSymexSyllable(existing), merged_span)
                }
                other => TokenMergeResult::Failed {
                    current: Ok(Token::SubscriptSymexSyllable(existing)),
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
                    match self.inner.next() {
                        None => None,
                        Some(Err(Unrecognised::InvalidChar('ℏ'))) => {
                            // ℏ is Unicode code point U+210F.  There
                            // is no glyph matching ℏ (because on the
                            // TX-2 this was produced with an overbar
                            // (which does not advance the carriage)
                            // and a regular h.  We accept it as a
                            // special case.
                            //
                            // Because there is no Glyph for this, we
                            // do not accept @...@ (e.g. @hbar@) for
                            // this.
                            return Some((Ok(super::Token::NotHold), self.inner.span()));
                        }
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
        let input = "@sup_eps@ᵂ";
        let mut lex = GlyphTokenizer::new(input);
        assert_eq!(
            lex.get_next_spanned_token(),
            Some((Ok(Token::SuperscriptSymexSyllable("εW".to_string())), 0..12))
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

    impl Iterator for NewLexer<'_> {
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

    impl Iterator for SpannedIter<'_> {
        type Item = (Result<Token, Unrecognised>, Span);

        fn next(&mut self) -> Option<Self::Item> {
            let token = self.lexer.next();
            token.map(|t| (t, self.lexer.span()))
        }
    }
}
