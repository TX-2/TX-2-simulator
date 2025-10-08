use std::{
    fmt::{Display, Write},
    ops::Range,
    str::CharIndices,
};

use base::{
    Unsigned36Bit,
    charset::{Script, subscript_char, superscript_char},
    error::StringConversionFailed,
};

use super::{
    glyph::{
        Elevated, Glyph, GlyphShape, Unrecognised, elevate, glyph_from_name, glyph_of_char,
        is_allowed_in_symex,
    },
    parser::helpers,
    state::NumeralMode,
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
        mode: NumeralMode,
    ) -> Result<Unsigned36Bit, StringConversionFailed> {
        helpers::make_num(self.digits.as_str(), self.has_trailing_dot, mode)
    }

    pub(crate) fn append_digits_of_literal(&mut self, other: &NumericLiteral) {
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum ErrorTokenKind {
    Tab,
    UnrecognisedGlyph(Unrecognised),
}

impl Display for ErrorTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ErrorTokenKind::Tab => {
                const LONG_MSG: &str = concat!(
                    "Please do not use the TAB character. ",
                    "The differences between the M4 assembler's interpretation of tab and its interpreation of the space ",
                    "characer are complex, and these are not fully implemented.  If you want to ",
                    "prevent two adjacent symexes being joined together, please use parentheses ",
                    "or an explicit '+' operation instead.  That is, use (A)(B) or A+B instead of A<tab>B. ",
                    "If you intended to simply use TAB to produce some particular code layout, please ",
                    "use spaces instead.",
                );
                f.write_str(LONG_MSG)
            }
            ErrorTokenKind::UnrecognisedGlyph(e) => write!(f, "{e}"),
        }
    }
}

/// The parser consumes these tokens.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum Token {
    // In order for the parser to recover from tokenization errors, we
    // need to be able to emit an error token.
    Error(ErrorTokenKind),
    LeftBrace(Script),
    RightBrace(Script),
    Newline,
    Tab,

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
    NotHold, // handled specially, there is no glyph for this.
    Arrow(Script),
    Hand(Script),
    Hash(Script),
    Equals(Script),

    /// Asterisk is used quite heavily (indicating deferred addressing)
    /// but while the TX-2 supports superscript and subscript
    /// asterisks, they don't seem to be used.  They are not valid as
    /// part of a symex (see User handbook, section 6-2.3) and are not
    /// macro terminators (6-4.5).  However, they are valid as part of
    /// a superposed character sequence making up a compound-character
    /// macro name.
    Asterisk(Script),

    Pipe(Script),
    DoublePipe(Script),
    ProperSuperset(Script),
    SubsetOf(Script),
    IdenticalTo(Script),
    Tilde(Script),
    LessThan(Script),
    GreaterThan(Script),
    Query(Script), // question mark, i.e. "?"
    Intersection(Script),
    Union(Script),

    /// Solidus is often called "slash" but people often confuse slash
    /// and backslash.  So we don't call it either.
    Solidus(Script),

    // @plus@ is actually not the correct glyph name, following sub.py.
    Plus(Script),
    Minus(Script),
    Times(Script),
    LogicalOr(Script),
    LogicalAnd(Script),

    // Any unary "-" is handled in the parser.
    Digits(Script, NumericLiteral),

    // Used as the index component of instructions like MKZ₄.₁₀
    BitPosition(Script, String, String),

    // TODO: missing from this are: overbar, square, circle.
    /// The rules concerning which characters can be part of a symex
    /// are given in the TX-2 Users Handbook, section 6-3.2, "RULES
    /// FOR SYMEX FORMATION".
    ///
    /// We so not accept dot as part of this token becuase it behaves
    /// differently in some circumstances (it is a macro terminator).
    /// However it is part of a valid symex also, and so we will need
    /// to parse it as such.
    SymexSyllable(Script, String),

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
    Comma(Script),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut write_elevated = |script: &Script, s: &str| -> std::fmt::Result {
            let el = elevate(*script, s);
            write!(f, "{el}")
        };

        match self {
            Token::Error(msg) => write!(f, "(error: {msg})"),
            Token::LeftBrace(script) => write_elevated(script, "{"),
            Token::RightBrace(script) => write_elevated(script, "}"),
            Token::Newline => f.write_char('\n'),
            Token::Tab => f.write_char('\t'),
            Token::LeftParen(script) => write_elevated(script, "("),
            Token::RightParen(script) => write_elevated(script, ")"),
            Token::Hold => f.write_char('h'),
            Token::NotHold => f.write_char('ℏ'),
            Token::Arrow(script) => write_elevated(script, "->"),
            Token::Hand(script) => write_elevated(script, "☛"),
            Token::Asterisk(script) => write_elevated(script, "*"),
            Token::Dot(script) => write_elevated(script, DOT_STR),
            Token::Hash(script) => write_elevated(script, "#"),
            Token::Equals(script) => write_elevated(script, "="),
            Token::Pipe(script) => write_elevated(script, "|"),
            Token::DoublePipe(script) => write_elevated(script, "‖"), // U+2016
            Token::ProperSuperset(script) => write_elevated(script, "⊃"), // U+2283
            Token::SubsetOf(script) => write_elevated(script, "⊂"),   // U+2282
            Token::IdenticalTo(script) => write_elevated(script, "≡"),
            Token::Tilde(script) => write_elevated(script, "~"),
            Token::LessThan(script) => write_elevated(script, "<"),
            Token::GreaterThan(script) => write_elevated(script, ">"),
            Token::Query(script) => write_elevated(script, "?"),
            Token::Intersection(script) => write_elevated(script, "∩"),
            Token::Union(script) => write_elevated(script, "∪"),
            Token::Solidus(script) => write_elevated(script, "/"),
            Token::Plus(script) => write_elevated(script, "+"),
            Token::Minus(script) => write_elevated(script, "-"),
            Token::Times(script) => write_elevated(script, "×"),
            Token::LogicalOr(script) => write_elevated(script, "∨"),
            Token::LogicalAnd(script) => write_elevated(script, "∧"),
            Token::Digits(script, numeric_literal) => {
                write!(f, "{}", elevate(*script, numeric_literal.to_string()))
            }
            Token::BitPosition(script, quarter, bit) => {
                let q_string = elevate(*script, quarter.to_string());
                let bit_string = elevate(*script, bit.to_string());
                let dotname = match script {
                    Script::Normal => "@dot@",
                    Script::Sub => "@sub_dot@",
                    Script::Super => "@sup_dot@",
                };
                write!(f, "{q_string}{dotname}{bit_string}")
            }
            Token::SymexSyllable(script, name) => {
                #[allow(clippy::unnecessary_wraps)]
                fn nochange(ch: char) -> Result<char, ()> {
                    Ok(ch)
                }
                fn convert_to_sup(ch: char) -> Result<char, ()> {
                    superscript_char(ch).map_err(|_| ())
                }
                fn convert_to_sub(ch: char) -> Result<char, ()> {
                    subscript_char(ch).map_err(|_| ())
                }
                type Transformer = fn(char) -> Result<char, ()>;
                let (prefix, transform): (&'static str, Transformer) = match script {
                    Script::Super => ("super_", convert_to_sup),
                    Script::Normal => ("", nochange),
                    Script::Sub => ("sub_", convert_to_sub),
                };
                for ch in name.chars() {
                    match transform(ch) {
                        Ok(sup_ch) => f.write_char(sup_ch),
                        Err(()) => match ch {
                            'α' => write!(f, "@{prefix}alpha@"),
                            'β' => write!(f, "@{prefix}beta@"),
                            'γ' => write!(f, "@{prefix}gamma@"),
                            'Δ' => write!(f, "@{prefix}delta@"),
                            'ε' => write!(f, "@{prefix}eps@"),
                            'λ' => write!(f, "@{prefix}lambda@"),
                            _ => write!(f, "@{prefix}{ch}@"),
                        },
                    }?;
                }
                Ok(())
            }
            Token::Comma(script) => write_elevated(script, ","),
        }
    }
}

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

fn tokenise_single_glyph(g: Elevated<&'static Glyph>) -> Option<Token> {
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
        Token::Digits(script, literal)
    };
    let make_symex = || -> Option<Token> {
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
                panic!(
                    "incoming token '{g:?}' was assigned as part of a symex syllable, but we don't have a character for it in script {script:?}"
                );
            }
            1 => (),
            n => {
                panic!(
                    "incoming token '{g:?}' was assigned as part of a symex syllable, but the resuting initial token body unexpectedly has more than one character (specifically, {n}): {name:?}"
                );
            }
        }
        Some(Token::SymexSyllable(script, name))
    };

    // In the grammar described in section 6 of the Users Handbook,
    // space and tab are not handled in quite the same way.  Space is
    // allowed in symexes, but tab is not (tab terminates a symex).
    #[allow(clippy::match_same_arms)] // easier to read in existing order
    let output: Option<Token> = match g.get().shape() {
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
        GlyphShape::Comma => Some(Token::Comma(script)),
        GlyphShape::Dot => Some(Token::Dot(script)),
        GlyphShape::Backspace => unimplemented!("compound characters are not yet supported"),
        GlyphShape::Hand => Some(Token::Hand(script)),
        GlyphShape::Sigma => {
            todo!("Sigma (which is a symex terminator) does not yet have a token")
        }
        GlyphShape::Pipe => Some(Token::Pipe(script)),
        GlyphShape::DoublePipe => Some(Token::DoublePipe(script)),
        GlyphShape::Solidus => Some(Token::Solidus(script)),
        GlyphShape::Times => Some(Token::Times(script)),
        GlyphShape::Hash => Some(Token::Hash(script)),
        GlyphShape::Arrow => Some(Token::Arrow(script)),
        GlyphShape::LessThan => Some(Token::LessThan(script)),
        GlyphShape::GreaterThan => Some(Token::GreaterThan(script)),
        GlyphShape::Overbar | GlyphShape::Square | GlyphShape::n => make_symex(),
        GlyphShape::SubsetOf => Some(Token::SubsetOf(script)),
        GlyphShape::Or => Some(Token::LogicalOr(script)),
        GlyphShape::q
        | GlyphShape::Gamma
        | GlyphShape::t
        | GlyphShape::w
        | GlyphShape::x
        | GlyphShape::i
        | GlyphShape::y
        | GlyphShape::z => make_symex(),
        GlyphShape::Query => Some(Token::Query(script)),
        GlyphShape::Union => Some(Token::Union(script)),
        GlyphShape::Intersection => Some(Token::Intersection(script)),
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
        GlyphShape::SupersetOf => Some(Token::ProperSuperset(script)),
        GlyphShape::Beta => make_symex(),
        GlyphShape::And => Some(Token::LogicalAnd(script)),
        GlyphShape::Lambda => make_symex(),
        GlyphShape::Tilde => Some(Token::Tilde(script)),
        GlyphShape::LeftBrace => Some(Token::LeftBrace(script)),
        GlyphShape::RightBrace => Some(Token::RightBrace(script)),
        GlyphShape::IdenticalTo => Some(Token::IdenticalTo(script)),
        GlyphShape::Equals => Some(Token::Equals(script)),
        GlyphShape::Apostrophe => make_symex(),
        GlyphShape::Asterisk => Some(Token::Asterisk(script)),
    };
    if let Some(t) = output.as_ref() {
        if matches!(t, Token::SymexSyllable(_, _)) {
            assert!(
                is_allowed_in_symex(g.get().shape),
                "attempted to make a symex with disallowed glyph shape {g:?}"
            );
        } else if matches!(t, Token::Digits(_, _) | Token::Dot(_)) {
            // Digits and dots mostly called "PERIOD" in the Users
            // Handbook) are allowed in numeric literals but also
            // allowed in symexes.  We scan them as numeric
            // literals and then join them into symexes when we
            // discover what their neighbours are.
            assert!(
                is_allowed_in_symex(g.get().shape),
                "all glyphs allowed in numeric literals are also allowed in symexes, but this went wrong for {g:?}"
            );
        } else if g.get().shape == GlyphShape::Space {
            // Permitted in a symex but this is implemented at the parser level.
        } else {
            assert!(
                !is_allowed_in_symex(g.get().shape),
                "glyph shape {g:?} is allowed in a symex but the scanner didn't recognise it that way"
            );
        }
    }
    output
}

#[derive(Debug, PartialEq, Eq)]
enum TokenMergeResult {
    Merged(Token, Span),
    Failed {
        current: Token,
        current_span: Span,
        incoming: Token,
        incoming_span: Span,
    },
}

fn merge_tokens(current: (Token, Span), incoming: (Token, Span)) -> TokenMergeResult {
    // We never merge errors with non-errors, so eliminate those
    // cases and, when both inputs are Ok variants, unwrap.
    let ((current, current_span), (incoming, incoming_span)) = (current, incoming);
    if matches!(
        (&current, &incoming),
        (&Token::Error(_), _) | (_, &Token::Error(_))
    ) {
        return TokenMergeResult::Failed {
            current,
            current_span,
            incoming,
            incoming_span,
        };
    }

    let merged_span = current_span.start..incoming_span.end;
    match current {
        Token::Minus(incoming_script)
            if incoming == Token::GreaterThan(incoming_script)
                && incoming_script == Script::Normal =>
        {
            TokenMergeResult::Merged(Token::Arrow(Script::Normal), merged_span)
        }
        Token::SymexSyllable(existing_script, mut existing_name) => match incoming {
            Token::Hold if existing_script == Script::Normal => {
                // overbar followed by h means not-hold, and we handle this case specially.
                if existing_name == "\u{0305}" {
                    TokenMergeResult::Merged(Token::NotHold, merged_span)
                } else {
                    TokenMergeResult::Failed {
                        current: Token::SymexSyllable(existing_script, existing_name),
                        current_span,
                        incoming: Token::Hold,
                        incoming_span,
                    }
                }
            }
            Token::SymexSyllable(incoming_script, incoming_name)
                if existing_script == incoming_script =>
            {
                existing_name.push_str(&incoming_name);
                TokenMergeResult::Merged(
                    Token::SymexSyllable(existing_script, existing_name),
                    merged_span,
                )
            }
            Token::Digits(incoming_script, literal) if existing_script == incoming_script => {
                existing_name.push_str(&literal.digits);
                if literal.has_trailing_dot {
                    existing_name.push(DOT_CHAR);
                }
                TokenMergeResult::Merged(
                    Token::SymexSyllable(existing_script, existing_name),
                    merged_span,
                )
            }
            other => TokenMergeResult::Failed {
                current: Token::SymexSyllable(existing_script, existing_name),
                current_span,
                incoming: other,
                incoming_span,
            },
        },
        Token::Digits(existing_script, mut existing_literal) => {
            if existing_literal.has_trailing_dot {
                // The left-hand literal has a dot.  So the valid
                // cases are where we're part-way through a symex, or
                // a bit position specification.
                match incoming {
                    Token::Digits(
                        Script::Sub,
                        NumericLiteral {
                            digits: incoming_digit,
                            has_trailing_dot: false,
                        },
                    ) if existing_script == Script::Sub => TokenMergeResult::Merged(
                        Token::BitPosition(
                            existing_script,
                            existing_literal.digits,
                            incoming_digit,
                        ),
                        merged_span,
                    ),
                    // Not valid for RHS to be Dot, as we already have one.
                    other => TokenMergeResult::Failed {
                        current: Token::Digits(existing_script, existing_literal),
                        current_span,
                        incoming: other,
                        incoming_span,
                    },
                }
            } else {
                match incoming {
                    Token::Digits(incoming_script, incoming_name)
                        if existing_script == incoming_script =>
                    {
                        existing_literal.append_digits_of_literal(&incoming_name);
                        TokenMergeResult::Merged(
                            Token::Digits(existing_script, existing_literal),
                            merged_span,
                        )
                    }
                    Token::Dot(right_script)
                        if existing_script == right_script
                            && !existing_literal.has_trailing_dot =>
                    {
                        existing_literal.has_trailing_dot = true;
                        TokenMergeResult::Merged(
                            Token::Digits(existing_script, existing_literal),
                            merged_span,
                        )
                    }
                    Token::SymexSyllable(incoming_script, sym)
                        if existing_script == incoming_script =>
                    {
                        let mut existing_name: String = existing_literal.digits;
                        existing_name.push_str(&sym);
                        TokenMergeResult::Merged(
                            Token::SymexSyllable(existing_script, existing_name),
                            merged_span,
                        )
                    }
                    other => TokenMergeResult::Failed {
                        current: Token::Digits(existing_script, existing_literal),
                        current_span,
                        incoming: other,
                        incoming_span,
                    },
                }
            }
        }
        Token::BitPosition(existing_script, existing_quarter, mut existing_bit) => match incoming {
            Token::Digits(
                incoming_script,
                NumericLiteral {
                    digits: incoming_digit,
                    has_trailing_dot: false,
                },
            ) if existing_script == incoming_script => {
                existing_bit.push_str(incoming_digit.as_str());
                TokenMergeResult::Merged(
                    Token::BitPosition(existing_script, existing_quarter, existing_bit),
                    merged_span,
                )
            }
            Token::Dot(incoming_script) if existing_script == incoming_script => {
                let name = format!("{existing_quarter}\u{00B7}{existing_bit}\u{00B7}");
                TokenMergeResult::Merged(Token::SymexSyllable(Script::Sub, name), merged_span)
            }
            Token::SymexSyllable(incoming_script, symbol) if existing_script == incoming_script => {
                let name = format!("{existing_quarter}\u{00B7}{existing_bit}{symbol}");
                TokenMergeResult::Merged(Token::SymexSyllable(Script::Sub, name), merged_span)
            }
            other => TokenMergeResult::Failed {
                current: Token::BitPosition(existing_script, existing_quarter, existing_bit),
                current_span,
                incoming: other,
                incoming_span,
            },
        },
        existing => TokenMergeResult::Failed {
            current: existing,
            current_span,
            incoming,
            incoming_span,
        },
    }
}

#[derive(Debug, Clone)]
struct GlyphTokenizer<'a> {
    current: Option<(Token, Span)>,
    inner: GlyphRecognizer<'a>,
}

impl<'a> GlyphTokenizer<'a> {
    fn new(input: &'a str) -> GlyphTokenizer<'a> {
        GlyphTokenizer {
            current: None,
            inner: GlyphRecognizer::new(input),
        }
    }

    pub(crate) fn get_next_spanned_token(&mut self) -> Option<(Token, Span)> {
        loop {
            let maybe_spanned_new_token: Option<(Token, Span)> = match self.inner.next() {
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
                    return Some((Token::NotHold, self.inner.span()));
                }
                Some(Err(e)) => {
                    let error_token = Token::Error(ErrorTokenKind::UnrecognisedGlyph(e));
                    Some((error_token, self.inner.span()))
                }
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
                                Some((token, span))
                            }
                            None => {
                                unimplemented!("unable) to convert glyph '{g:?}' to a token")
                            }
                        }
                    }
                }
            };
            if let Some((newtoken, newtoken_span)) = maybe_spanned_new_token {
                if let Some((current, current_span)) = self.current.take() {
                    match merge_tokens((current, current_span), (newtoken, newtoken_span)) {
                        TokenMergeResult::Merged(merged, merged_span) => {
                            self.current = Some((merged, merged_span));
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
    let mut lex = GlyphTokenizer::new("hx");
    assert_eq!(lex.get_next_spanned_token(), Some((Token::Hold, 0..1)));
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Normal, "x".to_string()), 1..2))
    );
    assert_eq!(lex.get_next_spanned_token(), None);
}

#[test]
fn test_glyph_tokenizer_glyph_names() {
    let mut lex = GlyphTokenizer::new("@sup_eps@");
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Super, "ε".to_string()), 0..9))
    );
    assert_eq!(lex.get_next_spanned_token(), None);
}

#[test]
fn test_glyph_tokenizer_multi_glyph_token() {
    // These glyphs are a single token because they are both valid
    // in a symex and are both in superscript.
    let input = "@sup_eps@ᵂ";
    let mut lex = GlyphTokenizer::new(input);
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Super, "εW".to_string()), 0..12))
    );
    assert_eq!(lex.get_next_spanned_token(), None);
}

#[test]
fn test_glyph_tokenizer_script_change_breaks_tokens() {
    // Verify that a change from superscript to normal script
    // causes two immediately adjoining letters to be considereed
    // separate tokens.
    let mut lex = GlyphTokenizer::new("@sup_eps@W");
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Super, "ε".to_string()), 0..9))
    );
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Normal, "W".to_string()), 9..10))
    );
    assert_eq!(lex.get_next_spanned_token(), None);
}

#[test]
fn test_glyph_tokenizer_space_breaks_tokens() {
    // Verify that a space breaks tokens.  For symexes, the parser
    // will join the syllables together into a single name, but
    // they are scanned as separate tokens.
    let mut lex = GlyphTokenizer::new("W Q");
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Normal, "W".to_string()), 0..1))
    );
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::SymexSyllable(Script::Normal, "Q".to_string()), 2..3))
    );
    assert_eq!(lex.get_next_spanned_token(), None);
}

#[test]
fn test_glyph_tokenizer_question_mark() {
    let mut lex = GlyphTokenizer::new("?");
    assert_eq!(
        lex.get_next_spanned_token(),
        Some((Token::Query(Script::Normal), 0..1))
    );
}

#[derive(Debug, Clone)]
pub(crate) struct Lexer<'a> {
    lower: lower::LowerLexer<'a>,
    upper: Option<GlyphTokenizer<'a>>,
    upper_span: Option<Span>,
}

impl<'a> Lexer<'a> {
    pub(crate) fn new(input: &'a str) -> Lexer<'a> {
        Lexer {
            lower: lower::LowerLexer::new(input),
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

    pub(crate) fn spanned(&self) -> SpannedIter<'a> {
        let lexer: Lexer<'a> = self.clone();
        SpannedIter::new(lexer)
    }

    fn get_next(&mut self) -> Option<Token> {
        use lower::Lexeme;
        if let Some(upper_lexer) = self.upper.as_mut() {
            if let Some((r, span)) = upper_lexer.get_next_spanned_token() {
                self.upper_span = Some(span);
                return Some(r);
            } else {
                // We have no more input from the upper lexer,
                // fetch more from the lower one.
            }
        }

        // Fetch more text from the lower lexer.
        self.upper = None;
        self.upper_span = None;
        match self.lower.next() {
            Lexeme::EndOfInput => None,
            Lexeme::Tok(tok) => Some(tok),
            Lexeme::Text(text) => {
                let upper = GlyphTokenizer::new(text);
                self.upper = Some(upper);
                match self
                    .upper
                    .as_mut()
                    .expect("the option cannot be empty, we just filled it")
                    .get_next_spanned_token()
                {
                    Some((r, span)) => {
                        self.upper_span = Some(span);
                        Some(r)
                    }
                    None => None,
                }
            }
            Lexeme::Err(e) => Some(Token::Error(ErrorTokenKind::UnrecognisedGlyph(e))),
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.get_next()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct SpannedIter<'a> {
    lexer: Lexer<'a>,
}

impl<'a> SpannedIter<'a> {
    pub(crate) fn new(lexer: Lexer<'a>) -> SpannedIter<'a> {
        SpannedIter { lexer }
    }
}

impl Iterator for SpannedIter<'_> {
    type Item = (Token, Span);

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.lexer.next();
        token.map(|t| (t, self.lexer.span()))
    }
}
