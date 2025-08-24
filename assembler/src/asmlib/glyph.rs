//! This module implements the @...@ construct we use to represent in
//! Unicode input files the characters that ther TX-2 supports but
//! which Unicode does not.  For example, @sub_A@ which represents a
//! subscripted letter A.
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::hash::Hash;
use std::sync::OnceLock;

use base::charset::{Script, subscript_char, superscript_char};

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum Unrecognised {
    InvalidChar(char),
    UnrecognisedGlyph(String),
}

impl Display for Unrecognised {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unrecognised::InvalidChar(ch) => write!(
                f,
                "'{ch}' is not part of the TX-2 assembler's character set"
            ),
            Unrecognised::UnrecognisedGlyph(name) => {
                write!(f, "'@{name}@' is not a recognised glyph name")
            }
        }
    }
}

impl Error for Unrecognised {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Elevated<T> {
    inner: T,
    script: Script,
}

impl<T> Elevated<T> {
    pub(crate) fn script(&self) -> Script {
        self.script
    }

    pub(crate) fn get(&self) -> &T {
        &self.inner
    }
}

trait AsStr {
    fn as_str(&self) -> &str;
}

impl AsStr for &str {
    fn as_str(&self) -> &str {
        self
    }
}

impl AsStr for String {
    fn as_str(&self) -> &str {
        self.as_str()
    }
}

impl<T: AsStr> Display for Elevated<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.script {
            Script::Normal => write!(f, "{}", &self.inner.as_str()),
            Script::Super => {
                for ch in self.inner.as_str().chars() {
                    match superscript_char(ch) {
                        Ok(superchar) => {
                            f.write_char(superchar)?;
                        }
                        Err(_) => match glyph_of_char(ch) {
                            Ok(elevated_glyph) => {
                                let glyph = elevated_glyph.get();
                                if let Some(superchar) = glyph.superscript {
                                    f.write_char(superchar)?;
                                } else {
                                    write!(f, "@sup_{}@", glyph.name)?;
                                }
                            }
                            Err(_) => {
                                unimplemented!("superscript variant of {ch}")
                            }
                        },
                    }
                }
                Ok(())
            }
            Script::Sub => {
                for ch in self.inner.as_str().chars() {
                    match subscript_char(ch) {
                        Ok(subchar) => {
                            f.write_char(subchar)?;
                        }
                        Err(_) => match glyph_of_char(ch) {
                            Ok(elevated_glyph) => {
                                let glyph = elevated_glyph.get();
                                if let Some(superchar) = glyph.superscript {
                                    f.write_char(superchar)?;
                                } else {
                                    write!(f, "@sub_{}@", glyph.name)?;
                                }
                            }
                            Err(_) => {
                                unimplemented!("find subscript variant of {ch}")
                            }
                        },
                    }
                }
                Ok(())
            }
        }
    }
}

impl<T> From<(Script, T)> for Elevated<T> {
    fn from((script, inner): (Script, T)) -> Elevated<T> {
        Elevated { inner, script }
    }
}

pub(crate) fn elevate<T>(script: Script, inner: T) -> Elevated<T> {
    Elevated { script, inner }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Glyph {
    pub(crate) shape: GlyphShape,
    pub(crate) name: &'static str,
    pub(crate) normal: Option<char>,
    pub(crate) superscript: Option<char>,
    pub(crate) subscript: Option<char>,
    // When advance is false, this glyph does not advance the
    // carriage.  This appears to be true for character codes 0o12 and
    // 0o13 (in both upper and lower case).  We should provide a
    // reference for this, but just now I'm taking this info from the
    // code in base/src/charset.rs which deals with these character
    // codes.
    //
    // We try to use combining characters for these.
    pub(crate) advance: bool,
}

impl Glyph {
    pub(crate) fn shape(&self) -> GlyphShape {
        self.shape
    }

    pub(crate) fn get_char(&self, script: Script) -> Option<char> {
        match script {
            Script::Normal => self.normal,
            Script::Super => self.superscript,
            Script::Sub => self.subscript,
        }
    }
}

#[test]
fn test_subscript_char_agreement() {
    for g in ALL_GLYPHS {
        if let Some(ch) = g.normal
            && let Some(glyph_sub_ch) = g.subscript
            && let Ok(charset_sub_ch) = subscript_char(ch)
        {
            assert_eq!(
                glyph_sub_ch,
                charset_sub_ch,
                "glyph {g:?} maps {ch} to {glyph_sub_ch} ({}) but subscript_char maps it to {charset_sub_ch} ({})",
                glyph_sub_ch.escape_unicode(),
                charset_sub_ch.escape_unicode(),
            );
        }
    }
}

#[test]
fn test_superscript_char_agreement() {
    for g in ALL_GLYPHS {
        if let Some(ch) = g.normal
            && let Some(glyph_sup_ch) = g.superscript
            && let Ok(charset_sup_ch) = superscript_char(ch)
        {
            assert_eq!(
                glyph_sup_ch,
                charset_sup_ch,
                "glyph {g:?} maps {ch} to {glyph_sup_ch} ({}) but superscript_char maps it to {charset_sup_ch} ({})",
                glyph_sup_ch.escape_unicode(),
                charset_sup_ch.escape_unicode(),
            );
        }
    }
}

mod shape {
    #![allow(non_camel_case_types)]

    /// All character shapes in the character set table from page 2 of
    /// the documentation on the Lincoln Writer channels (65, 66).
    /// TX-2 Users Handbook, July 1961.
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
    pub(crate) enum GlyphShape {
        Digit0,
        Digit1,
        Digit2,
        Digit3,
        Digit4,
        Digit5,
        Digit6,
        Digit7,
        Digit8,
        Digit9,
        Underscore,
        Circle,
        A,
        B,
        C,
        D,
        E,
        F,
        G,
        H,
        I,
        J,
        K,
        L,
        M,
        N,
        O,
        P,
        Q,
        R,
        S,
        T,
        U,
        V,
        W,
        X,
        Y,
        Z,
        LeftParen,
        RightParen,
        Add,
        Minus,
        Comma,
        Dot,
        // No CARRIAGE RETURN
        Tab,
        Backspace,
        // No COLOR BLACK, SUPER, NORMAL, SUB, COLOR RED
        Space,
        // No WORD EXAM, LINE FEED DOWN, LINE FEED UP, LOWER CASE, UPPER
        // CASE, STOP, NULLIFY.
        Hand,
        Sigma,
        Pipe,
        DoublePipe,
        Solidus,
        Times,
        Hash,
        Arrow,
        LessThan,
        GreaterThan,
        Overbar,
        Square,
        n,
        SubsetOf,
        Or,
        q,
        Gamma,
        t,
        w,
        x,
        i,
        y,
        z,
        Query,
        Union,
        Intersection,
        j,
        k,
        Alpha,
        Delta,
        p,
        Epsilon,
        h,
        SupersetOf,
        Beta,
        And,
        Lambda,
        Tilde,
        LeftBrace,
        RightBrace,
        IdenticalTo, /* hamb */
        Equals,
        Apostrophe,
        Asterisk,
    }
}
pub(crate) use shape::GlyphShape;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub(crate) struct NotInCharacterSet(pub char);

impl Display for NotInCharacterSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Character '{}' is not in the TX-2's Lincoln Writer character set",
            self.0
        )
    }
}

impl Error for NotInCharacterSet {}

pub(crate) fn glyph_of_char(original: char) -> Result<Elevated<&'static Glyph>, Unrecognised> {
    let ch: char = canonicalise_char(original);
    let mapping = glyph_map();
    match mapping.get(&ch) {
        Some(elevated) => Ok(elevated),
        None => Err(Unrecognised::InvalidChar(original)),
    }
}

#[test]
fn test_space_is_normal() {
    match glyph_of_char(' ') {
        Ok(elevated) => {
            assert_eq!(elevated.script(), Script::Normal);
        }
        Err(e) => {
            panic!("unexpected failure to look up space: {e:?}");
        }
    }
}

impl TryFrom<char> for Elevated<&'static Glyph> {
    type Error = NotInCharacterSet;

    fn try_from(ch: char) -> Result<Self, Self::Error> {
        glyph_of_char(ch).map_err(|_| NotInCharacterSet(ch))
    }
}

#[test]
fn test_glyph_of_dot() {
    assert_eq!(glyph_of_char('.'), glyph_of_char('·'));
}

//const fn code_point_of_shape(g: GlyphShape) -> (LwCase, Unsigned6Bit) {
//     use base::charset::LwCase;
//     use base::Pu6, Unsigned6Bit};
//    // Information taken from the character set table from page 2 of
//    // the documentation on the Lincoln Writer channels (65, 66).
//    // TX-2 Users Handbook, July 1961.
//    const L: LwCase = LwCase::Lower;
//    const U: LwCase = LwCase::Upper;
//    match g {
//        GlyphShape::Digit0 => (L, u6!(0)),
//        GlyphShape::Digit1 => (L, u6!(1)),
//        GlyphShape::Digit2 => (L, u6!(2)),
//        GlyphShape::Digit3 => (L, u6!(3)),
//        GlyphShape::Digit4 => (L, u6!(4)),
//        GlyphShape::Digit5 => (L, u6!(5)),
//        GlyphShape::Digit6 => (L, u6!(6)),
//        GlyphShape::Digit7 => (L, u6!(7)),
//        GlyphShape::Digit8 => (L, u6!(0o10)),
//        GlyphShape::Digit9 => (L, u6!(0o11)),
//        GlyphShape::Underscore => (L, u6!(0o12)),
//        GlyphShape::Circle => (L, u6!(0o13)),
//        GlyphShape::A => (L, u6!(0o20)),
//        GlyphShape::B => (L, u6!(0o21)),
//        GlyphShape::C => (L, u6!(0o22)),
//        GlyphShape::D => (L, u6!(0o23)),
//        GlyphShape::E => (L, u6!(0o24)),
//        GlyphShape::F => (L, u6!(0o25)),
//        GlyphShape::G => (L, u6!(0o26)),
//        GlyphShape::H => (L, u6!(0o27)),
//        GlyphShape::I => (L, u6!(0o30)),
//        GlyphShape::J => (L, u6!(0o31)),
//        GlyphShape::K => (L, u6!(0o32)),
//        GlyphShape::L => (L, u6!(0o33)),
//        GlyphShape::M => (L, u6!(0o34)),
//        GlyphShape::N => (L, u6!(0o35)),
//        GlyphShape::O => (L, u6!(0o36)),
//        GlyphShape::P => (L, u6!(0o37)),
//        GlyphShape::Q => (L, u6!(0o40)),
//        GlyphShape::R => (L, u6!(0o41)),
//        GlyphShape::S => (L, u6!(0o42)),
//        GlyphShape::T => (L, u6!(0o43)),
//        GlyphShape::U => (L, u6!(0o44)),
//        GlyphShape::V => (L, u6!(0o45)),
//        GlyphShape::W => (L, u6!(0o46)),
//        GlyphShape::X => (L, u6!(0o47)),
//        GlyphShape::Y => (L, u6!(0o50)),
//        GlyphShape::Z => (L, u6!(0o51)),
//        GlyphShape::LeftParen => (L, u6!(0o52)),
//        GlyphShape::RightParen => (L, u6!(0o53)),
//        GlyphShape::Add => (L, u6!(0o54)),
//        GlyphShape::Minus => (L, u6!(0o55)),
//        GlyphShape::Comma => (L, u6!(0o56)),
//        GlyphShape::Dot => (L, u6!(0o57)),
//        GlyphShape::Tab => (L, u6!(0o61)),
//        GlyphShape::Backspace => (L, u6!(0o62)),
//        // 0o63 is COLOR BLACK
//        //
//        // 0o64 is SUPER
//        //
//        // 0o65 is NORMAL
//        //
//        // 0o66 is SUB
//        //
//        // 0o67 is COLOR RED
//        GlyphShape::Space => (L, u6!(0o70)),
//        // 0o71 is WORD EXAM
//        //
//        // 0o72 is LINE FEED DOWN
//        //
//        // 0o73 is LINE FEED UP
//        //
//        // 0o74 is LOWER CASE
//        //
//        // 0o75 is UPPER CASE
//        //
//        // 0o76 is STOP
//        //
//        // 0o77 is NULLIFY
//        GlyphShape::Hand => (U, u6!(0)),
//        GlyphShape::Sigma => (U, u6!(1)),
//        GlyphShape::Pipe => (U, u6!(2)),
//        GlyphShape::DoublePipe => (U, u6!(3)),
//        GlyphShape::Solidus => (U, u6!(4)),
//        GlyphShape::Times => (U, u6!(5)),
//        GlyphShape::Hash => (U, u6!(6)),
//        GlyphShape::Arrow => (U, u6!(7)),
//        GlyphShape::LessThan => (U, u6!(0o10)),
//        GlyphShape::GreaterThan => (U, u6!(0o11)),
//        GlyphShape::Overbar => (U, u6!(0o12)),
//        GlyphShape::Square => (U, u6!(0o13)),
//        // 0o14 is "READ IN"
//        //
//        // 0o15 is "BEGIN"
//        //
//        // 0o16 is "NO"
//        //
//        // 0o17 is "YES"
//        GlyphShape::n => (U, u6!(0o20)),
//        GlyphShape::SubsetOf => (U, u6!(0o21)),
//        GlyphShape::Or => (U, u6!(0o22)),
//        GlyphShape::q => (U, u6!(0o23)),
//        GlyphShape::Gamma => (U, u6!(0o24)),
//        GlyphShape::t => (U, u6!(0o25)),
//        GlyphShape::w => (U, u6!(0o26)),
//        GlyphShape::x => (U, u6!(0o27)),
//        GlyphShape::i => (U, u6!(0o30)),
//        GlyphShape::y => (U, u6!(0o31)),
//        GlyphShape::z => (U, u6!(0o32)),
//        GlyphShape::Query => (U, u6!(0o33)),
//        GlyphShape::Union => (U, u6!(0o34)),
//        GlyphShape::Intersection => (U, u6!(0o35)),
//        GlyphShape::j => (U, u6!(0o36)),
//        GlyphShape::k => (U, u6!(0o37)),
//        GlyphShape::Alpha => (U, u6!(0o40)),
//        GlyphShape::Delta => (U, u6!(0o41)),
//        GlyphShape::p => (U, u6!(0o42)),
//        GlyphShape::Epsilon => (U, u6!(0o43)),
//        GlyphShape::h => (U, u6!(0o44)),
//        GlyphShape::SupersetOf => (U, u6!(0o45)),
//        GlyphShape::Beta => (U, u6!(0o46)),
//        GlyphShape::And => (U, u6!(0o47)),
//        GlyphShape::Lambda => (U, u6!(0o50)),
//        GlyphShape::Tilde => (U, u6!(0o51)),
//        GlyphShape::LeftBrace => (U, u6!(0o52)),
//        GlyphShape::RightBrace => (U, u6!(0o53)),
//        GlyphShape::IdenticalTo => (U, u6!(0o54)), // @hamb@
//        GlyphShape::Equals => (U, u6!(0o55)),
//        GlyphShape::Apostrophe => (U, u6!(0o56)),
//        GlyphShape::Asterisk => (U, u6!(0o57)),
//        // Code points 0o60 to 0o77 are non-graphinc characters.
//    }
//}

const GDEF: Glyph = Glyph {
    shape: GlyphShape::Hand,
    name: "",
    normal: None,
    superscript: None,
    subscript: None,
    advance: true,
};

const ALL_GLYPHS: &[Glyph] = &[
    // Information taken from the character set table from page 2 of
    // the documentation on the Lincoln Writer channels (65, 66).
    // TX-2 Users Handbook, July 1961.
    Glyph {
        shape: GlyphShape::Digit0,
        name: "0",
        normal: Some('0'),
        superscript: Some('⁰'),
        subscript: Some('₀'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit1,
        name: "1",
        normal: Some('1'),
        subscript: Some('₁'),
        superscript: Some('¹'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit2,
        name: "2",
        normal: Some('2'),
        subscript: Some('₂'),
        superscript: Some('²'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit3,
        name: "3",
        normal: Some('3'),
        subscript: Some('₃'),
        superscript: Some('³'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit4,
        name: "4",
        normal: Some('4'),
        subscript: Some('₄'),
        superscript: Some('⁴'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit5,
        name: "5",
        normal: Some('5'),
        subscript: Some('₅'),
        superscript: Some('⁵'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit6,
        name: "6",
        normal: Some('6'),
        subscript: Some('₆'),
        superscript: Some('⁶'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit7,
        name: "7",
        normal: Some('7'),
        subscript: Some('₇'),
        superscript: Some('⁷'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit8,
        name: "8",
        normal: Some('8'),
        subscript: Some('₈'),
        superscript: Some('⁸'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Digit9,
        name: "9",
        normal: Some('9'),
        subscript: Some('₉'),
        superscript: Some('⁹'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Underscore,
        name: "underscore",
        // This character does not advance the carriage, so instead of
        // representing it with ASCII \x5F (underscore) we use a
        // combining low line.
        normal: Some('\u{0332}'), // U+0332, combining low line
        advance: false,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Circle,
        name: "circle",
        // U+25CB, Unicode white circle, '○', advances the cursor
        // position, which the Lincoln Writer code (0o13) doesn't do.
        // So we use a combining character.
        normal: Some('\u{20DD}'), // U+20DD, combining enclosing circle
        advance: false,
        ..GDEF
    },
    // 0o14 is "READ IN"
    //
    // 0o15 is "BEGIN"
    //
    // 0o16 is "NO"
    //
    // 0o17 is "YES"
    Glyph {
        shape: GlyphShape::A,
        name: "A",
        normal: Some('A'),
        superscript: Some('ᴬ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::B,
        name: "B",
        normal: Some('B'),
        superscript: Some('ᴮ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::C,
        name: "C",
        normal: Some('C'),
        superscript: Some('ꟲ'), // U+A7F2 (we don't use U+1D9C, that's the lower-case C)
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::D,
        name: "D",
        normal: Some('D'),
        superscript: Some('ᴰ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::E,
        name: "E",
        normal: Some('E'),
        superscript: Some('ᴱ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::F,
        name: "F",
        normal: Some('F'),
        superscript: Some('ꟳ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::G,
        name: "G",
        normal: Some('G'),
        superscript: Some('ᴳ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::H,
        name: "H",
        normal: Some('H'),
        superscript: Some('ᴴ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::I,
        name: "I",
        normal: Some('I'),
        superscript: Some('ᴵ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::J,
        name: "J",
        normal: Some('J'),
        superscript: Some('ᴶ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::K,
        name: "K",
        normal: Some('K'),
        superscript: Some('ᴷ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::L,
        name: "L",
        normal: Some('L'),
        superscript: Some('ᴸ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::M,
        name: "M",
        normal: Some('M'),
        superscript: Some('ᴹ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::N,
        name: "N",
        normal: Some('N'),
        superscript: Some('ᴺ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::O,
        name: "O",
        normal: Some('O'),
        superscript: Some('ᴼ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::P,
        name: "P",
        normal: Some('P'),
        superscript: Some('ᴾ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Q,
        name: "Q",
        normal: Some('Q'),
        superscript: Some('ꟴ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::R,
        name: "R",
        normal: Some('R'),
        superscript: Some('ᴿ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::S,
        name: "S",
        normal: Some('S'),
        // There is no Unicode superscript 'S', U+2E2 is a superscript 's'.
        superscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::T,
        name: "T",
        normal: Some('T'),
        superscript: Some('ᵀ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::U,
        name: "U",
        normal: Some('U'),
        superscript: Some('ᵁ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::V,
        name: "V",
        normal: Some('V'),
        superscript: Some('ⱽ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::W,
        name: "W",
        normal: Some('W'),
        superscript: Some('ᵂ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::X,
        name: "X",
        normal: Some('X'),
        // There is no superscript X in Unicode.
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Y,
        name: "Y",
        normal: Some('Y'),
        // There is no superscript Y in Unicode.
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Z,
        name: "Z",
        normal: Some('Z'),
        // There is no superscript Z in Unicode.
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::LeftParen,
        name: "lparen",
        normal: Some('('),
        subscript: Some('₍'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::RightParen,
        name: "rparen",
        normal: Some(')'),
        subscript: Some('₎'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Add,
        name: "add", // following sub.py
        normal: Some('+'),
        superscript: Some('⁺'),
        subscript: Some('₊'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Minus,
        name: "minus", // following sub.py
        normal: Some('-'),
        superscript: Some('⁻'),
        subscript: Some('₋'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Comma,
        name: "comma",
        normal: Some(','),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Dot,
        name: "dot",
        // This is a centre dot, not a period.  We use a centre dot so
        // that it's not confused with a subscript dot.
        normal: Some('\u{00B7}'), // ·

        // Using an ASCII full stop / period (".") would be too
        // confusing for the user, who (when preparing source code
        // input) might expect this to be interpreted as the
        // normal-script PERIOD.  So for subscript we instead use
        // U+2024, "One Dot Leader".
        subscript: Some('\u{2024}'), // "․" (not ASCII ".")
        superscript: None,
        ..GDEF
    },
    // CARRIAGE RETURN is missing.
    Glyph {
        shape: GlyphShape::Tab,
        name: "tab",
        normal: Some('\t'),
        ..GDEF
    },
    Glyph {
        // backspace is used in some combining-character symexes.
        shape: GlyphShape::Backspace,
        name: "backspace",
        normal: None, // better to say @backspace@.
        ..GDEF
    },
    // 0o63 is COLOR BLACK
    //
    // 0o64 is SUPER
    //
    // 0o65 is NORMAL
    //
    // 0o66 is SUB
    //
    // 0o67 is COLOR RED
    Glyph {
        shape: GlyphShape::Space,
        name: "space",
        normal: Some(' '),
        subscript: Some(' '),
        superscript: Some(' '),
        ..GDEF
    },
    // 0o71 is WORD EXAM
    //
    // 0o72 is LINE FEED DOWN
    //
    // 0o73 is LINE FEED UP
    //
    // 0o74 is LOWER CASE
    //
    // 0o75 is UPPER CASE
    //
    // 0o76 is STOP
    //
    // 0o77 is NULLIFY
    //
    //
    // Right-hand column of the character set table follows.
    Glyph {
        shape: GlyphShape::Hand,
        name: "hand",
        normal: Some('☛'), // U+261B
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Sigma,
        name: "sigma",
        normal: Some('Σ'), // U+03A3
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Pipe,
        name: "pipe",
        normal: Some('|'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::DoublePipe,
        name: "doublepipe",
        normal: Some('‖'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Solidus,
        name: "solidus", // better known as "slash".
        normal: Some('/'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Times,
        name: "times",
        normal: Some('×'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Hash,
        name: "hash",
        normal: Some('#'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Arrow,
        // arr not arrow to follow Jurij's sub.py
        name: "arr",
        normal: Some('\u{2192}'), // →
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::LessThan,
        name: "lessthan",
        normal: Some('<'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::GreaterThan,
        name: "greaterthan",
        normal: Some('>'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Overbar,
        name: "overbar",
        // This character does not advance the carriage, so we use a
        // combining character for it.
        normal: Some('\u{0305}'), // U+0305, combining overline
        superscript: None,
        subscript: None,
        advance: false,
    },
    Glyph {
        shape: GlyphShape::Square,
        name: "square",
        // This character does not advance the carriage, so instead of
        // using a character like U+25A1 ('□'), we use a combining
        // character.
        normal: Some('\u{20DE}'), // U+20DE, combining enclosing square
        subscript: None,
        superscript: None,
        advance: false,
    },
    // 0o14 is "READ IN"
    //
    // 0o15 is "BEGIN"
    //
    // 0o16 is "NO"
    //
    // 0o17 is "YES"
    Glyph {
        shape: GlyphShape::n,
        name: "n",
        normal: Some('n'),
        superscript: Some('ⁿ'),
        subscript: Some('ₙ'), // U+2099
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::SubsetOf,
        name: "subsetof",
        normal: Some('\u{2282}'), // Subset of, ⊂
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Or,
        name: "or",
        normal: Some('∨'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::q,
        name: "q",
        normal: Some('q'),
        superscript: None,
        // U+107A5 is a subscript q, but this is not widely supported,
        // so we don't use it.  Instead the user should use "@sub_q@".
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Gamma,
        name: "gamma",
        normal: Some('γ'), // U+03B3, Greek small letter gamma
        superscript: Some('ᵞ'),
        subscript: Some('ᵧ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::t,
        name: "t",
        normal: Some('t'),
        superscript: Some('ᵗ'), // U+1D57
        subscript: Some('ₜ'),   // U+209C
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::w,
        name: "w",
        normal: Some('w'),
        superscript: Some('ʷ'),
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::x,
        name: "x",
        normal: Some('x'),
        superscript: Some('ˣ'),
        subscript: Some('ₓ'), // U+2093
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::i,
        name: "i",
        normal: Some('i'),
        superscript: Some('ⁱ'),
        subscript: Some('ᵢ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::y,
        name: "y",
        normal: Some('y'),
        superscript: Some('ʸ'),
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::z,
        name: "z",
        normal: Some('z'),
        subscript: None,
        superscript: Some('ᶻ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Query, // A question mark.
        name: "?",
        normal: Some('?'),
        superscript: Some('ˀ'), // dot is missing but it's the best we can do.
        // U+FE56, "Small Question Mark" is not really a subscript
        // character, but let's try it out.
        subscript: Some('﹖'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Union,
        name: "union",
        normal: Some('∪'),
        superscript: None,
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Intersection,
        name: "intersection",
        normal: Some('\u{2229}'),
        subscript: None,
        superscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::j,
        name: "j",
        normal: Some('j'),
        superscript: Some('ʲ'), // U+02B2
        subscript: Some('ⱼ'),   // U+2C7C
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::k,
        name: "k",
        normal: Some('k'),
        superscript: Some('ᵏ'),
        subscript: Some('ₖ'), // U+2096
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Alpha,
        name: "alpha",
        normal: Some('α'), // U+03B1, alpha
        // this is actually a Latin superscript alpha, but it will normally look the same.
        superscript: Some('ᵅ'),
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Delta,
        name: "delta",
        normal: Some('Δ'), // U+0395, capital delta
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::p,
        name: "p",
        normal: Some('p'),
        superscript: Some('ᵖ'),
        subscript: Some('ₚ'), // U+209A
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Epsilon,
        name: "eps",
        normal: Some('ε'),      // U+03B5, Epsilon (not ∈, Element of)
        superscript: Some('ᵋ'), // U+1D4B
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::h,
        name: "h",
        normal: Some('h'),
        superscript: Some('ʰ'),
        subscript: Some('ₕ'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::SupersetOf,
        name: "sup",       // name aligns with Jurij's sub.py
        normal: Some('⊃'), // U+2283, superset of
        superscript: None,
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Beta,
        name: "beta",
        normal: Some('β'),      // U+03B2, Greek beta symbol
        superscript: Some('ᵝ'), // U+1D5D
        subscript: Some('ᵦ'),   // U+1D66
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::And,
        name: "and",
        normal: Some('∧'), // U+2227, Logical And
        superscript: None,
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Lambda,
        name: "lambda",
        normal: Some('λ'), // U+3BB, Greek letter lambda
        superscript: None,
        subscript: None,
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Tilde,
        name: "tilde",
        normal: Some('~'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::LeftBrace,
        name: "leftbrace",
        normal: Some('{'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::RightBrace,
        name: "rightbrace",
        normal: Some('}'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::IdenticalTo,
        name: "hamb",      // following Jurij's sub.py
        normal: Some('≡'), // U+2261, Identical to (Jurij used ☰, U+2630, Trigram For Heaven)
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Equals,
        name: "equals",
        normal: Some('='),
        subscript: Some('₌'),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Apostrophe,
        name: "apostrophe",
        normal: Some('\''),
        ..GDEF
    },
    Glyph {
        shape: GlyphShape::Asterisk,
        name: "asterisk",
        normal: Some('*'),
        subscript: None,
        superscript: None,
        ..GDEF
    },
    // Code points 0o60 to 0o77 are non-graphinc characters.
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GlyphMapByChar {
    mapping: HashMap<char, Elevated<&'static Glyph>>,
}

static GLYPH_MAP_BY_CHAR: OnceLock<GlyphMapByChar> = OnceLock::new();

impl Default for GlyphMapByChar {
    fn default() -> Self {
        let mut mapping = HashMap::new();
        for g in ALL_GLYPHS {
            for script in [Script::Sub, Script::Super, Script::Normal] {
                if g.normal == Some(' ') && script != Script::Normal {
                    // Note that the space character has the same
                    // representation in normal script, superscript
                    // and subscript.  We have a convention that space
                    // is always deemed to be in normal script.
                    continue;
                }
                if let Some(key) = g.get_char(script) {
                    let value = elevate(script, g);
                    if let Some(prev) = mapping.insert(key, value) {
                        panic!("duplicate glyph mapping for character '{key}': {g:?} and {prev:?}");
                    }
                }
            }
        }
        Self { mapping }
    }
}

impl GlyphMapByChar {
    fn get(&self, ch: &char) -> Option<Elevated<&'static Glyph>> {
        self.mapping.get(ch).copied()
    }
}

pub(crate) fn glyph_map() -> &'static GlyphMapByChar {
    GLYPH_MAP_BY_CHAR.get_or_init(GlyphMapByChar::default)
}

fn canonicalise_char(ch: char) -> char {
    match ch {
        // We don't convert U+A7F2 (ꟲ) to U+1D9C because the former is
        // a majuscule (captial) letter and the latter is a minuscule
        // (lower-case) letter.
        '.' => '\u{00B7}', // . -> ·

        // The TX-2 character set doesn't include ':', but some of the
        // older sources use ':' to signal that the hold bit should be
        // set in an instruction.  In the Users Handbook (in 1961 at
        // least) this function is performed by 'h'.
        ':' => 'h',
        _ => ch,
    }
}

pub(crate) fn name_from_glyph(mut ch: char) -> Option<&'static str> {
    ch = canonicalise_char(ch);
    ALL_GLYPHS
        .iter()
        .find(|g| g.normal == Some(ch))
        .map(|g| g.name)
}

pub(crate) fn glyph_from_name(name: &str) -> Option<Elevated<&'static Glyph>> {
    let (script, glyph_base_name) = if let Some(suffix) = name.strip_prefix("sub_") {
        (Script::Sub, suffix)
    } else if let Some(suffix) = name.strip_prefix("sup_") {
        (Script::Super, suffix)
    } else {
        (Script::Normal, name)
    };
    ALL_GLYPHS
        .iter()
        .find(|g| g.name == glyph_base_name)
        .map(|g| elevate(script, g))
}

/// Specified in Users Handbook section 6-2.3 item 6.
pub(crate) fn is_allowed_in_symex(g: GlyphShape) -> bool {
    match g {
        GlyphShape::Digit0 |
        GlyphShape::Digit1 |
        GlyphShape::Digit2 |
        GlyphShape::Digit3 |
        GlyphShape::Digit4 |
        GlyphShape::Digit5 |
        GlyphShape::Digit6 |
        GlyphShape::Digit7 |
        GlyphShape::Digit8 |
        GlyphShape::Digit9 |
        GlyphShape::A |
        GlyphShape::B |
        GlyphShape::C |
        GlyphShape::D |
        GlyphShape::E |
        GlyphShape::F |
        GlyphShape::G |
        GlyphShape::H |
        GlyphShape::I |
        GlyphShape::J |
        GlyphShape::K |
        GlyphShape::L |
        GlyphShape::M |
        GlyphShape::N |
        GlyphShape::O |
        GlyphShape::P |
        GlyphShape::Q |
        GlyphShape::R |
        GlyphShape::S |
        GlyphShape::T |
        GlyphShape::U |
        GlyphShape::V |
        GlyphShape::W |
        GlyphShape::X |
        GlyphShape::Y |
        GlyphShape::Z |
        GlyphShape::Alpha|
        GlyphShape::Beta |
        GlyphShape::Gamma |
        GlyphShape::Delta  |
        GlyphShape::Epsilon |
        GlyphShape::Lambda |
        // Note: h is not allowed.
        GlyphShape::i |
        GlyphShape::j |
        GlyphShape::k |
        GlyphShape::n |
        GlyphShape::p |
        GlyphShape::q |
        GlyphShape::t |
        GlyphShape::w |
        GlyphShape::x |
        GlyphShape::y |
        GlyphShape::z |
        GlyphShape::Dot |
        GlyphShape::Apostrophe |
        GlyphShape::Underscore |
        GlyphShape::Overbar |
        GlyphShape::Square |
        GlyphShape::Circle => true,
        GlyphShape::Space => {
            // Space bar is allowed in a symex, per section 6-2.3.
            // But that doesn't necessarily mean that other space
            // characters are.  However, we treat space and tab the
            // same, and don't include them in the symex syllable
            // token (instead we join symex syllables together in the
            // parser).
            true
        }
        _ => false,
    }
}
