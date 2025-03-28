//! Character set conversions.
//!
//! Unicode to and from Lincoln Writer characters.  No support for
//! colour shifting.  Limited support for overstrke characters (such
//! as the LW circle (0o73 upper case) overstruck with logical or
//! (0o22 lower case); these are currently supported only as Unicode
//! combining characters.
//!
//! The Xerox printer uses a different character set but this code
//! doesn't currently include a mapping for it.
//!
//! Controlling documentation:
//!
//! - [Table 7-6 in the User
//!   Handbook](https://archive.org/details/tx-2-users-handbook-nov-63/page/n195)
//!   describes the Lincoln Writer codes.
//! - [Table 7-5 in the User
//!   Handbook](https://archive.org/details/tx-2-users-handbook-nov-63/page/n195) describes the character codes for the Xerox printer.  This code doesn't yet implement this mapping.
//! - [The Lincoln Keyboard - a typewriter keyboard designed for
//!   computers imput flexibility. A. Vanderburgh.  Communications of
//!   the ACM, Volume 1, Issue 7, July
//!   1958.](https://dl.acm.org/doi/10.1145/368873.368879) describes
//!   the Lincoln Writer keyboard and the fact that some characters
//!   do not advance the print carriage.
//! - The Lincoln Lab Division 6 Quarterly Progress Report (15 June
//!   1958).
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter};

use super::{u6, Unsigned6Bit};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy)]
pub struct NoSubscriptKnown(char);

impl Display for NoSubscriptKnown {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "no subscript mapping is yet implemented for '{}'",
            self.0
        )
    }
}

impl Error for NoSubscriptKnown {}

pub fn subscript_char(ch: char) -> Result<char, NoSubscriptKnown> {
    match ch {
        '0' => Ok('\u{2080}'), // ₀
        '1' => Ok('\u{2081}'), // ₁
        '2' => Ok('\u{2082}'), // ₂
        '3' => Ok('\u{2083}'), // ₃
        '4' => Ok('\u{2084}'), // ₄
        '5' => Ok('\u{2085}'), // ₅
        '6' => Ok('\u{2086}'), // ₆
        '7' => Ok('\u{2087}'), // ₇
        '8' => Ok('\u{2088}'), // ₈
        '9' => Ok('\u{2089}'), // ₉
        '+' => Ok('\u{208A}'), // '₊'
        '-' => Ok('\u{208B}'), // ₋
        '.' => Ok('.'),        // there appears to be no subscript version
        _ => Err(NoSubscriptKnown(ch)),
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct NoSuperscriptKnown(char);

impl Display for NoSuperscriptKnown {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "no superscript mapping is yet implemented for '{}'",
            self.0
        )
    }
}

impl Error for NoSuperscriptKnown {}

pub fn superscript_char(ch: char) -> Result<char, NoSuperscriptKnown> {
    match ch {
        '0' => Ok('\u{2070}'),
        '1' => Ok('\u{00B9}'),
        '2' => Ok('\u{00B2}'),
        '3' => Ok('\u{00B3}'),
        '4' => Ok('\u{2074}'),
        '5' => Ok('\u{2075}'),
        '6' => Ok('\u{2076}'),
        '7' => Ok('\u{2077}'),
        '8' => Ok('\u{2078}'),
        '9' => Ok('\u{2079}'),
        'A' => Ok('ᴬ'),
        'B' => Ok('ᴮ'),
        'C' => Ok('\u{A7F2}'),
        'D' => Ok('ᴰ'),
        'E' => Ok('ᴱ'),
        'F' => Ok('\u{A7F3}'),
        'G' => Ok('ᴳ'),
        'H' => Ok('ᴴ'),
        'I' => Ok('ᴵ'),
        'J' => Ok('ᴶ'),
        'K' => Ok('ᴷ'),
        'L' => Ok('ᴸ'),
        'M' => Ok('ᴹ'),
        'N' => Ok('ᴺ'),
        'O' => Ok('ᴼ'),
        'P' => Ok('ᴾ'),
        'Q' => Ok('\u{A7F4}'),
        'R' => Ok('ᴿ'),
        // There is no Unicode superscript 'S', U+2E2 is a superscript 's'.
        'T' => Ok('ᵀ'),
        'U' => Ok('ᵁ'),
        'V' => Ok('ⱽ'),
        'W' => Ok('ᵂ'),
        'X' => Ok('\u{2093}'),
        'Y' | 'Z' => Err(NoSuperscriptKnown(ch)),
        '+' => Ok('\u{207A}'),
        '-' => Ok('\u{207B}'),
        _ => Err(NoSuperscriptKnown(ch)),
    }
}

impl Display for LincolnToUnicodeStrictConversionFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            LincolnToUnicodeStrictConversionFailure::CannotSubscript(
                _,
                LincolnChar::Unprintable(n),
            )
            | LincolnToUnicodeStrictConversionFailure::CannotSuperscript(
                _,
                LincolnChar::Unprintable(n),
            ) => {
                write!(
                    f,
                    "cannot convert code {:#o} from Lincoln Writer character set to Unicode, because it has no printable representation",
                    n
                )
            }
            LincolnToUnicodeStrictConversionFailure::CannotSubscript(
                u,
                LincolnChar::UnicodeBaseChar(ch),
            ) => {
                write!(
                    f,
                    "cannot convert {:#o} from Lincoln Writer character set to Unicode, because Unicode has no subscript form of '{}'",
                    u,
                    ch
                )
            }
            LincolnToUnicodeStrictConversionFailure::CannotSuperscript(
                u,
                LincolnChar::UnicodeBaseChar(ch),
            ) => {
                write!(
                    f,
                    "cannot convert {:#o} from Lincoln Writer character set to Unicode, because Unicode has no superscript form of '{}'",
                    u,
                    ch
                )
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Script {
    Normal,
    Super,
    Sub,
}

impl Script {
    pub fn shift(&self) -> u32 {
        match self {
            Script::Super => 30, // This is a config value.
            Script::Sub => 18,   // This is an index value
            Script::Normal => 0, // e.g. an address value
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Colour {
    Black,
    Red,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum LwCase {
    Lower,
    Upper,
}

impl LwCase {
    fn as_str(&self) -> &'static str {
        match self {
            LwCase::Lower => "lower",
            LwCase::Upper => "upper",
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LincolnState {
    pub script: Script,
    pub case: LwCase,
    pub colour: Colour,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LincolnStateTextInfo {
    pub script: &'static str,
    pub case: &'static str,
    pub colour: &'static str,
}

impl Default for LincolnState {
    fn default() -> Self {
        // Carriage return sets the LW to lower case and normal script
        // so those are the defaults.  See pages 4-37 to 4-42 of the
        // User Handbook.
        Self {
            script: Script::Normal,
            case: LwCase::Lower,
            colour: Colour::Black,
        }
    }
}

impl LincolnState {
    /// CARRIAGE RETURN also has the side effect of setting the
    /// "keyboard" to lower case and "normal script".  This statement
    /// appears in the description if the Lincoln Writer in the Users
    /// Handbook (page 4-37 and again on 4-41).  The document
    /// explicitly states that a write of this code (from the TX-2 to
    /// the Lincoln Writer) also affects the state of the keyboard. On
    /// page 4-41 the document also states that carriage return
    /// written by the TX-2 to the Lincoln Writer has the same effect.
    ///
    /// XXX: both of the previous two statements describe the TX2->LW
    /// direction, re-check the documentation for what happens in the
    /// other direction.
    fn on_carriage_return(&mut self) {
        self.script = Script::Normal;
        self.case = LwCase::Lower;
    }
}

impl From<&LincolnState> for LincolnStateTextInfo {
    fn from(state: &LincolnState) -> LincolnStateTextInfo {
        LincolnStateTextInfo {
            script: match state.script {
                Script::Normal => "Normal script",
                Script::Super => "Superscript",
                Script::Sub => "Subscript",
            },
            case: state.case.as_str(),
            colour: match state.colour {
                Colour::Black => "Black",
                Colour::Red => "Red",
            },
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LincolnChar {
    /// There is a Unicode character which we're trying to print (but
    /// this actual Unicode character may be incorrect, i.e. it is
    /// normal-script when the fully-described character is actually
    /// superscript).
    UnicodeBaseChar(char),
    /// Unprintable chars include YES, READ IN, BEGIN, NO, and so forth.
    Unprintable(Unsigned6Bit),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct DescribedChar {
    /// The actual character we're trying to print.  The `attributes`
    /// attribute specifies whether this is a subscript, superscript
    /// or normal character, and what colour it is.
    pub base_char: LincolnChar,
    /// If the character has a direct Unicode translation, that is in
    /// unicode_representation.  Some characters, for example
    /// superscript Y, have no Unicode representation.
    pub unicode_representation: Option<char>,
    /// Specifies whether the character is upper-case, lower-case
    /// (both as understood in terms of normal typography, i.e. "A" is
    /// upper-case), whether it is subscript, superscript, or normal,
    /// and what colour it is.
    pub attributes: LincolnState,
    /// When advance is `true`, printing this character should advance
    /// the printing position.
    pub advance: bool,
    /// Indicates whether the label on the Lincoln Writer keyboard
    /// is the same as the Unicode representation.
    pub label_matches_unicode: bool,
}

fn unprintable(c: Unsigned6Bit, state: LincolnState) -> DescribedChar {
    DescribedChar {
        base_char: LincolnChar::Unprintable(c),
        unicode_representation: None,
        attributes: state,
        advance: false,
        label_matches_unicode: false,
    }
}
fn bycase(lower: char, upper: char, state: &LincolnState) -> Option<char> {
    Some(match state.case {
        LwCase::Upper => upper,
        LwCase::Lower => lower,
    })
}

/// Perform any state changes implied by a character code.
pub fn lincoln_writer_state_update(lin_ch: Unsigned6Bit, state: &mut LincolnState) {
    match u8::from(lin_ch) {
        0o60 => {
            state.on_carriage_return();
        }
        0o63 => {
            state.colour = Colour::Black;
        }
        0o64 => {
            state.script = Script::Super;
        }
        0o65 => {
            state.script = Script::Normal;
        }
        0o66 => {
            state.script = Script::Sub;
        }
        0o67 => {
            state.colour = Colour::Red;
        }
        0o74 => {
            state.case = LwCase::Lower;
        }
        0o75 => {
            state.case = LwCase::Upper;
        }
        _ => (),
    }
}

/// Convert a Lincoln Writer character to a description which can
/// be used to print a Unicode approximation of it.
///
/// In the success case we return None when the only effect of this
/// Lincoln Writer character is to change mode (e.g. to upper case)
/// and `Some(DescribedChar)` when there is something to print.  In
/// the `Some(DescribedChar)` case, the DescribedChar instance
/// describes what is to be printed and provides a Unicode
/// approximation to it, if there is one.
///
/// The character codes are shown in table 7-6 in the Users handbook.
/// This shows two columns of characters for each code.  Somewhat
/// counterintuitively, I believe that the left-hand column is "lower
/// case".  hence for code 027 for example, 'H' is "lower case" and
/// "x" is upper case.   I believe this for the following reasons:
///
/// 1. because the LW defaults to "lower case" after Carriage Return,
///    and we'd expect this to correspond to the most commonly used
///    characters.  The block capitals and digits are all in the
///    left-hand column.  There is a complete set of A-Z but there is
///    not a complete set of a-z.
/// 2. The layout of the Lincoln Writer keyboard is consistent with
///    this idea.  There are two keyboards, an upper and a lower.  The
///    lower keyboard contains block capitals and digits, and the
///    upper keyboard contains minuscule letters (e.g. "q", "k").
///    This idea is based on the Lincoln Writer diagram on page 24 of
///    the Lincoln Lab Division 6 Quarterly Progress Report (15 June
///    1958).
pub fn lincoln_char_to_described_char(
    lin_ch: Unsigned6Bit,
    state: &mut LincolnState,
) -> Option<DescribedChar> {
    lincoln_writer_state_update(lin_ch, state);
    let advance: bool = lin_ch != 0o12 && lin_ch != 0o13;
    let by_case = |lower, upper: char| -> Option<char> { bycase(lower, upper, state) };
    let base_char: Option<char> = match u8::from(lin_ch) {
        0o00 => by_case('0', '☛'), // \U261B, black hand pointing right
        0o01 => by_case('1', 'Σ'), // \U03A3, Greek capital letter Sigma
        0o02 => by_case('2', '|'),
        0o03 => by_case('3', '‖'), // \U2016, double vertical line
        0o04 => by_case('4', '/'),
        0o05 => by_case('5', '×'), // multiplication sign (U+00D7)
        0o06 => by_case('6', '#'),
        0o07 => by_case('7', '→'), // rightwards arrow (U+2192)
        0o10 => by_case('8', '<'),
        0o11 => by_case('9', '>'),
        0o12 => {
            // These characters do not advance the carriage.  Hence we
            // translate the lower-case 0o12 into Unicode 'combining
            // low line' rather than underscore.
            by_case(
                '\u{0332}', // combining low line
                '\u{0305}', // combining overline
            )
        }
        0o13 => {
            // These characters do not advance the carriage.
            by_case(
                '\u{20DD}', // combining enclosing circle
                '\u{20DE}', // combining enclosing square
            )
        }
        0o14..=0o17 => return Some(unprintable(lin_ch, *state)), // "READ IN", "BEGIN", "NO", "YES"
        0o20 => by_case('A', 'n'),
        0o21 => by_case('B', '⊂'), // Subset of (U+2282)
        0o22 => by_case('C', '∨'), // Logical or (U+2228)
        0o23 => by_case('D', 'q'),
        0o24 => by_case('E', 'γ'), // Greek small letter gamma (U+03B3)
        0o25 => by_case('F', 't'),
        0o26 => by_case('G', 'w'),
        0o27 => by_case('H', 'x'),
        0o30 => by_case('I', 'i'),
        0o31 => by_case('J', 'y'),
        0o32 => by_case('K', 'z'),
        0o33 => by_case('L', '?'),
        0o34 => by_case('M', '∪'), // Union, U+222A
        0o35 => by_case('N', '∩'), // Intersection, U+2229
        0o36 => by_case('O', 'j'),
        0o37 => by_case('P', 'k'),
        0o40 => by_case('Q', 'α'), // Greek small letter alpha, U+03B1
        0o41 => by_case('R', 'Δ'), // Greek capital delta, U+0394
        0o42 => by_case('S', 'p'),
        // Previously we thought that the right-hand character was ∈
        // (Element of, U+2208), but seeing the greek letters grouped
        // in section 6-2.3 ("RULES FOR SYMEX FORMATION") shows that
        // this is a greek letter, epsilon.
        0o43 => by_case('T', 'ε'), // Epsilon
        0o44 => by_case('U', 'h'),
        0o45 => by_case('V', '⊃'), // Superset of, U+2283
        0o46 => by_case('W', 'β'), // Greek beta symbol, U+03B2
        0o47 => by_case('X', '∧'), // Logical And U+2227
        0o50 => by_case('Y', 'λ'), // Greek small letter lambda, U+03BB
        0o51 => by_case('Z', '~'),
        0o52 => by_case('(', '{'),
        0o53 => by_case(')', '}'),
        0o54 => by_case('+', '≡'), // Identical to, U+2261
        0o55 => by_case('-', '='),
        0o56 => by_case(',', '\u{0027}'), // Single apostrophe, U+0027
        0o57 => by_case('.', '*'),
        0o60 => {
            // Despite the state change, on input only the 060 is
            // emitted by the Lincoln Writer.  Carriage Return also
            // advances the paper (i.e. performs a line feed).
            Some('\r') // state change was already done.
        }
        0o61 => Some('\t'),
        0o62 => Some('\u{0008}'), // backspace, U+0008
        0o63 => None,             // COLOR BLACK; state change already done
        0o64 => None,             // SUPER; state change already done
        0o65 => None,             // NORMAL; state change already done
        0o66 => None,             // SUB; state change already done
        0o67 => None,             // COLOR RED; state change already done
        0o70 => Some(' '),        // space
        0o71 => return Some(unprintable(lin_ch, *state)), // WORD EXAM
        0o72 => Some('\n'),       // LINE FEED
        0o73 => Some('\u{008D}'), // Reverse line feed
        0o74 => None,             // LOWER CASE; state change already done
        0o75 => None,             // UPPER CASE; state change already done
        0o76 => return Some(unprintable(lin_ch, *state)), // STOP
        0o77 => {
            // Supposedly NULLIFY.  It's used on paper tape as a way
            // to delete a character. Punching out all the bit holes
            // changes the code to 0o77 and applications supposedly
            // ignore these characters on the basis that the user has
            // deleted them.
            //
            // For example suppose the user presses 'Q' followed by
            // 'DELETE'.
            //
            // In off-line mode, where the LW is being used only to
            // prepare a paper tape the TX-2 doesn't directly see the
            // codes.  The tape will be punched with code 0o40
            // (representing 'Q') and then the same location will be
            // re-punched with 0o77 (effectively deleting the 'Q').
            // Later when the paper tape is read, the only code the
            // machine will see is the 0o77 (assuming that there was
            // no previous upper/lower case change code).
            //
            // In on-line mode the TX-2 will see two codes, 0o40
            // followed by 0o77; the Lincoln Writer cannot "un-send"
            // the 0o40. This is the same behaviour as modern
            // computers have for DELETE.  Therefore we map this code
            // to ASCII DEL.
            Some('\u{007F}')
        }
        _ => unreachable!("All Unsigned6Bit values should have been handled"),
    };

    if let Some(base) = base_char {
        let display = match state.script {
            Script::Normal => Some(base),
            Script::Sub => subscript_char(base).ok(),
            Script::Super => superscript_char(base).ok(),
        };
        // Non-carriage-advancing characters don't strictly match the
        // key label, because we represent them as combining
        // characters and so there's a space in the key label too.
        let label_matches_unicode = advance
            && match display {
                None => false,
                Some(' ') => {
                    // Here the mapping is to ' ' but in the keyboard
                    // implementation, the space bar's label is the
                    // zero-length string.
                    false
                }
                Some('\n' | '\r' | '\t' | '\u{0008}' | '\u{008D}' | '\u{007F}') => false,
                Some('☛') => {
                    // On the keyboard we label this with '☞' (Unicode
                    // U+261E) instead of '☛'(U+261B) because the
                    // outline looks more readable on the drawn
                    // keyboard.  So these don't match.
                    false
                }
                Some(_) => true,
            };
        Some(DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar(base),
            unicode_representation: display,
            attributes: *state,
            advance,
            label_matches_unicode,
        })
    } else {
        None
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LincolnToUnicodeStrictConversionFailure {
    CannotSubscript(Unsigned6Bit, LincolnChar),
    CannotSuperscript(Unsigned6Bit, LincolnChar),
}

/// Convert a stream of Lincoln Writer codes to a Unicode string.
/// Lincoln Writer codes are 6 bits, and these are assumed to be in
/// the lower 6 bits of the input values.
pub fn lincoln_to_unicode_strict(
    input: &[Unsigned6Bit],
) -> Result<String, LincolnToUnicodeStrictConversionFailure> {
    let mut result = String::with_capacity(input.len());
    let mut state: LincolnState = LincolnState::default();
    for byte in input.iter() {
        match lincoln_char_to_described_char(*byte, &mut state) {
            Some(DescribedChar {
                base_char: LincolnChar::Unprintable(_),
                ..
            }) => {
                // Codes like "YES" are handled here.  When printed on
                // the Lincoln Writer, no character is printed (though
                // some time is taken to not print it).
                //
                // We do nothing (i.e. generate no error and no output
                // character).
            }
            Some(DescribedChar {
                base_char: _,
                unicode_representation: Some(display),
                attributes: _,
                advance: _,
                label_matches_unicode: _,
            }) => {
                result.push(display);
            }
            Some(DescribedChar {
                base_char,
                unicode_representation: None,
                attributes,
                advance: _,
                label_matches_unicode: _,
            }) => match attributes.script {
                Script::Normal => unreachable!(),
                Script::Sub => {
                    return Err(LincolnToUnicodeStrictConversionFailure::CannotSubscript(
                        *byte, base_char,
                    ));
                }
                Script::Super => {
                    return Err(LincolnToUnicodeStrictConversionFailure::CannotSuperscript(
                        *byte, base_char,
                    ));
                }
            },
            None => (),
        }
    }
    Ok(result)
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct LincChar {
    state: LincolnState,
    value: Unsigned6Bit,
}

pub struct UnicodeToLincolnMapping {
    m: HashMap<char, LincChar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnicodeToLincolnConversionFailure {
    NoMapping(char),
}

impl Display for UnicodeToLincolnConversionFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            UnicodeToLincolnConversionFailure::NoMapping(ch) => {
                write!(
                    f,
                    "there is no mapping for '{}' from Unicode to Lincoln Writer character set",
                    ch,
                )
            }
        }
    }
}

impl UnicodeToLincolnMapping {
    pub fn new() -> UnicodeToLincolnMapping {
        let mut m: HashMap<char, LincChar> = HashMap::new();
        for script in [Script::Normal, Script::Super, Script::Sub] {
            for case in [LwCase::Lower, LwCase::Upper] {
                for value in 0..=0o77 {
                    if let Ok(ch) = Unsigned6Bit::try_from(value) {
                        let mut state = LincolnState {
                            script,
                            case,
                            colour: Colour::Black,
                        };
                        if let Some(DescribedChar {
                            base_char: _,
                            unicode_representation: Some(display),
                            attributes: _,
                            advance: _,
                            label_matches_unicode: _,
                        }) = lincoln_char_to_described_char(ch, &mut state)
                        {
                            m.insert(display, LincChar { state, value: ch });
                        }
                    } else {
                        continue;
                    }
                }
            }
        }
        UnicodeToLincolnMapping { m }
    }

    pub fn to_lincoln(
        &self,
        s: &str,
    ) -> Result<Vec<Unsigned6Bit>, UnicodeToLincolnConversionFailure> {
        let mut result: Vec<Unsigned6Bit> = Vec::with_capacity(s.len());
        let mut current_case: Option<LwCase> = None;
        let mut current_script: Option<Script> = None;

        for ch in s.chars() {
            match self.m.get(&ch) {
                None => {
                    return Err(UnicodeToLincolnConversionFailure::NoMapping(ch));
                }
                Some(lch) => {
                    if Some(lch.state.case) == current_case {
                        // Nothing to do
                    } else {
                        result.push(match lch.state.case {
                            LwCase::Upper => u6!(0o75),
                            LwCase::Lower => u6!(0o74),
                        });
                        current_case = Some(lch.state.case);
                    }

                    if Some(lch.state.script) == current_script {
                        // Nothing to do
                    } else {
                        result.push(match lch.state.script {
                            Script::Super => u6!(0o64),
                            Script::Normal => u6!(0o65),
                            Script::Sub => u6!(0o66),
                        });
                        current_script = Some(lch.state.script);
                    }

                    result.push(lch.value);
                }
            }
        }
        Ok(result)
    }
}

impl Default for UnicodeToLincolnMapping {
    fn default() -> UnicodeToLincolnMapping {
        UnicodeToLincolnMapping::new()
    }
}
