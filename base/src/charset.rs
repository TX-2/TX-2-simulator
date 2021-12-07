use std::error::Error;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
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
        'S' => Ok('\u{209B}'),
        'T' => Ok('ᵀ'),
        'U' => Ok('ᵁ'),
        'V' => Ok('ⱽ'),
        'W' => Ok('ᵂ'),
        'X' => Ok('\u{2093}'),
        'Y' | 'Z' => Err(NoSuperscriptKnown(ch)),
        _ => Err(NoSuperscriptKnown(ch)),
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LincolnToUnicodeConversionFailure {
    CharacterOutOfRange(u8),
    NoMapping(u8),
}

enum Script {
    Normal,
    Super,
    Sub,
}

struct LincolnState {
    script: Script,
    uppercase: bool,
}

impl Default for LincolnState {
    fn default() -> Self {
        Self {
            script: Script::Normal,
            uppercase: true,
        }
    }
}

fn lincoln_char_to_unicode_char(
    lin_ch: &u8,
    state: &mut LincolnState,
) -> Result<Option<char>, LincolnToUnicodeConversionFailure> {
    let nm = || -> Result<Option<char>, LincolnToUnicodeConversionFailure> {
        Err(LincolnToUnicodeConversionFailure::NoMapping(*lin_ch))
    };
    let by_case = |upper: char, lower: char| -> Option<char> {
        Some(if state.uppercase { upper } else { lower })
    };
    let base_char: Option<char> = match lin_ch {
        0o00 => by_case('0', '☛'), // \U261B, black hand pointing right
        0o01 => by_case('1', 'Σ'),  // \U03A3, Greek capital letter Sigma
        0o02 => by_case('2', '|'),
        0o03 => by_case('3', '‖'), // \U2016, double vertical line
        0o04 => by_case('4', '/'),
        0o05 => by_case('5', '×'), // multiplication sign (U+00D7)
        0o06 => by_case('6', '#'),
        0o07 => by_case('7', '→'), // rightwards arrow (U+2192)
        0o10 => by_case('8', '<'),
        0o11 => by_case('9', '>'),
        0o12 => by_case('_', '‾'),   // Overline (U+203E)
        0o13 => by_case('○', '□'), // U+25CB white circle, U+25A1 white square
        0o14 => return nm(),           // "READ IN"
        0o15 => return nm(),           // "BEGIN"
        0o16 => return nm(),           // "NO"
        0o17 => return nm(),           // "YES"
        0o20 => by_case('A', '≈'),   // Almost Equal To (U+2248)
        0o21 => by_case('B', '⊂'),   // Subset of (U+2282)
        0o22 => by_case('C', '∨'),   // Logical or (U+2228)
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
        0o40 => by_case('Q', 'a'),
        0o41 => by_case('R', 'Δ'), // Greek capital delta, U+0394
        0o42 => by_case('S', 'p'),
        0o43 => by_case('T', '∈'), // Element of, U+2208
        0o44 => by_case('U', 'h'),
        0o45 => by_case('V', '⊃'), // Superset of, U+2283
        0o46 => by_case('W', 'ϐ'),  // Greek beta symbol, U+03D0
        0o47 => by_case('X', '^'),
        0o50 => by_case('Y', 'λ'), // Greek small letter lambda, U+03BB
        0o51 => by_case('Z', '~'),
        0o52 => by_case('(', '{'),
        0o53 => by_case(')', '}'),
        0o54 => by_case('+', '≡'), // Identical to, U+2261
        0o55 => by_case('-', '='),
        0o56 => by_case(',', '\u{0027}'), // Single apostrophe, U+0027
        0o57 => by_case('.', '*'),
        0o60 => Some('\r'),
        0o61 => Some('\t'),
        0o62 => Some('\u{0008}'), // backspace, U+0008
        0o63 => return nm(),      // COLOR BLACK
        0o64 => {
            state.script = Script::Super;
            None
        }
        0o65 => {
            state.script = Script::Normal;
            None
        }
        0o66 => {
            state.script = Script::Sub;
            None
        }
        0o67 => return nm(),      // COLOR RED
        0o70 => Some(' '),        // space
        0o71 => return nm(),      // WORD EXAM
        0o72 => Some('\n'),       // LINE FEED
        0o73 => Some('\u{008D}'), // Reverse line feed
        0o74 => {
            state.uppercase = false;
            None
        }
        0o75 => {
            state.uppercase = true;
            None
        }
        0o76 => return nm(), // STOP
        0o77 => {
            // Supposedly NULLIFY but it's used on tape to delete
            // the previous character so delete fits.
            Some('\u{007F}')
        }
        _ => {
            return Err(LincolnToUnicodeConversionFailure::CharacterOutOfRange(
                *lin_ch,
            ));
        }
    };

    if let Some(base) = base_char {
        match state.script {
            Script::Normal => Ok(Some(base)),
            Script::Sub => Ok(Some(subscript_char(base).unwrap_or(base))),
            Script::Super => Ok(Some(superscript_char(base).unwrap_or(base))),
        }
    } else {
        Ok(None)
    }
}

/// Convert a stream of Lincoln Writer codes to a Unicode string.
/// Lincoln Writer codes are 6 bits, and these are assumed to be in
/// the lower 6 bits of the input values.
pub fn lincoln_to_unicode_strict(
    input: &[u8],
) -> Result<String, LincolnToUnicodeConversionFailure> {
    let mut result = String::with_capacity(input.len());
    let mut state: LincolnState = LincolnState::default();
    for byte in input {
        match lincoln_char_to_unicode_char(byte, &mut state) {
            Ok(Some(ch)) => {
                result.push(ch);
            }
            Ok(None) => (),
            Err(e) => {
                return Err(e);
            }
        }
    }
    Ok(result)
}

#[test]
fn test_lincoln_to_unicode_strict() {
    // Regular script
    assert_eq!(
        lincoln_to_unicode_strict(&[0o27, 0o24, 0o33, 0o33, 0o36]),
        Ok("HELLO".to_string())
    );

    assert_eq!(
        lincoln_to_unicode_strict(&[
            0o64, // Superscript
            0o27, 0o24, 0o33, 0o33, 0o36
        ]), // HELLO
        Ok("ᴴᴱᴸᴸᴼ".to_string())
    );

    assert_eq!(
        lincoln_to_unicode_strict(&[
            0o65, // Normal
            0o27, // H
            0o66, // Subscript
            0o02, // 2
            0o36
        ]), // O
        Ok("H₂O".to_string())
    );

    assert_eq!(
        lincoln_to_unicode_strict(&[
            0o74, // Lower case
            0o52, // { (when lower case)
            0o53, // } (when lower case)
            0o75, // Upper case
            0o52, // ( (when upper case)
            0o53, // ) (when upper case)
        ]),
        Ok("{}()".to_string())
    );
}
