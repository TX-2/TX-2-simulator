use std::fmt::Write;
use std::num::IntErrorKind;
use std::ops::Shl;

use nom::branch::alt;
use nom::bytes::complete::{tag, take, take_until, take_while1};
use nom::character::complete::{char, digit1, one_of, space0};
use nom::combinator::{map, map_res, opt, recognize, verify};
use nom::multi::{many0, many1};
use nom::sequence::{delimited, pair, preceded, separated_pair, terminated, tuple};

use super::ast::*;
use super::ek;
use super::state::{Error, NumeralMode, StateExtra};
use super::types::*;
use base::prelude::*;

#[derive(Debug, Clone)]
pub(crate) struct ErrorLocation {
    /// line is usually derived from LocatedSpan::location_line() which returns
    /// a u32.
    pub(crate) line: LineNumber,
    pub(crate) column: Option<usize>,
}

impl<'a, 'b> From<&ek::LocatedSpan<'a, 'b>> for ErrorLocation {
    fn from(span: &ek::LocatedSpan<'a, 'b>) -> ErrorLocation {
        ErrorLocation {
            line: span.location_line(),
            column: Some(span.get_utf8_column()),
        }
    }
}

pub(crate) fn maybe_superscript_sign<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Option<char>> {
    opt(alt((
        char('\u{207B}'), // U+207B: superscript minus
        char('\u{207A}'), // U+207A: superscript plus
    )))(input)
}

pub(crate) fn maybe_subscript_sign<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Option<char>> {
    opt(alt((
        char('\u{208B}'), // U+208B: subscript minus
        char('\u{208A}'), // U+208A: subscript plus
    )))(input)
}

fn make_u36(s: &str, radix: u32) -> Result<Unsigned36Bit, StringConversionFailed> {
    match u64::from_str_radix(s, radix) {
        Ok(n) => n.try_into().map_err(StringConversionFailed::Range),
        Err(e) => match e.kind() {
            IntErrorKind::Empty | IntErrorKind::InvalidDigit => {
                Err(StringConversionFailed::NotOctal)
            }
            IntErrorKind::PosOverflow => {
                Err(StringConversionFailed::Range(ConversionFailed::TooLarge))
            }
            _ => unreachable!(),
        },
    }
}

fn make_num(
    (sign, digits, radix): (Option<char>, &str, u32),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    let n = make_u36(digits, radix)?;
    if let Some('-') = sign {
        Ok(Unsigned36Bit::ZERO.wrapping_sub(n))
    } else {
        Ok(n)
    }
}

fn make_num_from_span(
    (sign, digits, dot): (Option<char>, ek::LocatedSpan, Option<ek::LocatedSpan>),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_num((sign, &digits, digits.extra.radix(dot.is_some())))
}

fn maybe_superscript_sign_to_maybe_regular_sign(
    maybe_superscript_sign: Option<char>,
) -> Option<char> {
    maybe_superscript_sign.map(|ch| match ch {
        '\u{207B}' => '-', // U+207B: superscript minus
        '\u{207A}' => '+', // U+207A: superscript plus
        _ => unreachable!(),
    })
}

fn maybe_subscript_sign_to_maybe_regular_sign(maybe_subscript_sign: Option<char>) -> Option<char> {
    maybe_subscript_sign.map(|ch| match ch {
        '\u{208B}' => '-', // U+208B: subscript minus
        '\u{208A}' => '+', // U+208A: subscript plus
        _ => unreachable!(),
    })
}

fn superscript_oct_digit_to_value(ch: char) -> Option<u8> {
    match ch {
        '\u{2070}' => Some(0),
        '\u{00B9}' => Some(1),
        '\u{00B2}' => Some(2),
        '\u{00B3}' => Some(3),
        '\u{2074}' => Some(4),
        '\u{2075}' => Some(5),
        '\u{2076}' => Some(6),
        '\u{2077}' => Some(7),
        _ => None,
    }
}

fn subscript_oct_digit_to_value(ch: char) -> Option<u8> {
    match ch {
        '\u{2080}' => Some(0),
        '\u{2081}' => Some(1),
        '\u{2082}' => Some(2),
        '\u{2083}' => Some(3),
        '\u{2084}' => Some(4),
        '\u{2085}' => Some(5),
        '\u{2086}' => Some(6),
        '\u{2087}' => Some(7),
        _ => None,
    }
}

fn make_superscript_num(
    (superscript_sign, superscript_digits, dot): (
        Option<char>,
        ek::LocatedSpan,
        Option<ek::LocatedSpan>,
    ),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    let radix: u32 = superscript_digits.extra.radix(dot.is_some());
    let sign: Option<char> = maybe_superscript_sign_to_maybe_regular_sign(superscript_sign);
    let mut normal_digits: String = String::new();
    for digit in superscript_digits.fragment().chars() {
        if let Some(n) = superscript_oct_digit_to_value(digit) {
            if write!(&mut normal_digits, "{}", n).is_err() {
                // writes to strings always succeed
                unreachable!()
            }
        } else {
            return Err(StringConversionFailed::NotOctal);
        }
    }
    make_num((sign, &normal_digits, radix))
}

fn make_subscript_num(
    (subscript_sign, subscript_digits, dot): (Option<char>, ek::LocatedSpan, Option<char>),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    let radix: u32 = subscript_digits.extra.radix(dot.is_some());
    let sign: Option<char> = maybe_subscript_sign_to_maybe_regular_sign(subscript_sign);
    let mut normal_digits: String = String::new();
    for digit in subscript_digits.fragment().chars() {
        if let Some(n) = subscript_oct_digit_to_value(digit) {
            if write!(&mut normal_digits, "{}", n).is_err() {
                // writes to strings always succeed
                unreachable!()
            }
        } else {
            return Err(StringConversionFailed::NotOctal);
        }
    }
    make_num((sign, &normal_digits, radix))
}

/// The Linconln writer places the "regular" (i.e. not superscript or
/// subscript) in the middle of the vertical rise of normal digits
/// instead of on the line.  So, "3⋅141", not "3.141".
fn maybe_normal_dot<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Option<ek::LocatedSpan<'a, 'b>>> {
    opt(alt((
        tag("\u{22C5}"), // Unicode Dot Operator U+22C5 ("⋅")
        tag("\u{00B7}"), // Unicode Middle Dot U+00B7 ("·")
    )))(input)
}

fn maybe_superscript_dot<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Option<ek::LocatedSpan<'a, 'b>>> {
    opt(
        tag("\u{0307} "), // Unicode Combining Dot Above ̇followed by space ("̇ ")
    )(input)
}

/// Recognise a subscript dot.  On the Linconln Writer, the dot is
/// raised above the line, like the dot customarily used for the
/// dot-product.  Hence for subscripts we use the regular ascii dot
/// (full stop, period) which is on the line.
fn maybe_subscript_dot<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Option<char>> {
    opt(char('.'))(input)
}

pub(crate) fn normal_literal<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, LiteralValue> {
    fn maybe_sign<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Option<char>> {
        opt(alt((char('-'), char('+'))))(input)
    }
    fn normal_number<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Unsigned36Bit> {
        map_res(
            tuple((maybe_sign, digit1, maybe_normal_dot)),
            make_num_from_span,
        )(input)
    }

    map(normal_number, |n| {
        LiteralValue::from((Elevation::Normal, n))
    })(input)
}

pub(crate) fn opcode<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, LiteralValue> {
    fn valid_opcode(s: ek::LocatedSpan) -> Result<LiteralValue, ()> {
        match opcode_to_num(s.fragment()) {
            DecodedOpcode::Valid(opcode) => {
                // Some instructions are assembled with the hold bit automatically set.
                // These are JPX, JNX, LDE, ITE.  See Users Handbook, section 4-3.2 on page 4-5.
                let maybe_hold: u64 = if matches!(u8::from(opcode), 0o06 | 0o07 | 0o20 | 0o40) {
                    1 << 35
                } else {
                    0
                };
                Ok(LiteralValue::from((
                    Elevation::Normal,
                    // Bits 24-29 (dec) inclusive in the instruction word
                    // represent the opcode, so shift the opcode's value
                    // left by 24 decimal.
                    Unsigned36Bit::from(opcode).shl(24).bitor(maybe_hold),
                )))
            }
            DecodedOpcode::Invalid => Err(()),
        }
    }
    map_res(take(3usize), valid_opcode)(input)
}

pub(crate) fn superscript_literal<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, LiteralValue> {
    fn superscript_octal_number<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, Unsigned36Bit> {
        fn is_superscript_oct_digit(ch: char) -> bool {
            superscript_oct_digit_to_value(ch).is_some()
        }

        fn superscript_oct_digit1<'a, 'b>(
            input: ek::LocatedSpan<'a, 'b>,
        ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
            take_while1(is_superscript_oct_digit)(input)
        }

        map_res(
            tuple((
                maybe_superscript_sign,
                superscript_oct_digit1,
                maybe_superscript_dot,
            )),
            make_superscript_num,
        )(input)
    }

    map(superscript_octal_number, |n| {
        LiteralValue::from((Elevation::Superscript, n))
    })(input)
}

pub(crate) fn subscript_literal<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, LiteralValue> {
    fn subscript_octal_number<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, Unsigned36Bit> {
        fn is_subscript_oct_digit(ch: char) -> bool {
            subscript_oct_digit_to_value(ch).is_some()
        }

        fn subscript_oct_digit1<'a, 'b>(
            input: ek::LocatedSpan<'a, 'b>,
        ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
            take_while1(is_subscript_oct_digit)(input)
        }
        map_res(
            tuple((
                maybe_subscript_sign,
                subscript_oct_digit1,
                maybe_subscript_dot,
            )),
            make_subscript_num,
        )(input)
    }

    map(subscript_octal_number, |n| {
        LiteralValue::from((Elevation::Subscript, n))
    })(input)
}

pub(crate) fn program_instruction_fragment<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, InstructionFragment> {
    preceded(space0, map(expression, InstructionFragment::from))(input)
}

pub(crate) fn program_instruction_fragments<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Vec<InstructionFragment>> {
    many1(program_instruction_fragment)(input)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DecodedOpcode {
    Valid(Unsigned6Bit),
    Invalid,
}

fn opcode_to_num(input: &str) -> DecodedOpcode {
    let val: u8 = match input {
        // opcode 1 is unused
        // opcode 2 may be XEQ, but no documentation on this.
        // opcode 3 is unused
        "IOS" => 0o4, // see also Vol 3 page 16-05-07
        "JMP" => 0o5,
        "JPX" => 0o6,
        "JNX" => 0o7,
        "AUX" => 0o10,
        "RSX" => 0o11,
        "SKX" | "REX" | "SEX" => 0o12,
        // opcode 0o13 = 11 is undefined (unused).
        "EXX" => 0o14,
        "ADX" => 0o15,
        "DPX" => 0o16,
        "SKM" => 0o17,
        "LDE" => 0o20,
        "SPF" => 0o21,
        "SPG" => 0o22,
        // op>code 0o23 = 19 is undefined (unused).
        "LDA" => 0o24,
        "LDB" => 0o25,
        "LDC" => 0o26,
        "LDD" => 0o27,
        "STE" => 0o30,
        "FLF" => 0o31,
        "FLG" => 0o32,
        // opcode 033 = 27 is unused.
        "STA" => 0o34,
        "STB" => 0o35,
        "STC" => 0o36,
        "STD" => 0o37,
        "ITE" => 0o40,
        "ITA" => 0o41,
        "UNA" => 0o42,
        "SED" => 0o43,

        // I have two copies of the User Handbook and they differ in
        // their description of opcodes 0o44, 0o45.
        //
        // In the August 1963 copy, 0o44 is missing and 0045 is JOV.
        //
        // In the index of the October 1961 copy, 0o44 is JOV and 0o45 is
        // JZA (handwritten).  However, in this copy, page 3-32 (which
        // describes JPA, JNA, JOV) gives JOV as 0o45.  So I assume this
        // is just an error in the index.  This copy does not otherwise
        // describe a JZA opcode.
        "JOV" => 0o45,

        "JPA" => 0o46,
        "JNA" => 0o47,
        // opcode 0o50 = 40 is undefined (unused).
        // opcode 0o51 = 41 is undefined (unused).
        // opcode 0o52 = 42 is undefined (unused).
        // opcode 0o53 = 43 is undefined (unused).
        "EXA" => 0o54,
        "INS" => 0o55,
        "COM" => 0o56,
        "TSD" => 0o57,
        "CYA" => 0o60,
        "CYB" => 0o61,
        "CAB" => 0o62,
        // opcode 0o63 = 51 is unused.
        "NOA" => 0o64,
        "DSA" => 0o65,
        "NAB" => 0o66,
        "ADD" => 0o67,
        "SCA" => 0o70,
        "SCB" => 0o71,
        "SAB" => 0o72,
        // opcode 0o71 = 59 is unused.
        "TLY" => 0o74,
        "DIV" => 0o75,
        "MUL" => 0o76,
        "SUB" => 0o77,
        _ => {
            return DecodedOpcode::Invalid;
        }
    };
    DecodedOpcode::Valid(Unsigned6Bit::try_from(val).unwrap())
}

fn spaces1<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
    take_while1(|c| c == ' ')(input)
}

fn is_nonblank_simple_symex_char(c: char) -> bool {
    c.is_ascii_digit()
        || c.is_ascii_uppercase()
        || matches!(
            c,
            'i' | 'j' | 'k' | 'n' | 'p' | 'q' | 't' | 'w' | 'x' | 'y' | 'z' |
            '.' | '\'' | '_' |
            '\u{203E}' | // Unicode non-combining overline
            '\u{25A1}' | // Unicode white square
            '\u{25CB}' // Unicode white circle
        )
}

/// Recognise a single dead character, a character which does not
/// advance the character/cursor when printed.
pub(crate) fn dead_char<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
    recognize(one_of(concat!(
        "\u{0332}", // combining low line
        "\u{0305}", // combining overline
        "\u{20DD}", // combining enclosing circle
        "\u{20DE}", // combining enclosing square
    )))(input)
}

/// Recognise a single compound character.
///
/// ## Users Handbook Definition of Compound Characters
///
/// Compound chars are described in item 7 on page 607 of the TX-2
/// Users Handbook (Nov 63).
///
/// Compound characters are described like so:
///
///  - Only one backspace
///  - Two or three characters only.
///  - Space bar is allowed
///  - Any sequence of characters is legal. (Except ...)
///
/// This seems confusing at first but the key to understanding
/// it is that the Lincoln Writer (from which these characters
/// come) has four characters which don't advance the carriage
/// when they are printed (underline, overline, square,
/// circle).  That is, the following character is overstruck.
/// The underline _ is one such character: then _ followed by G
/// is a compound character, _ overstruck with G.  This would
/// be a two-character compound character.
///
/// A compound character can also be formed with a space,
/// presumably for example a character which doesn't advance
/// the carriage followed by a space, which does.
///
/// Using our single allowed backspace, we could create a
/// compound character using a character which does advance the
/// carriage, for example K.  K\b> K overstruck with a >.
///
/// Another three-character option is to use two
/// non-carriage-advancing characters.  The documentation
/// doesn't seem to clearly state whether Lincoln Writer codes
/// 0o74 and 0o75 ("LOWER CASE" and "UPPER CASE") are
/// permitted.  This makes a difference because for example
/// CIRCLE is upper case while SQUARE is lower case (both
/// signaled by code 013).   So I am not clear on whether
/// this sequence of codes is a valid single compound
/// character (assume we start in upper-case).
///
/// Code  Representing          Advances carriage?
/// 013   CIRCLE                No (it's special)
/// 074   Shift to lower case   No (it's non-printing)
/// 013   SQUARE                No (it's special)
/// 057   *                     Yes (rightward)
///
/// If valid this would represent a circle, square and asterisk
/// all on the same spot.
///
/// For the moment we don't need to worry about this, because we
/// cannot tell the difference; the current parser implementation
/// accepts Unicode input, and by the time the Lincoln Writer code
/// have been translated into Unicode, the upper/lower case shift
/// codes are no longer present in the parser's input.
///
/// Another input that tests our understanding is this one:
///
/// Code  Representing          Advances carriage?
/// 013   CIRCLE                No (it's special)
/// 062   Backspace             Yes (leftward!)
/// 012   _ (underline)         No (it's special)
///
/// This meets the letter of the condition (just one backspace,
/// only three characters).  But the net effect of these code is a
/// net leftward movement of the carriage/cursor.
///
/// Yet another:
/// 031   J                     Yes
/// 062   Backspace             Yes (leftward!)
/// 027   H                     Yes
/// 062   Backspace             Yes (leftward!)
/// 032   K                     Yes
///
/// Here we apparently see 031 062 027 as the first compound
/// character (three characters, one backspace) but is the
/// following thing valid?  The problem is it starts with a
/// backspace.  That cannot be part of the initial compound
/// character because only one backspace is allowed.
///
/// ## Additional Restrictions
///
/// It seems that the Users Handbook underspecifies the compound
/// character.  We will have to do something - accept some inputs
/// and perhaps reject others.
///
/// For now, I plan to add additional restrictions, not stated in
/// the Users Handbook, which helps disambiguate:
///
/// A compound character is a sequene of two or three characters
/// which
///  1. Does not begin with a backspace
///  2. Does not end with a backspace
///  3. Does not end with a dead character (a character which does
///     not advance the carriage).
///  4. Includes either a backspace or a dead character.
///
/// The thinking behind this restriction is that it enforces a
/// requirement that the "compound character" not overlap with
/// those characters that precede or follow it.
///
/// If D represents a non-advancing character (_, square, and so
/// on), X represents a character which does advance the carriage,
/// S represents space and \b represents backspace, these are
/// valid compound characters:
///
/// DS
/// DX
/// S\bX
/// X\bS
/// S\bS (more about this one below)
/// DDS
/// DDX
///
/// In terms of error-handling, once we see a dead character at
/// the current input position, we know that we need to end up
/// with a compound character which starts with it.  Once we see a
/// regular character which advances the carriage followed by a
/// backspace, we know we must be looking at a three-character
/// compound character (i.e. it's an error for the character after
/// the \b to be a dead character).
///
/// The following examples would not be valid because the above
/// rule disallows them.  After each I identify in parentheses the
/// reason I think it should not be allowed (i.e. why our
/// additional restriction is helpful).
///
/// XX\b (would overlap the next character)
/// DDD  (would overlap the next character)
/// DXD  (would overlap the next character)
/// DSD  (would overlap the next character)
/// DDD  (would overlap the next character)
/// SDD  (would overlap the next character)
/// XDD  (would overlap the next character)
/// \bDX (would overlap the previous character)
/// \bXX (similar, but also visually appears to be two characters).
///
/// These rules permit the form "S\bS" even though that's
/// potentially confusing for users in that it is visually
/// insidtinguishable from a single space.
///
/// Condition 4 above ensures that these forms are not considered
/// compound characters:
///
/// XX  (we want to parse that as two simple characters)
/// XXX (we want to parse that as three simple characters)
/// XSX (we want to parse that as two single-character syllables
///     separated by a space)
/// XDX (we want to parse this as the simple character X followed by
///      the compound character DX, because this reflects the fact
///      that the syllable takes up two "columns")
///
/// This overstriking behaviour is described by A. Vanderburgh
/// in "The Lincoln Keyboard - a typewriter keyboard designed
/// for computers imput flexibility", a one-page paper in
/// Communications of the ACM, Volume 1, Issue 7, July 1958
/// (https://doi.org/10.1145/368873.368879).
pub(crate) fn parse_compound_char<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
    // accepts a single character which advances the carriage.
    fn advances<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        fn all_simple(input: &ek::LocatedSpan) -> bool {
            input.chars().all(is_nonblank_simple_symex_char)
        }
        fn parse_simple_nonblanks<'a, 'b>(
            input: ek::LocatedSpan<'a, 'b>,
        ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
            verify(take(1usize), all_simple)(input)
        }
        alt((recognize(char(' ')), recognize(parse_simple_nonblanks)))(input)
    }

    fn bs<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        const BACKSPACE: char = '\u{8}';
        recognize(separated_pair(
            advances,
            char(BACKSPACE),
            ek::expect(
                advances,
                "backspace must be followed by a character which advances the cursor",
            ),
        ))(input)
    }

    fn two<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        recognize(preceded(
            dead_char,
            ek::expect(
                advances,
                "the character following a dead character must advance the cursor",
            ),
        ))(input)
    }

    fn three<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        alt((bs, preceded(dead_char, two)))(input)
    }

    alt((two, three))(input)
}

pub(crate) fn parse_symex<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, SymbolName> {
    fn is_reserved_identifier(ident: &ek::LocatedSpan) -> bool {
        fn is_register_name(name: &str) -> bool {
            matches!(name, "A" | "B" | "C" | "D" | "E")
        }

        is_register_name(ident.fragment())
            || matches!(opcode_to_num(ident.fragment()), DecodedOpcode::Valid(_))
    }

    fn parse_nonblank_simple_symex_chars<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        take_while1(is_nonblank_simple_symex_char)(input)
    }

    // This function gives the impression it wouldn't be very
    // efficient, but any TX-2 program will have to fit into the
    // address space of the machine, meaning that the assembler input
    // is unlikely to be more than 2^17 lines.  We can profile the
    // assembler on some longer input once the assembler actually
    // works.  For now we're concerned with correctness and we'll punt
    // on efficiency until we can quantify any problem.
    fn parse_symex_syllable<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        fn parse_compound_chars<'a, 'b>(
            input: ek::LocatedSpan<'a, 'b>,
        ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
            recognize(many1(parse_compound_char))(input)
        }
        recognize(many1(alt((
            parse_nonblank_simple_symex_chars,
            // compound chars containing a space still don't terminate the symex.
            parse_compound_chars,
        ))))(input)
    }

    fn parse_symex_reserved_syllable<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        verify(parse_symex_syllable, is_reserved_identifier)(input)
    }

    fn parse_symex_non_reserved_syllable<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        fn not_reserved(input: &ek::LocatedSpan) -> bool {
            !is_reserved_identifier(input)
        }
        verify(parse_symex_syllable, not_reserved)(input)
    }

    fn parse_multi_syllable_symex<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        recognize(pair(
            parse_symex_non_reserved_syllable,
            many0(preceded(spaces1, parse_symex_syllable)),
        ))(input)
    }

    map(
        alt((parse_multi_syllable_symex, parse_symex_reserved_syllable)),
        |loc| SymbolName::from(&loc),
    )(input)
}

pub(crate) fn arrow<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
    fn just_arrow<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        alt((
            tag("->"),
            tag("\u{2192}"), // Unicode rightwards pointing arrow
        ))(input)
    }
    recognize(tuple((space0, just_arrow, space0)))(input)
}

pub(crate) fn literal<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, LiteralValue> {
    alt((normal_literal, superscript_literal, subscript_literal))(input)
}

// Parse an expression; these can currently only take the form of a literal.
// TX-2's M4 assembler allows arithmetic expressions also, but these are not
// currently implemented.
//
// When we do implement fuller support for expressions, we need to pay
// attention to the rules for symex termination (see section 6-2.3
// "RULES FOR SYMEX FORMATION" item 8), because script changes
// terminate symexes.
//
// This means that BAT² is not an identifier but an sequence[1] whose
// value is computed by OR-ing the value of the symex BAT with the
// value of the literal "²" (which is 2<<30, or 0o20_000_000_000).
// Whether BAT² is itself an expression or an "InstructionFragment" is
// something we will need to consider carefully.  For example, is
// (BAT²) valid?  If yes, then so is (BAT²)+1, meaning that our
// current rule for instruction_fragment may have to change
// significantly.
//
// [1] I use "sequence" in the paragraph above to avoid saying
// "expression" or "instruction fragment".
pub(crate) fn expression<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Expression> {
    let symbolic_expression = map(symbol_name, |name| {
        Expression::Symbol(Elevation::Normal, name)
    });
    let literal_expression = map(alt((literal, opcode)), |literal: LiteralValue| {
        Expression::from(literal)
    });
    alt((literal_expression, symbolic_expression))(input)
}

/// An address expression is a literal value or a symex.  That is I
/// think it's not required that an arithmetic expression
/// (e.g. "5+BAR") be accepted in an origin notation (such as
/// "<something>|").
fn address_expression<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Address> {
    // We should eventually support symexes here.
    map_res(literal, |literal| Address::try_from(literal.value()))(input)
}

pub(crate) fn symbol_name<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, SymbolName> {
    map(parse_symex, SymbolName::from)(input)
}

pub(crate) fn tag_definition<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, SymbolName> {
    terminated(symbol_name, arrow)(input)
}

fn origin<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Address> {
    terminated(address_expression, pair(space0, tag("|")))(input)
}

pub(crate) fn double_hand<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Option<char>> {
    fn hand<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, char> {
        char('☛')(input)
    }

    preceded(
        hand,
        ek::expect(hand, "'☛' should be followed by another '☛'"),
    )(input)
}

fn base_change<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
    fn decimal<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
        map(alt((tag("DECIMAL"), tag("DEC"))), |_| {
            ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)
        })(input)
    }
    fn octal<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
        map(alt((tag("OCTAL"), tag("OCT"))), |_| {
            ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)
        })(input)
    }

    alt((decimal, octal))(input)
}

fn punch_address(a: Option<LiteralValue>) -> Result<PunchCommand, String> {
    match a {
        None => Ok(PunchCommand(None)),
        Some(literal) => {
            let value = literal.value();
            match Unsigned18Bit::try_from(value) {
                Err(e) => Err(format!(
                    "PUNCH address value {:o} is not a valid address: {}",
                    value, e
                )),
                Ok(halfword) => {
                    let addr: Address = Address::from(halfword);
                    if addr.mark_bit() != Unsigned18Bit::ZERO {
                        Err(format!(
                            "PUNCH address value {:o} must not be a deferred address",
                            addr
                        ))
                    } else {
                        Ok(PunchCommand(Some(addr)))
                    }
                }
            }
        }
    }
}

fn punch<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
    match map_res(
        // We interpret "AA" in the descripion of the PUNCH
        // metacommand as accepting only literal numeric (and not
        // symbolic) values.  That may not be a correct
        // interpretation, though.
        preceded(preceded(tag("PUNCH"), spaces1), opt(literal)),
        punch_address,
    )(input)
    {
        Ok((input, punch)) => {
            let cmd: ManuscriptMetaCommand = ManuscriptMetaCommand::Punch(punch);
            Ok((input, cmd))
        }
        Err(nom::Err::Error(e) | nom::Err::Failure(e)) => {
            let err = Error(
                ErrorLocation::from(&e.input),
                "invalid PUNCH address".to_string(),
            );
            e.input.extra.report_error(err);
            Ok((e.input, ManuscriptMetaCommand::Invalid))
        }
        Err(e) => Err(e),
    }
}

fn metacommand_body<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
    alt((base_change, punch))(input)
}

pub(crate) fn metacommand<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
    map(
        pair(
            double_hand,
            ek::expect(
                metacommand_body,
                "double meta hand '☛☛' must be followed by a valid meta command",
            ),
        ),
        |got| match got {
            (Some(_), Some(cmd)) => cmd,
            _ => ManuscriptMetaCommand::Invalid,
        },
    )(input)
}

/// Accept either 'h' or ':' signalling the hold bit should be set.
/// The documentation seems to use both, though perhaps ':' is the
/// older usage.
fn hold<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, HoldBit> {
    map(alt((tag("h"), tag(":"))), |_| HoldBit::Hold)(input)
}

fn not_hold<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, HoldBit> {
    map(
        alt((
            // Accept a combining overbar with h, as used on the TX-2.
            tag("\u{0305}h"),
            // Also accept the "h with stroke" (better known as h-bar) symbol.
            tag("ℏ"),
        )),
        |_| HoldBit::NotHold,
    )(input)
}

pub(crate) fn maybe_hold<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, HoldBit> {
    let holdmapper = |got: Option<HoldBit>| got.unwrap_or(HoldBit::Unspecified);
    map(opt(preceded(space0, alt((hold, not_hold)))), holdmapper)(input)
}

pub(crate) fn program_instruction<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ProgramInstruction> {
    fn build_inst(
        parts: (Option<SymbolName>, HoldBit, Vec<InstructionFragment>),
    ) -> ProgramInstruction {
        let (maybe_tag, holdbit, fragments) = parts;
        ProgramInstruction {
            tag: maybe_tag,
            holdbit,
            parts: fragments,
        }
    }

    map(
        tuple((
            opt(tag_definition),
            maybe_hold,
            program_instruction_fragments,
        )),
        build_inst,
    )(input)
}

fn execute_metacommand(state_extra: &StateExtra, cmd: &ManuscriptMetaCommand) {
    match cmd {
        ManuscriptMetaCommand::Invalid => {
            // Error messages about invalid metacommands are
            // accumulated in the parser state and don't need to be
            // separately reported.
        }
        ManuscriptMetaCommand::Punch(_) => {
            // Instead of executing this metacommand as we parse it,
            // we simply return it as part of the parser output, and
            // it is executed by the driver.
        }
        ManuscriptMetaCommand::BaseChange(new_base) => state_extra.set_numeral_mode(*new_base),
    }
}

/// Assginments are called "equalities" in the TX-2 Users Handbook.
/// See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
/// AUTOMATIC ASSIGNMENT".
pub(crate) fn assignment<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, (SymbolName, Expression)> {
    let equals = delimited(space0, tag("="), space0);
    separated_pair(parse_symex, equals, expression)(input)
}

pub(crate) fn statement<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Statement> {
    alt((
        // We have to parse an assignment first here, in order to
        // accept "FOO=2" as an assignment rather than the instruction
        // fragment "FOO" followed by a syntax error.
        map(assignment, |(sym, val)| Statement::Assignment(sym, val)),
        map(program_instruction, Statement::Instruction),
    ))(input)
}

pub(crate) fn manuscript_line<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ManuscriptLine> {
    fn parse_and_execute_metacommand<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ManuscriptLine> {
        match metacommand(input) {
            Ok((tail, cmd)) => {
                execute_metacommand(&tail.extra, &cmd);
                Ok((tail, ManuscriptLine::MetaCommand(cmd)))
            }
            Err(e) => Err(e),
        }
    }

    fn build_code_line(parts: (Option<Address>, Statement)) -> ManuscriptLine {
        let maybe_origin: Option<Origin> = parts.0.map(Origin);
        ManuscriptLine::Code(maybe_origin, parts.1)
    }

    let origin_only = map(origin, |address| {
        ManuscriptLine::JustOrigin(Origin(address))
    });

    let line = alt((
        parse_and_execute_metacommand,
        map(pair(opt(origin), statement), build_code_line),
        // Because we prefer to parse a statement if one exists,
        // the origin_only alternative has to appear after the
        // alternative which parses a statement.
        origin_only,
    ));

    preceded(space0, line)(input)
}

pub(crate) fn comment<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, String> {
    map(
        recognize(preceded(preceded(space0, tag("**")), take_until("\n"))),
        |text: ek::LocatedSpan| text.fragment().to_string(),
    )(input)
}

pub(crate) fn newline<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, char> {
    char('\n')(input)
}

pub(crate) fn end_of_line<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
    fn one_end_of_line<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        recognize(preceded(preceded(space0, opt(comment)), newline))(input)
    }

    recognize(many1(one_end_of_line))(input)
}

fn manuscript_lines_to_blocks(
    lines: Vec<ManuscriptLine>,
) -> (Vec<ManuscriptBlock>, Option<PunchCommand>) {
    let mut result: Vec<ManuscriptBlock> = Vec::new();
    let mut current_statements: Vec<Statement> = Vec::new();
    let mut maybe_punch: Option<PunchCommand> = None;
    let mut effective_origin: Option<Origin> = None;

    fn ship_block(
        statements: &Vec<Statement>,
        maybe_origin: Option<Origin>,
        result: &mut Vec<ManuscriptBlock>,
    ) {
        if !statements.is_empty() {
            result.push(ManuscriptBlock {
                origin: maybe_origin,
                statements: statements.to_vec(),
            });
        }
    }

    for line in lines {
        match line {
            ManuscriptLine::MetaCommand(ManuscriptMetaCommand::Invalid) => {
                // The error was already reported in the parser state.
                // The recovery action is just to ignore it.
            }
            ManuscriptLine::MetaCommand(ManuscriptMetaCommand::Punch(punch)) => {
                maybe_punch = Some(punch);
            }
            ManuscriptLine::MetaCommand(ManuscriptMetaCommand::BaseChange(_)) => {
                // These already took effect on the statements which
                // were parsed following them, so no need to keep them
                // now.
            }
            ManuscriptLine::JustOrigin(new_origin) => {
                ship_block(&current_statements, effective_origin, &mut result);
                current_statements.clear();
                effective_origin = Some(new_origin);
                // There is no statement to push, though.
            }
            ManuscriptLine::Code(new_origin, statement) => {
                if new_origin.is_some() {
                    ship_block(&current_statements, effective_origin, &mut result);
                    current_statements.clear();
                    effective_origin = new_origin;
                }
                current_statements.push(statement);
            }
        }
    }
    ship_block(&current_statements, effective_origin, &mut result);
    current_statements.clear();
    (result, maybe_punch)
}

pub(crate) fn source_file<'a, 'b>(
    body: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, SourceFile> {
    fn parse_empty_source_file<'a, 'b>(
        body: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, SourceFile> {
        map(take(0usize), |_| SourceFile::empty())(body)
    }

    // Parse a manuscript (which is a sequence of metacommands, macros
    // and assembly-language instructions).
    pub(crate) fn parse_nonempty_source_file<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, SourceFile> {
        // TODO: when we implement metacommands we will need to separate
        // the processing of the metacommands and the generation of the
        // assembled code, because in between those things has to come the
        // execution of metacommands such as INSERT, DELETE, REPLACE.
        let parse_source_lines = preceded(
            many0(end_of_line),
            many0(terminated(
                manuscript_line,
                ek::expect(end_of_line, "expected newline after a program instruction"),
            )),
        );

        map(parse_source_lines, |lines| {
            let (blocks, punch) = manuscript_lines_to_blocks(lines);
            SourceFile { blocks, punch }
        })(input)
    }

    terminated(
        alt((parse_nonempty_source_file, parse_empty_source_file)),
        ek::expect_end_of_file,
    )(body)
}
