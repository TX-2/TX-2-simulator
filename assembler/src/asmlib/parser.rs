use std::fmt::{self, Display, Formatter, Write};
use std::num::IntErrorKind;
use std::ops::Range;

//use std::ops::Range;
//use base::prelude::*;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while1};
use nom::character::complete::{char, oct_digit1, space0};
use nom::combinator::{map, map_res, opt, recognize, verify};
use nom::multi::{many0, many1};
use nom::sequence::{pair, preceded, terminated, tuple};

use crate::ek::{self, ToRange};
use crate::types::*;
use base::prelude::*;

impl Display for ek::Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self.0.columns.as_ref() {
            None => write!(f, "{}: {}", self.0.line, self.1,),
            Some(cols) => write!(f, "{}:{}: {}", self.0.line, cols.start, self.1,),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ErrorLocation {
    /// line is usually derived from LocatedSpan::location_line() which returns
    /// a u32.
    pub line: LineNumber,
    pub columns: Option<Range<usize>>,
}

impl<'a, 'b> From<&ek::LocatedSpan<'a, 'b>> for ErrorLocation {
    fn from(span: &ek::LocatedSpan<'a, 'b>) -> ErrorLocation {
        let r: Range<usize> = (*span).to_range();
        ErrorLocation {
            line: span.location_line(),
            columns: Some(r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramInstruction {
    pub(crate) tag: Option<SymbolName>,
    pub(crate) parts: Vec<InstructionFragment>,
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

fn make_u36(s: &str) -> Result<Unsigned36Bit, StringConversionFailed> {
    match u64::from_str_radix(s, 8) {
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

fn make_num((sign, digits): (Option<char>, &str)) -> Result<Unsigned36Bit, StringConversionFailed> {
    let n = make_u36(digits)?;
    if let Some('-') = sign {
        Ok(Unsigned36Bit::ZERO.wrapping_sub(n))
    } else {
        Ok(n)
    }
}

fn make_num_from_span(
    (sign, digits): (Option<char>, ek::LocatedSpan),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_num((sign, &digits))
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
    (superscript_sign, superscript_digits): (Option<char>, ek::LocatedSpan),
) -> Result<Unsigned36Bit, StringConversionFailed> {
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
    make_num((sign, &normal_digits))
}

fn make_subscript_num(
    (subscript_sign, subscript_digits): (Option<char>, ek::LocatedSpan),
) -> Result<Unsigned36Bit, StringConversionFailed> {
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
    make_num((sign, &normal_digits))
}

pub(crate) fn normal_literal_instruction_fragment<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, InstructionFragment> {
    fn maybe_sign<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Option<char>> {
        opt(alt((char('-'), char('+'))))(input)
    }

    fn normal_octal_number<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, Unsigned36Bit> {
        map_res(pair(maybe_sign, oct_digit1), make_num_from_span)(input)
    }

    map(normal_octal_number, |n| InstructionFragment {
        elevation: Elevation::Normal,
        value: n,
    })(input)
}

pub(crate) fn superscript_literal_instruction_fragment<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, InstructionFragment> {
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
            pair(maybe_superscript_sign, superscript_oct_digit1),
            make_superscript_num,
        )(input)
    }

    map(superscript_octal_number, |n| InstructionFragment {
        elevation: Elevation::Superscript,
        value: n,
    })(input)
}

pub(crate) fn subscript_literal_instruction_fragment<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, InstructionFragment> {
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
            pair(maybe_subscript_sign, subscript_oct_digit1),
            make_subscript_num,
        )(input)
    }

    map(subscript_octal_number, |n| InstructionFragment {
        elevation: Elevation::Subscript,
        value: n,
    })(input)
}

pub(crate) fn program_instruction_fragment<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, InstructionFragment> {
    alt((
        normal_literal_instruction_fragment,
        superscript_literal_instruction_fragment,
        subscript_literal_instruction_fragment,
    ))(input)
}

pub(crate) fn program_instruction_fragments<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Vec<InstructionFragment>> {
    many1(program_instruction_fragment)(input)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodedOpcode {
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
        "SKX" => 0o12,
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

    fn parse_nonblank_symex_chars<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        fn is_nonblank_symex_char(c: char) -> bool {
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

        take_while1(is_nonblank_symex_char)(input)
    }

    fn parse_symex_syllable<'a, 'b>(
        input: ek::LocatedSpan<'a, 'b>,
    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
        // This functionm should also accept compound chars.  These are
        // described in item 7 on page 607 of the TX-2 Users Handbook (Nov
        // 63).
        //
        // Compound characters are described like so:
        //
        //  - Only one backspace
        //  - Two or three characters only.
        //  - Space bar is allowed
        //  - Any sequence of characters is lebal. (Except ...)
        //
        // This seems confusing at first but the key to understanding it
        // is that the Lincoln Writer (from which these characters come)
        // has a small number of characters which don't advance the
        // carriage when they are printed.  That is, the following
        // character is overstruck.  Suppose X is one such character: then
        // XV is a compound character, X overstruck with V.  This would be
        // a two-character compound character.  Using our single allowed
        // backspace, we could create Q\bK, a Q overstruck with a K.
        //
        // This overstriking behaviour is described in an one-page paper
        // about the Lincoln Writer published in an early ACM publication
        // by Alexander Vanderburgh.
        parse_nonblank_symex_chars(input)
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
    recognize(tuple((space0, tag("->"), space0)))(input)
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

// pub(crate) fn maybe_honest_tag_definition<'a, 'b>(
//     input: ek::LocatedSpan<'a, 'b>,
// ) -> ek::IResult<'a, 'b, Optional<> {
//     opt(terminated(symbol_name, arrow))(input)
// }

pub(crate) fn program_instruction<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ProgramInstruction> {
    map(
        pair(opt(tag_definition), program_instruction_fragments),
        |(maybe_tag, fragments)| ProgramInstruction {
            tag: maybe_tag,
            parts: fragments,
        },
    )(input)
}

pub(crate) fn newline<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, char> {
    char('\n')(input)
}

pub(crate) fn directive<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, Vec<ProgramInstruction>> {
    many0(terminated(
        program_instruction,
        ek::expect(newline, "expected newline after a program instruction"),
    ))(input)
}

pub fn parse_source_file(
    body: &str,
    _symtab: &mut SymbolTable,
    errors: &mut Vec<ek::Error>,
) -> Result<Vec<ProgramInstruction>, AssemblerFailure> {
    let (prog_instr, new_errors) = ek::parse(body);
    if !new_errors.is_empty() {
        errors.extend(new_errors.into_iter());
    }
    Ok(prog_instr)
}
