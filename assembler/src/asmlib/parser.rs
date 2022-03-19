use std::fmt::{self, Display, Formatter, Write};
use std::num::IntErrorKind;
use std::ops::Range;

//use std::ops::Range;
//use base::prelude::*;
use nom::branch::alt;
use nom::bytes::complete::take_while1;
use nom::character::complete::{char, oct_digit1};
use nom::combinator::{map, map_res, opt};
use nom::multi::{many0, many1};
use nom::sequence::{pair, terminated};

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
pub enum ProgramInstruction {
    Parts(Vec<InstructionFragment>),
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

    pub fn normal_octal_number<'a, 'b>(
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
    pub fn superscript_octal_number<'a, 'b>(
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
    pub fn subscript_octal_number<'a, 'b>(
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

pub(crate) fn program_instruction<'a, 'b>(
    input: ek::LocatedSpan<'a, 'b>,
) -> ek::IResult<'a, 'b, ProgramInstruction> {
    map(many1(program_instruction_fragment), |fragments| {
        ProgramInstruction::Parts(fragments)
    })(input)
}

pub fn newline<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, char> {
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
