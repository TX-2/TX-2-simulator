use std::fmt::Write;
use std::num::IntErrorKind;
use std::ops::Range;

//use std::ops::Range;
//use base::prelude::*;
use nom::branch::alt;
use nom::bytes::complete::take_while1;
use nom::character::complete::{char, oct_digit1};
use nom::combinator::{map, map_res, opt};
use nom::multi::many0;
use nom::sequence::pair;

use crate::ek::{self, ToRange};
use crate::types::*;
use base::prelude::*;

#[derive(Debug)]
pub struct ErrorLocation {
    line: u32,
    columns: Option<Range<usize>>,
}

impl<'a> From<&ek::LocatedSpan<'a>> for ErrorLocation {
    fn from(span: &ek::LocatedSpan<'a>) -> ErrorLocation {
        let r: Range<usize> = (*span).to_range();
        ErrorLocation {
            line: span.location_line(),
            columns: Some(r),
        }
    }
}

#[derive(Debug)]
pub enum ProgramInstruction {
    Parts(Vec<InstructionFragment>),
    Error,
}

impl ProgramInstruction {
    pub fn empty_line_representation() -> ProgramInstruction {
        ProgramInstruction::Parts(Vec::new())
    }
}

fn maybe_superscript_sign(input: ek::LocatedSpan) -> ek::IResult<Option<char>> {
    opt(alt((
        char('\u{207B}'), // U+207B: superscript minus
        char('\u{207A}'), // U+207A: superscript plus
    )))(input)
}

fn maybe_subscript_sign(input: ek::LocatedSpan) -> ek::IResult<Option<char>> {
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

fn normal_literal_instruction_fragment(input: ek::LocatedSpan) -> ek::IResult<InstructionFragment> {
    fn maybe_sign(input: ek::LocatedSpan) -> ek::IResult<Option<char>> {
        opt(alt((char('-'), char('+'))))(input)
    }

    pub fn normal_octal_number(input: ek::LocatedSpan) -> ek::IResult<Unsigned36Bit> {
        map_res(pair(maybe_sign, oct_digit1), make_num_from_span)(input)
    }

    map(normal_octal_number, |n| InstructionFragment {
        elevation: Elevation::Normal,
        value: n,
    })(input)
}

fn superscript_literal_instruction_fragment(
    input: ek::LocatedSpan,
) -> ek::IResult<InstructionFragment> {
    pub fn superscript_octal_number(input: ek::LocatedSpan) -> ek::IResult<Unsigned36Bit> {
        fn is_superscript_oct_digit(ch: char) -> bool {
            superscript_oct_digit_to_value(ch).is_some()
        }

        fn superscript_oct_digit1(input: ek::LocatedSpan) -> ek::IResult<ek::LocatedSpan> {
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

fn subscript_literal_instruction_fragment(
    input: ek::LocatedSpan,
) -> ek::IResult<InstructionFragment> {
    pub fn subscript_octal_number(input: ek::LocatedSpan) -> ek::IResult<Unsigned36Bit> {
        fn is_subscript_oct_digit(ch: char) -> bool {
            subscript_oct_digit_to_value(ch).is_some()
        }

        fn subscript_oct_digit1(input: ek::LocatedSpan) -> ek::IResult<ek::LocatedSpan> {
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

pub fn program_instruction_fragment(input: ek::LocatedSpan) -> ek::IResult<InstructionFragment> {
    alt((
        normal_literal_instruction_fragment,
        superscript_literal_instruction_fragment,
        subscript_literal_instruction_fragment,
    ))(input)
}

pub fn program_instruction(input: ek::LocatedSpan) -> ek::IResult<ProgramInstruction> {
    map(many0(program_instruction_fragment), |fragments| {
        ProgramInstruction::Parts(fragments)
    })(input)
}

pub fn assemble_line(
    line_number: usize,
    line: &str,
    _symtab: &mut SymbolTable,
    errors: &mut Vec<ek::Error>,
) -> Result<Option<ProgramInstruction>, AssemblerFailure> {
    let (prog_instr, new_errors) = ek::parse(line_number, line);
    if !new_errors.is_empty() {
        errors.extend(new_errors.into_iter());
        Ok(Some(ProgramInstruction::Error))
    } else {
        match prog_instr {
            ProgramInstruction::Parts(inst) => Ok(if inst.is_empty() {
                None
            } else {
                Some(ProgramInstruction::Parts(inst))
            }),
            ProgramInstruction::Error => unreachable!(),
        }
    }
}
