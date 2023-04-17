use std::fmt::Write;
use std::num::IntErrorKind;

use base::prelude::*;

use super::super::ast::*;
use super::super::ek;

pub(super) fn make_u36(s: &str, radix: u32) -> Result<Unsigned36Bit, StringConversionFailed> {
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

pub(super) fn make_num(
    (sign, digits, radix): (Option<char>, &str, u32),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    let n = make_u36(digits, radix)?;
    if let Some('-') = sign {
        Ok(Unsigned36Bit::ZERO.wrapping_sub(n))
    } else {
        Ok(n)
    }
}

pub(super) fn make_num_from_span(
    (sign, digits, dot): (Option<char>, ek::LocatedSpan, Option<ek::LocatedSpan>),
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_num((sign, &digits, digits.extra.radix(dot.is_some())))
}

pub(super) fn maybe_superscript_sign_to_maybe_regular_sign(
    maybe_superscript_sign: Option<char>,
) -> Option<char> {
    maybe_superscript_sign.map(|ch| match ch {
        '\u{207B}' => '-', // U+207B: superscript minus
        '\u{207A}' => '+', // U+207A: superscript plus
        _ => unreachable!(),
    })
}

pub(super) fn maybe_subscript_sign_to_maybe_regular_sign(
    maybe_subscript_sign: Option<char>,
) -> Option<char> {
    maybe_subscript_sign.map(|ch| match ch {
        '\u{208B}' => '-', // U+208B: subscript minus
        '\u{208A}' => '+', // U+208A: subscript plus
        _ => unreachable!(),
    })
}

pub(super) fn superscript_oct_digit_to_value(ch: char) -> Option<u8> {
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

pub(super) fn subscript_oct_digit_to_value(ch: char) -> Option<u8> {
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

pub(super) fn make_superscript_num(
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

pub(super) fn make_subscript_num(
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DecodedOpcode {
    Valid(Unsigned6Bit),
    Invalid,
}

pub(super) fn opcode_to_num(input: &str) -> DecodedOpcode {
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

pub(super) fn punch_address(a: Option<LiteralValue>) -> Result<PunchCommand, String> {
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

pub(super) fn manuscript_lines_to_blocks(
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

/// Some instructions are assembled with the hold bit automatically
/// set.  These are JPX, JNX, LDE, ITE.  See Users Handbook, section
/// 4-3.2 on page 4-5.
pub(super) fn opcode_auto_hold_bit(opcode: Unsigned6Bit) -> u64 {
    if matches!(u8::from(opcode), 0o06 | 0o07 | 0o20 | 0o40) {
        1 << 35
    } else {
        0
    }
}

pub(super) fn is_nonblank_simple_symex_char(c: char) -> bool {
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

pub(super) fn is_register_name(name: &str) -> bool {
    matches!(name, "A" | "B" | "C" | "D" | "E")
}
