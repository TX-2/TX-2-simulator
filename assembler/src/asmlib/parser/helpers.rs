use std::error::Error;
use std::fmt::{self, Display};
use std::num::IntErrorKind;

use base::prelude::*;

use super::super::ast::*;
use super::super::state::NumeralMode;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(super) enum Sign {
    Plus,
    Minus,
}

pub(super) fn make_u36(s: &str, radix: u32) -> Result<Unsigned36Bit, StringConversionFailed> {
    match u64::from_str_radix(s, radix) {
        Ok(n) => n.try_into().map_err(StringConversionFailed::Range),
        Err(e) => match e.kind() {
            IntErrorKind::Empty => Err(StringConversionFailed::EmptyInput),
            IntErrorKind::InvalidDigit => {
                match s.chars().find(|ch| ch.to_digit(radix).is_none()) {
                    Some(ch) => Err(StringConversionFailed::NotOctal(ch)),
                    None => {
                        panic!("at least one character of '{s}' is known to be invalid in base {radix}");
                    }
                }
            }
            IntErrorKind::PosOverflow => {
                Err(StringConversionFailed::Range(ConversionFailed::TooLarge))
            }
            _ => unreachable!(),
        },
    }
}

#[test]
fn test_make_u36() {
    assert_eq!(Ok(u36!(0)), make_u36("0", 8));
    assert_eq!(Ok(u36!(0)), make_u36("+0", 8));
    assert_eq!(Ok(u36!(1)), make_u36("1", 8));
    assert_eq!(Ok(u36!(1)), make_u36("1", 10));
    assert_eq!(Ok(u36!(1)), make_u36("+1", 8));
    assert_eq!(Ok(u36!(1)), make_u36("+1", 8));
    assert!(make_u36("+1+1", 8).is_err());
    assert!(make_u36("18", 8).is_err());
    assert!(make_u36("19", 8).is_err());
    assert_eq!(Ok(u36!(19)), make_u36("19", 10));
}

pub(super) fn make_num(
    sign: Option<Sign>,
    digits: &str,
    hasdot: bool,
    state: &NumeralMode,
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_u36(digits, state.radix(hasdot)).map(|n| {
        if let Some(Sign::Minus) = sign {
            Unsigned36Bit::ZERO.wrapping_sub(n)
        } else {
            n
        }
    })
}

//// //pub(super) fn make_num_from_span(
//// //    (sign, digits, dot): (Option<char>, ek::LocatedSpan, Option<ek::LocatedSpan>),
//// //) -> Result<Unsigned36Bit, StringConversionFailed> {
//// //    make_num((sign, &digits, digits.extra.radix(dot.is_some())))
//// //}

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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct InvalidSymexChar(char);

impl Error for InvalidSymexChar {}

impl Display for InvalidSymexChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "'{}' is not valid at this point in a symbol name",
            self.0
        )
    }
}

pub(crate) fn convert_superscript_digit(ch: char) -> Result<char, ()> {
    match ch {
        '\u{2070}' => Ok('0'),
        '\u{00B9}' => Ok('1'),
        '\u{00B2}' => Ok('2'),
        '\u{00B3}' => Ok('3'),
        '\u{2074}' => Ok('4'),
        '\u{2075}' => Ok('5'),
        '\u{2076}' => Ok('6'),
        '\u{2077}' => Ok('7'),
        '\u{2078}' => Ok('8'),
        '\u{2079}' => Ok('9'),
        _ => Err(()),
    }
}

pub(crate) fn convert_subcript_digit(ch: char) -> Result<char, ()> {
    match ch {
        '\u{2080}' => Ok('0'),
        '\u{2081}' => Ok('1'),
        '\u{2082}' => Ok('2'),
        '\u{2083}' => Ok('3'),
        '\u{2084}' => Ok('4'),
        '\u{2085}' => Ok('5'),
        '\u{2086}' => Ok('6'),
        '\u{2087}' => Ok('7'),
        '\u{2088}' => Ok('8'),
        '\u{2089}' => Ok('9'),
        _ => Err(()),
    }
}

pub(super) fn is_register_name(name: &str) -> bool {
    matches!(name, "A" | "B" | "C" | "D" | "E")
}
