use std::fmt::{Display, Write};
use std::num::IntErrorKind;

use base::prelude::*;

use super::super::{ast::*, manuscript::PunchCommand, state::NumeralMode};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) enum Sign {
    Plus,
    Minus,
}

impl Display for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            Sign::Plus => '+',
            Sign::Minus => '-',
        })
    }
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
    assert!(make_u36("+-1", 8).is_err());
    assert!(make_u36("-+1", 8).is_err());
    assert!(make_u36("--1", 8).is_err());
    assert!(make_u36("++1", 8).is_err());
    assert!(make_u36("+ 1", 8).is_err());
    assert!(make_u36("- 1", 8).is_err());
    assert!(make_u36("18", 8).is_err());
    assert!(make_u36("19", 8).is_err());
    assert_eq!(Ok(u36!(19)), make_u36("19", 10));
}

pub(crate) fn make_num(
    digits: &str,
    hasdot: bool,
    state: &NumeralMode,
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_u36(digits, state.radix(hasdot))
}

pub(super) fn punch_address(a: Option<LiteralValue>) -> Result<PunchCommand, String> {
    match a {
        None => Ok(PunchCommand(None)),
        Some(literal) => {
            let value = literal.value();
            match Unsigned18Bit::try_from(value) {
                Err(e) => Err(format!(
                    "PUNCH address value {value:o} is not a valid address: {e}",
                )),
                Ok(halfword) => {
                    let addr: Address = Address::from(halfword);
                    if addr.mark_bit() != Unsigned18Bit::ZERO {
                        Err(format!(
                            "PUNCH address value {addr:o} must not be a deferred address",
                        ))
                    } else {
                        Ok(PunchCommand(Some(addr)))
                    }
                }
            }
        }
    }
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

pub(super) fn is_register_name(name: &str) -> bool {
    matches!(name, "A" | "B" | "C" | "D" | "E")
}
