use std::fmt::{Display, Write};

use super::onescomplement::unsigned::Unsigned36Bit;
use super::quarters::Quarter;

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitPos {
    B1 = 0,
    B2 = 1,
    B3 = 2,
    B4 = 3,
    B5 = 4,
    B6 = 5,
    B7 = 6,
    B8 = 7,
    B9 = 8,
}

impl Display for BitPos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            BitPos::B1 => '1',
            BitPos::B2 => '2',
            BitPos::B3 => '3',
            BitPos::B4 => '4',
            BitPos::B5 => '5',
            BitPos::B6 => '6',
            BitPos::B7 => '7',
            BitPos::B8 => '8',
            BitPos::B9 => '9',
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSelector {
    pub quarter: Quarter,
    /// `bitpos` values 1 to 9 inclusive are normal bit positions in a
    /// quarter.  0 is a valid value but not a valid bit (so a default
    /// will be used when SKM tests bit 0).  10 is the meta bit.  11
    /// is the parity bit stored in memory.  12 is the parity value
    /// computed from the bits stored in memory.
    pub bitpos: BitPos,
}

impl BitSelector {
    pub const fn raw_mask(&self) -> u64 {
        let shift = (self.quarter as u32) * 9 + (self.bitpos as u32);
        1_u64 << shift
    }

    pub fn mask(&self) -> Unsigned36Bit {
        Unsigned36Bit::try_from(self.raw_mask())
            .expect("bit selector mask values cannot be outside the range of Unsigned36Bit")
    }
}

impl Display for BitSelector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", &self.quarter, &self.bitpos)
    }
}

#[cfg(test)]
const fn bit_select_mask(quarter: Quarter, bitpos: BitPos) -> u64 {
    BitSelector { quarter, bitpos }.raw_mask()
}

#[test]
fn test_bit_select_mask_q1() {
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B1),
        0o001_u64,
        "failed for bit 1.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B2),
        0o002_u64,
        "failed for bit 1.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B3),
        0o004_u64,
        "failed for bit 1.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B4),
        0o010_u64,
        "failed for bit 1.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B5),
        0o020_u64,
        "failed for bit 1.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B6),
        0o040_u64,
        "failed for bit 1.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B7),
        0o100_u64,
        "failed for bit 1.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B8),
        0o200_u64,
        "failed for bit 1.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, BitPos::B9),
        0o400_u64,
        "failed for bit 1.9"
    );
}

#[test]
fn test_bit_select_mask_q2() {
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B1),
        0o001_000_u64,
        "failed for bit 2.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B2),
        0o002_000_u64,
        "failed for bit 2.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B3),
        0o004_000_u64,
        "failed for bit 2.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B4),
        0o010_000_u64,
        "failed for bit 2.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B5),
        0o020_000_u64,
        "failed for bit 2.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B6),
        0o040_000_u64,
        "failed for bit 2.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B7),
        0o100_000_u64,
        "failed for bit 2.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B8),
        0o200_000_u64,
        "failed for bit 2.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, BitPos::B9),
        0o400_000_u64,
        "failed for bit 2.9"
    );
}

#[test]
fn test_bit_select_mask_q3() {
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B1),
        0o001_000_000_u64,
        "failed for bit 3.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B2),
        0o002_000_000_u64,
        "failed for bit 3.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B3),
        0o004_000_000_u64,
        "failed for bit 3.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B4),
        0o010_000_000_u64,
        "failed for bit 3.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B5),
        0o020_000_000_u64,
        "failed for bit 3.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B6),
        0o040_000_000_u64,
        "failed for bit 3.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B7),
        0o100_000_000_u64,
        "failed for bit 3.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B8),
        0o200_000_000_u64,
        "failed for bit 3.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, BitPos::B9),
        0o400_000_000_u64,
        "failed for bit 3.9"
    );
}

#[test]
fn test_bit_select_mask_q4() {
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B1),
        0o001_000_000_000_u64,
        "failed for bit 4.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B2),
        0o002_000_000_000_u64,
        "failed for bit 4.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B3),
        0o004_000_000_000_u64,
        "failed for bit 4.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B4),
        0o010_000_000_000_u64,
        "failed for bit 4.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B5),
        0o020_000_000_000_u64,
        "failed for bit 4.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B6),
        0o040_000_000_000_u64,
        "failed for bit 4.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B7),
        0o100_000_000_000_u64,
        "failed for bit 4.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B8),
        0o200_000_000_000_u64,
        "failed for bit 4.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, BitPos::B9),
        0o400_000_000_000_u64,
        "failed for bit 4.9"
    );
}

#[cfg(test)]
fn all_bit_selectors() -> Vec<BitSelector> {
    let mut result = Vec::with_capacity(36);
    for quarter in [Quarter::Q1, Quarter::Q2, Quarter::Q3, Quarter::Q4] {
        for bitpos in [
            BitPos::B1,
            BitPos::B2,
            BitPos::B3,
            BitPos::B4,
            BitPos::B5,
            BitPos::B6,
            BitPos::B7,
            BitPos::B8,
            BitPos::B9,
        ] {
            result.push(BitSelector { quarter, bitpos })
        }
    }
    result
}

pub const fn bit_select(value: Unsigned36Bit, selector: BitSelector) -> bool {
    value.bits & selector.raw_mask() != 0
}

#[test]
fn test_bit_select() {
    for (bitpos, selector) in all_bit_selectors().into_iter().enumerate() {
        let just_that_bit: Unsigned36Bit =
            Unsigned36Bit::try_from(1_u64 << bitpos).expect("test bit should not be out of range");
        for selector_to_test in all_bit_selectors() {
            let found_value: bool = bit_select(just_that_bit, selector_to_test);
            if selector_to_test == selector {
                // The quarter and bit number is the one we had set, so the value should be 1.
                assert!(
                    found_value,
                    "bit {selector_to_test} should be set in {just_that_bit:012o}"
                );
            } else {
                assert!(
                    !found_value,
                    "bit {selector_to_test} should be unset in {just_that_bit:012o}"
                );
            }
        }
    }
}
