use super::onescomplement::unsigned::Unsigned36Bit;

#[repr(u8)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
pub enum Quarter {
    Q1 = 0,
    Q2 = 1,
    Q3 = 2,
    Q4 = 3,
}

#[repr(u8)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
pub enum QuarterBit {
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

const fn bit_select_mask(quarter: Quarter, bit: QuarterBit) -> u64 {
    let shift = (quarter as u32) * 9 + (bit as u32);
    1_u64 << shift
}

#[test]
fn test_bit_select_mask_q1() {
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B1),
        0o001_u64,
        "failed for bit 1.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B2),
        0o002_u64,
        "failed for bit 1.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B3),
        0o004_u64,
        "failed for bit 1.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B4),
        0o010_u64,
        "failed for bit 1.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B5),
        0o020_u64,
        "failed for bit 1.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B6),
        0o040_u64,
        "failed for bit 1.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B7),
        0o100_u64,
        "failed for bit 1.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B8),
        0o200_u64,
        "failed for bit 1.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q1, QuarterBit::B9),
        0o400_u64,
        "failed for bit 1.9"
    );
}

#[test]
fn test_bit_select_mask_q2() {
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B1),
        0o001_000_u64,
        "failed for bit 2.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B2),
        0o002_000_u64,
        "failed for bit 2.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B3),
        0o004_000_u64,
        "failed for bit 2.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B4),
        0o010_000_u64,
        "failed for bit 2.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B5),
        0o020_000_u64,
        "failed for bit 2.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B6),
        0o040_000_u64,
        "failed for bit 2.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B7),
        0o100_000_u64,
        "failed for bit 2.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B8),
        0o200_000_u64,
        "failed for bit 2.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q2, QuarterBit::B9),
        0o400_000_u64,
        "failed for bit 2.9"
    );
}

#[test]
fn test_bit_select_mask_q3() {
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B1),
        0o001_000_000_u64,
        "failed for bit 3.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B2),
        0o002_000_000_u64,
        "failed for bit 3.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B3),
        0o004_000_000_u64,
        "failed for bit 3.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B4),
        0o010_000_000_u64,
        "failed for bit 3.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B5),
        0o020_000_000_u64,
        "failed for bit 3.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B6),
        0o040_000_000_u64,
        "failed for bit 3.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B7),
        0o100_000_000_u64,
        "failed for bit 3.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B8),
        0o200_000_000_u64,
        "failed for bit 3.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q3, QuarterBit::B9),
        0o400_000_000_u64,
        "failed for bit 3.9"
    );
}

#[test]
fn test_bit_select_mask_q4() {
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B1),
        0o001_000_000_000_u64,
        "failed for bit 4.1"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B2),
        0o002_000_000_000_u64,
        "failed for bit 4.2"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B3),
        0o004_000_000_000_u64,
        "failed for bit 4.3"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B4),
        0o010_000_000_000_u64,
        "failed for bit 4.4"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B5),
        0o020_000_000_000_u64,
        "failed for bit 4.5"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B6),
        0o040_000_000_000_u64,
        "failed for bit 4.6"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B7),
        0o100_000_000_000_u64,
        "failed for bit 4.7"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B8),
        0o200_000_000_000_u64,
        "failed for bit 4.8"
    );
    assert_eq!(
        bit_select_mask(Quarter::Q4, QuarterBit::B9),
        0o400_000_000_000_u64,
        "failed for bit 4.9"
    );
}

pub const fn bit_select(value: Unsigned36Bit, quarter: Quarter, bit: QuarterBit) -> bool {
    let mask = bit_select_mask(quarter, bit);
    value.bits & mask != 0
}

#[cfg(test)]
fn all_bit_selectors() -> Vec<(Quarter, QuarterBit)> {
    let mut result = Vec::with_capacity(36);
    for q in [Quarter::Q1, Quarter::Q2, Quarter::Q3, Quarter::Q4] {
        for b in [
            QuarterBit::B1,
            QuarterBit::B2,
            QuarterBit::B3,
            QuarterBit::B4,
            QuarterBit::B5,
            QuarterBit::B6,
            QuarterBit::B7,
            QuarterBit::B8,
            QuarterBit::B9,
        ] {
            result.push((q, b));
        }
    }
    result
}

#[test]
fn test_bit_select() {
    for (bitpos, (quarter_of_bit_to_set, bit_to_set)) in all_bit_selectors().into_iter().enumerate()
    {
        let just_that_bit: Unsigned36Bit =
            Unsigned36Bit::try_from(1_u64 << bitpos).expect("test bit should not be out of range");
        for (quarter_to_test, bit_to_test) in all_bit_selectors() {
            if (quarter_to_test, bit_to_test) == (quarter_of_bit_to_set, bit_to_set) {
                // The quarter and bit number is the one we had set, so the value should be 1.
                assert!(
                    bit_select(just_that_bit, quarter_to_test, bit_to_test),
                    "bit {quarter_to_test:?}.{bit_to_test:?} should be set in {just_that_bit:012o}"
                );
            } else {
                assert!(
                    !bit_select(just_that_bit, quarter_to_test, bit_to_test),
                    "bit {quarter_to_test:?}.{bit_to_test:?} should be unset in {just_that_bit:012o}"
                );
            }
        }
    }
}
