//! Various convenience utilities for splitting 36-bit TX-2 words
//! into smaller components and for joining them together.
use std::ops::Shl;

use crate::onescomplement::unsigned::{Unsigned18Bit, Unsigned36Bit, Unsigned9Bit};

/// Split a 36-bit word into two 18-bit values.
pub fn split_halves(w: Unsigned36Bit) -> (Unsigned18Bit, Unsigned18Bit) {
    (left_half(w), right_half(w))
}

/// Join two 18-bit values into a 36-bit word.
pub fn join_halves(left: Unsigned18Bit, right: Unsigned18Bit) -> Unsigned36Bit {
    Unsigned36Bit::from(left).shl(18) | Unsigned36Bit::from(right)
}

/// Join two quarters into a halfword.
pub fn join_quarters(left: Unsigned9Bit, right: Unsigned9Bit) -> Unsigned18Bit {
    Unsigned18Bit::from(left).shl(9) | Unsigned18Bit::from(right)
}

/// Extract the right (more-significant) halfword from a full word.
pub fn right_half(word: Unsigned36Bit) -> Unsigned18Bit {
    let bits: u64 = u64::from(word);
    Unsigned18Bit::try_from(bits & 0o777_777).unwrap()
}

/// Extract the right (less-significant) halfword from a full word.
pub fn left_half(word: Unsigned36Bit) -> Unsigned18Bit {
    let bits: u64 = u64::from(word) >> 18;
    Unsigned18Bit::try_from(bits & 0o777_777).unwrap()
}

/// Split a halfword into left (more significant) and right (less
/// significant) 9-bit quarters (in the sense that they are quarters
/// of the original 26-bit full word).
pub fn split_halfword(halfword: Unsigned18Bit) -> (Unsigned9Bit, Unsigned9Bit) {
    let bits: u32 = u32::from(halfword);
    (
        Unsigned9Bit::try_from((bits >> 9) & 0o777).unwrap(),
        Unsigned9Bit::try_from((bits) & 0o777).unwrap(),
    )
}

/// Split a 36-bit word into four 9-bit quarters.  The result is a
/// tuple which contains the quarters ordered from most-significant
/// (Q4) to least-significant (Q1).
pub fn quarters(word: Unsigned36Bit) -> [Unsigned9Bit; 4] {
    let (left, right) = split_halves(word);
    let (q4, q3) = split_halfword(left);
    let (q2, q1) = split_halfword(right);
    [q4, q3, q2, q1]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::onescomplement::unsigned::{Unsigned18Bit, Unsigned36Bit, Unsigned9Bit};

    macro_rules! assert_octal_eq {
        ($left:expr, $right:expr $(,)?) => {{
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if !(*left_val == *right_val) {
                        panic!(
                            "Assertion failed: {:>#012o} != {:>#012o}",
                            left_val, right_val
                        );
                    }
                }
            }
        }};
    }

    #[test]
    fn test_join_halves() {
        assert_octal_eq!(
            join_halves(
                Unsigned18Bit::try_from(0o123_456_u32).unwrap(),
                Unsigned18Bit::try_from(0o525_252_u32).unwrap()
            ),
            Unsigned36Bit::try_from(0o123_456_525_252_u64).unwrap()
        );
    }

    #[test]
    fn test_join_quarters() {
        assert_octal_eq!(
            join_quarters(
                Unsigned9Bit::try_from(0o123_u16).unwrap(),
                Unsigned9Bit::try_from(0o456_u16).unwrap()
            ),
            Unsigned18Bit::try_from(0o123_456_u32).unwrap()
        );
    }

    #[test]
    fn test_split_halfword() {
        let h = Unsigned18Bit::try_from(0o123_456_u32).expect("valid test data");
        assert_eq!(
            split_halfword(h),
            (
                Unsigned9Bit::try_from(0o123).unwrap(),
                Unsigned9Bit::try_from(0o456).unwrap()
            )
        );
    }

    #[test]
    fn test_quarters() {
        fn q(n: u16) -> Unsigned9Bit {
            Unsigned9Bit::try_from(n).expect("valid test data")
        }
        assert_eq!(
            quarters(Unsigned36Bit::try_from(0o123_456_525_252_u64).unwrap()),
            [q(0o123), q(0o456), q(0o525), q(0o252)]
        )
    }
}
