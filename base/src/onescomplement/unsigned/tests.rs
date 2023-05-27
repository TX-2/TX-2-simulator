use std::ops::Shl;
use std::ops::Shr;

use super::{ConversionFailed, Unsigned36Bit, Unsigned9Bit};

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
fn test_unsigned9bit_max() {
    assert_eq!(Unsigned9Bit::MAX.bits, 0o777);
}

#[test]
fn test_unsigned9bit_min() {
    assert_eq!(Unsigned9Bit::MIN.bits, 0);
}

#[test]
fn test_from_u8() {
    assert_eq!(Unsigned9Bit::from(0_u8).bits, 0_u16);
    assert_eq!(Unsigned9Bit::from(1_u8).bits, 1_u16);
    assert_eq!(Unsigned9Bit::from(0o377_u8).bits, 0o377_u16);
}

#[test]
fn test_try_from_unsigned9bit_u8() {
    assert_eq!(u8::try_from(Unsigned9Bit::from(0_u8)), Ok(0_u8));
    assert_eq!(u8::try_from(Unsigned9Bit::from(1_u8)), Ok(1_u8));
    assert_eq!(u8::try_from(Unsigned9Bit::from(0o377_u8)), Ok(0o377_u8));
    assert_eq!(
        u8::try_from(Unsigned9Bit {
            bits: 0b011_111_111_u16
        }),
        Ok(0o377_u8)
    );
    // Setting the top bit doesn't make these values negative, unlike Signed9Bit.
    assert_eq!(
        u8::try_from(Unsigned9Bit {
            bits: 0b111_111_110_u16
        }),
        Err(ConversionFailed::TooLarge)
    );
    assert_eq!(
        u8::try_from(Unsigned9Bit {
            bits: 0b110_000_000_u16
        }),
        Err(ConversionFailed::TooLarge)
    );
}

#[test]
fn test_i8_round_tripping() {
    let mut prev: Option<Unsigned9Bit> = None;
    for i in 0..i8::MAX {
        let q: Unsigned9Bit = Unsigned9Bit::try_from(i).unwrap();
        if let Some(qprev) = prev {
            assert!(
                q > qprev,
                "failed to round-trip {}: {:?} should be greater than {:?}",
                i,
                q,
                qprev
            );
        }
        prev = Some(q);
        match i8::try_from(q) {
            Ok(out) => {
                assert_eq!(i, out, "Round trip failed for {}->{:?}->{}", i, &q, out);
            }
            Err(e) => {
                panic!(
                    "Unexpected overflow when round-tripping  {}->{:?}-> [conversion to i8 failed with error {}]",
                    i, &q, e);
            }
        }
    }
}

#[test]
fn test_u8_round_tripping() {
    let mut prev: Option<Unsigned9Bit> = None;
    for i in u8::MIN..u8::MAX {
        let q: Unsigned9Bit = Unsigned9Bit::from(i);
        if let Some(qprev) = prev {
            assert!(
                q > qprev,
                "failed to round-trip {}: {:?} should be greater than {:?}",
                i,
                q,
                qprev
            );
        }
        prev = Some(q);
        match u8::try_from(q) {
            Ok(out) => {
                assert_eq!(i, out, "Round trip failed for {}->{:?}->{}", i, &q, out);
            }
            Err(e) => {
                panic!(
                    "Unexpected overflow when round-tripping  {}->{:?}-> [conversion to i8 failed with error {}]",
                    i, &q, e);
            }
        }
    }
}

#[test]
fn test_try_from_i8_unsigned9bit() {
    assert_octal_eq!(Unsigned9Bit::try_from(0_i8).unwrap().bits, 0_u16);
    assert_octal_eq!(Unsigned9Bit::try_from(1_i8).unwrap().bits, 1_u16);
    assert_octal_eq!(Unsigned9Bit::try_from(127_i8).unwrap().bits, 127_u16);

    assert_eq!(
        Unsigned9Bit::try_from(-1_i8),
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        Unsigned9Bit::try_from(-2_i8),
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        Unsigned9Bit::try_from(-8_i8),
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        Unsigned9Bit::try_from(-128_i8),
        Err(ConversionFailed::TooSmall)
    );
}

#[test]
fn test_unsigned9bit_zero_values() {
    const ZERO: Unsigned9Bit = Unsigned9Bit { bits: 0_u16 };
    assert_eq!(u16::from(ZERO), 0, "zero should convert to 0_u16");
    assert_eq!(u8::try_from(ZERO), Ok(0), "zero should convert to 0_u8");

    // The value that would be +0 in Signed9Bit is just a large value in Unsigned9Bit.
    const CAREFUL_NOW: Unsigned9Bit = Unsigned9Bit {
        bits: 0b111_111_111_u16,
    };
    assert_eq!(u16::try_from(CAREFUL_NOW), Ok(0o777));
}

#[test]
fn test_from_unsigned9bit_to_i8() {
    assert_eq!(i8::try_from(Unsigned9Bit { bits: 0 }), Ok(0_i8));
    assert_eq!(i8::try_from(Unsigned9Bit { bits: 1 }), Ok(1_i8));
    assert_eq!(i8::try_from(Unsigned9Bit { bits: 127_u16 }), Ok(127_i8));
    assert_eq!(
        i8::try_from(Unsigned9Bit {
            bits: 0b111_111_110_u16
        }),
        Err(ConversionFailed::TooLarge)
    );
    assert_eq!(
        i8::try_from(Unsigned9Bit {
            bits: 0b111_111_101_u16
        }),
        Err(ConversionFailed::TooLarge)
    );
    assert_eq!(
        i8::try_from(Unsigned9Bit {
            bits: 0b110_111_101_u16
        }),
        Err(ConversionFailed::TooLarge)
    );
    assert_eq!(
        i8::try_from(Unsigned9Bit {
            bits: 0b110_000_000_u16
        }),
        Err(ConversionFailed::TooLarge)
    );
    assert!(i8::try_from(Unsigned9Bit::MAX).is_err());
    assert_eq!(i8::try_from(Unsigned9Bit::MIN), Ok(0));
}

#[test]
fn test_from_u16_to_unsigned9bit() {
    assert_octal_eq!(Unsigned9Bit::try_from(0_u16).unwrap().bits, 0_u16);
    assert_octal_eq!(Unsigned9Bit::try_from(1_u16).unwrap().bits, 1_u16);
    assert_octal_eq!(Unsigned9Bit::try_from(0o377_u16).unwrap().bits, 0o377_u16);
    assert_octal_eq!(Unsigned9Bit::try_from(0o400_u16).unwrap().bits, 0o400);
    assert_eq!(
        Unsigned9Bit::try_from(0o1000_u16),
        Err(ConversionFailed::TooLarge)
    );
}

#[test]
fn test_from_unsigned9bit_to_u16() {
    assert_octal_eq!(u16::from(Unsigned9Bit { bits: 0 }), 0);
    assert_octal_eq!(u16::from(Unsigned9Bit { bits: 1 }), 1);
    assert_octal_eq!(u16::from(Unsigned9Bit { bits: 0o377_u16 }), 0o377_u16);
    assert_octal_eq!(u16::from(Unsigned9Bit { bits: 0o400_u16 }), 0o400_u16);
    assert_octal_eq!(u16::from(Unsigned9Bit { bits: 0o477_u16 }), 0o477_u16);
    assert_octal_eq!(u16::from(Unsigned9Bit { bits: 0o777_u16 }), 0o777_u16);
}

#[test]
fn test_unsigned9bit_ord() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert!(zero < one);
    assert!(!(one < zero));
    assert!(!(zero < zero));
    assert!(!(one < one));

    assert!(one > zero);
    assert!(!(zero > zero));
    assert!(!(one > one));
    assert!(!(zero > one));

    assert!(Unsigned9Bit::MIN < Unsigned9Bit::MAX);
    assert!(Unsigned9Bit::MAX > Unsigned9Bit::MIN);
}

#[test]
fn test_unsigned9bit_eq() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!(zero, zero);
    assert_eq!(one, one);

    let another_one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!(
        one, another_one,
        "ensure we don't confuse identy with equality"
    );
}

#[test]
fn test_unsigned9bit_checked_add() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(zero.checked_add(zero), Some(zero));
    assert_eq!(zero.checked_add(one), Some(one));
    assert_eq!(one.checked_add(zero), Some(one));
    assert_eq!(Unsigned9Bit::MAX.checked_add(zero), Some(Unsigned9Bit::MAX));
    assert_eq!(Unsigned9Bit::MIN.checked_add(zero), Some(Unsigned9Bit::MIN));

    // Test the basics: 1+1=2
    let two: Unsigned9Bit = Unsigned9Bit::from(2_u8);
    assert_eq!(one.checked_add(one), Some(two));

    // Verify that we correctly detect overflow
    assert_eq!(Unsigned9Bit::MAX.checked_add(one), None);
}

#[test]
fn test_unsigned9bit_checked_sub() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(zero.checked_sub(zero), Some(zero));
    assert_eq!(one.checked_sub(zero), Some(one));
    assert_eq!(Unsigned9Bit::MAX.checked_sub(zero), Some(Unsigned9Bit::MAX));
    assert_eq!(Unsigned9Bit::MIN.checked_sub(zero), Some(Unsigned9Bit::MIN));

    // Test the basics: 2-1=1
    let two: Unsigned9Bit = Unsigned9Bit::from(2_u8);
    assert_eq!(two.checked_sub(one), Some(one));
    assert_eq!(two.checked_sub(two), Some(zero));

    // Verify that we correctly detect overflow
    assert_eq!(Unsigned9Bit::MIN.checked_sub(one), None);
    assert_eq!(zero.checked_sub(one), None); // same thing

    assert_eq!(
        u16::from(Unsigned9Bit::MAX.checked_sub(one).unwrap()),
        510_u16
    );
}

#[test]
fn test_unsigned9bit_abs() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!(zero, zero.abs());
    assert_eq!(one, one.abs());
}

#[test]
fn test_unsigned9bit_checked_abs() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!((zero, false), zero.overflowing_abs());
    assert_eq!((one, false), one.overflowing_abs());
}

#[test]
fn test_unsigned9bit_not() {
    let all_zeroes = Unsigned9Bit { bits: 0 };
    let all_ones = Unsigned9Bit { bits: 0o777 };
    assert_eq!(!all_zeroes, all_ones);
    assert_eq!(!all_ones, all_zeroes);

    assert_eq!(!Unsigned9Bit { bits: 1 }, Unsigned9Bit { bits: 0o776 });
    assert_eq!(!Unsigned9Bit { bits: 0o40 }, Unsigned9Bit { bits: 0o737 });
}

#[test]
fn test_unsigned9bit_and() {
    let all_zeroes = Unsigned9Bit { bits: 0 };
    let all_ones = Unsigned9Bit { bits: 0o777 };
    assert_eq!(all_zeroes & all_zeroes, all_zeroes);
    assert_eq!(all_ones & all_ones, all_ones);
    assert_eq!(all_ones & all_zeroes, all_zeroes);

    let three = Unsigned9Bit { bits: 0o3 };
    let two = Unsigned9Bit { bits: 0o2 };
    assert_eq!(three & two, two);
}

#[test]
fn test_unsigned9bit_impl_and() {
    let all_zeroes = Unsigned9Bit { bits: 0 };
    let all_ones = Unsigned9Bit { bits: 0o777 };
    assert_eq!(all_zeroes.and(0_u16), all_zeroes);
    assert_eq!(all_ones.and(0o777_u16), all_ones);
    assert_eq!(all_ones.and(0_u16), all_zeroes);

    let three = Unsigned9Bit { bits: 0o3 };
    let two = Unsigned9Bit { bits: 0o2 };
    assert_eq!(three & 0o2_u16, two);
}

#[test]
fn test_unsigned9bit_or() {
    let all_zeroes = Unsigned9Bit { bits: 0 };
    let all_ones = Unsigned9Bit { bits: 0o777 };
    assert_eq!(all_zeroes & all_zeroes, all_zeroes);
    assert_eq!(all_ones | all_ones, all_ones);
    assert_eq!(all_ones | all_zeroes, all_ones);

    let three = Unsigned9Bit { bits: 0o3 };
    let two = Unsigned9Bit { bits: 0o2 };
    assert_eq!(three | two, three);
    assert_eq!(three | all_zeroes, three);
    assert_eq!(three | all_ones, all_ones);
}

#[test]
fn test_unsigned9bit_shr() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!(zero.shr(zero), zero);
    assert_eq!(zero.shr(one), zero);
    assert_eq!(one.shr(zero), one);

    // Shifting the least significant bit off the right-hand side puts
    // it into the most-signficant position.
    assert_eq!(one.shr(one), Unsigned9Bit::ZERO | (1_u16 << 8));

    // If we shift a bit more places to the right than there are bit
    // positions, it just ends up in the position determined by the
    // obvious modulus operation (and e.g. does not get zeroed).
    //
    // Shift right by   ... is equivalent to shifting right by
    //              9                                        0
    //             10                                        1
    //             11                                        2
    //             12                                        3
    //             13                                        4
    // ...
    //             31                                        4
    assert_eq!(one.shr(Unsigned9Bit::from(9_u8)), one);
    assert_eq!(
        one.shr(Unsigned9Bit::from(10_u8)),
        Unsigned9Bit::try_from(0o400).unwrap()
    );
    assert_eq!(
        one.shr(Unsigned9Bit::from(11_u8)),
        Unsigned9Bit::try_from(0o200).unwrap()
    );
    assert_eq!(
        one.shr(Unsigned9Bit::from(12_u8)),
        Unsigned9Bit::try_from(0o100).unwrap()
    );
    assert_eq!(
        one.shr(Unsigned9Bit::from(13_u8)),
        Unsigned9Bit::try_from(0o040).unwrap()
    );
    assert_eq!(
        one.shr(Unsigned9Bit::from(31_u8)),
        Unsigned9Bit::try_from(0o040).unwrap()
    );

    let all_ones = Unsigned9Bit { bits: 0o777 };
    assert_eq!(all_ones.shr(zero), all_ones);
    assert_eq!(all_ones.shr(one), all_ones);
    assert_eq!(all_ones.shr(all_ones), all_ones);
}

#[test]
fn test_unsigned9bit_shl() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!(zero.shl(zero), zero);
    assert_eq!(zero.shl(one), zero);
    assert_eq!(one.shl(zero), one);

    let two: Unsigned9Bit = Unsigned9Bit::from(2_u8);
    assert_eq!(one.shl(one), two);

    assert_octal_eq!(
        Unsigned9Bit::try_from(0o400).unwrap().shl(1),
        Unsigned9Bit::from(1_u8)
    );

    assert_octal_eq!(
        Unsigned9Bit::try_from(0o020).unwrap().shl(14),
        Unsigned9Bit::from(1_u8)
    );

    assert_eq!(Unsigned9Bit::ZERO, Unsigned9Bit::ZERO << Unsigned9Bit::ZERO);
    assert_eq!(Unsigned9Bit::ZERO, Unsigned9Bit::ZERO << Unsigned9Bit::ONE);
    assert_eq!(Unsigned9Bit::ONE, Unsigned9Bit::ONE << Unsigned9Bit::ZERO);
    assert_eq!(
        Unsigned9Bit::from(4_u8),
        Unsigned9Bit::ONE << Unsigned9Bit::from(2_u8)
    );
}

#[test]
fn test_unsigned9bit_xor() {
    let zero: Unsigned9Bit = Unsigned9Bit::from(0_u8);
    let one: Unsigned9Bit = Unsigned9Bit::from(1_u8);
    assert_eq!(zero ^ zero, zero);
    assert_eq!(one ^ one, zero);
    assert_eq!(one ^ zero, one);
    assert_eq!(zero ^ one, one);
}

#[test]
fn test_unsigned36bit_checked_mul() {
    let two: Unsigned36Bit = Unsigned36Bit::from(2_u8);
    let four: Unsigned36Bit = Unsigned36Bit::from(4_u8);
    assert_eq!(two.checked_mul(two), Some(four));
}

#[test]
fn test_unsigned36bit_wrapping_mul() {
    let two: Unsigned36Bit = Unsigned36Bit::from(2_u8);
    let four: Unsigned36Bit = Unsigned36Bit::from(4_u8);
    assert_eq!(two.wrapping_mul(two), four);
}

#[test]
fn test_unsigned36bit_checked_div() {
    let two: Unsigned36Bit = Unsigned36Bit::from(2_u8);
    let four: Unsigned36Bit = Unsigned36Bit::from(4_u8);
    assert_eq!(four.checked_div(two), Some(two));

    assert_eq!(four.checked_div(Unsigned36Bit::ZERO), None);
}
