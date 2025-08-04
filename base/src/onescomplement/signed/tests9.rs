use super::{ConversionFailed, Signed9Bit};

macro_rules! assert_octal_eq {
    ($left:expr_2021, $right:expr_2021 $(,)?) => {{
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
fn test_from_u8() {
    assert_eq!(Signed9Bit::from(0_u8).bits, 0_u16);
    assert_eq!(Signed9Bit::from(1_u8).bits, 1_u16);
    assert_eq!(Signed9Bit::from(0o377_u8).bits, 0o377_u16);
}

#[test]
fn test_try_from_signed9bit_u8() {
    assert_eq!(u8::try_from(Signed9Bit::from(0_u8)), Ok(0_u8));
    assert_eq!(u8::try_from(Signed9Bit::from(1_u8)), Ok(1_u8));
    assert_eq!(u8::try_from(Signed9Bit::from(0o377_u8)), Ok(0o377_u8));
    assert_eq!(
        u8::try_from(Signed9Bit {
            bits: 0b011_111_111_u16
        }),
        Ok(0o377_u8)
    );
    assert_eq!(
        u8::try_from(Signed9Bit {
            bits: 0b111_111_110_u16
        }), // -1
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        u8::try_from(Signed9Bit {
            bits: 0b110_000_000_u16
        }), // -127
        Err(ConversionFailed::TooSmall)
    );
}

#[test]
fn test_i8_round_tripping() {
    let mut prev: Option<Signed9Bit> = None;
    for i in i8::MIN..i8::MAX {
        let q: Signed9Bit = Signed9Bit::from(i);
        if let Some(qprev) = prev {
            assert!(
                q > qprev,
                "failed to round-trip {i}: {q:?} should be greater than {qprev:?}",
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
    let mut prev: Option<Signed9Bit> = None;
    for i in u8::MIN..u8::MAX {
        let q: Signed9Bit = Signed9Bit::from(i);
        if let Some(qprev) = prev {
            assert!(
                q > qprev,
                "failed to round-trip {i}: {q:?} should be greater than {qprev:?}",
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
fn test_try_from_i8_signed9bit() {
    assert_octal_eq!(Signed9Bit::from(0_i8).bits, 0_u16);
    assert_octal_eq!(Signed9Bit::from(1_i8).bits, 1_u16);
    assert_octal_eq!(Signed9Bit::from(127_i8).bits, 127_u16);
    assert_octal_eq!(Signed9Bit::from(-1_i8).bits, 0b111_111_110_u16);
    assert_octal_eq!(Signed9Bit::from(-2_i8).bits, 0b111_111_101_u16);
    assert_octal_eq!(Signed9Bit::from(-8_i8).bits, 0b111_110_111_u16);
    assert_octal_eq!(Signed9Bit::from(-32_i8).bits, 0b111_011_111_u16);
    assert_octal_eq!(Signed9Bit::from(-64_i8).bits, 0b110_111_111_u16);
    assert_octal_eq!(Signed9Bit::from(-65_i8).bits, 0b110_111_110_u16);
    assert_octal_eq!(Signed9Bit::from(-66_i8).bits, 0b110_111_101_u16);
    assert_octal_eq!(Signed9Bit::from(-127_i8).bits, 0b110_000_000_u16);
    assert_octal_eq!(Signed9Bit::from(-128_i8).bits, 0b101_111_111_u16);
}

#[test]
fn test_signed9bit_zero_values() {
    const MINUS_ZERO: Signed9Bit = Signed9Bit {
        bits: 0b111_111_111_u16,
    };
    assert_eq!(
        i8::try_from(MINUS_ZERO),
        Ok(0_i8),
        "-0 should convert to 0_i8"
    );
    const PLUS_ZERO: Signed9Bit = Signed9Bit {
        bits: 0b000_000_000_u16,
    };
    assert_eq!(
        i8::try_from(PLUS_ZERO),
        Ok(0_i8),
        "+0 should convert to 0_i8"
    );
    // assert_eq!(PLUS_ZERO, MINUS_ZERO);   // need to implement PartialEq first.
}

#[test]
fn test_from_signed9bit_to_i8() {
    assert_eq!(i8::try_from(Signed9Bit { bits: 0 }), Ok(0_i8));
    assert_eq!(i8::try_from(Signed9Bit { bits: 1 }), Ok(1_i8));
    assert_eq!(i8::try_from(Signed9Bit { bits: 127_u16 }), Ok(127_i8));
    assert_eq!(
        i8::try_from(Signed9Bit {
            bits: 0b111_111_110_u16
        }),
        Ok(-1_i8)
    );
    assert_eq!(
        i8::try_from(Signed9Bit {
            bits: 0b111_111_101_u16
        }),
        Ok(-2_i8)
    );
    assert_eq!(
        i8::try_from(Signed9Bit {
            bits: 0b110_111_101_u16
        }),
        Ok(-66_i8)
    );
    assert_eq!(
        i8::try_from(Signed9Bit {
            bits: 0b110_000_000_u16
        }),
        Ok(-127_i8)
    );
    assert!(i8::try_from(Signed9Bit::MAX).is_err());
    assert!(i8::try_from(Signed9Bit::MIN).is_err());
}

#[test]
fn test_from_u16_to_signed9bit() {
    assert_octal_eq!(Signed9Bit::try_from(0_u16).unwrap().bits, 0_u16);
    assert_octal_eq!(Signed9Bit::try_from(1_u16).unwrap().bits, 1_u16);
    assert_octal_eq!(
        Signed9Bit::try_from(0o377_u16).unwrap().bits,
        0o000_000_377_u16
    );
    assert!(Signed9Bit::try_from(0o400_u16).is_err());
}

#[test]
fn test_from_signed9bit_to_u16() {
    assert_eq!(u16::try_from(Signed9Bit { bits: 0 }), Ok(0));
    assert_eq!(u16::try_from(Signed9Bit { bits: 1 }), Ok(1));
    assert_eq!(u16::try_from(Signed9Bit { bits: 0o377_u16 }), Ok(0o377_u16));
    assert_eq!(
        u16::try_from(Signed9Bit { bits: 0o400_u16 }),
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        u16::try_from(Signed9Bit { bits: 0o477_u16 }),
        Err(ConversionFailed::TooSmall)
    );
}

#[test]
fn test_signed9bit_ord() {
    let zero: Signed9Bit = Signed9Bit::from(0_i8);
    let one: Signed9Bit = Signed9Bit::from(1_i8);
    assert!(zero < one);
    assert!(one >= zero);
    assert!(zero >= zero);
    assert!(one >= one);

    assert!(one > zero);
    assert!(zero <= zero);
    assert!(one <= one);
    assert!(zero <= one);

    assert!(Signed9Bit::MIN < Signed9Bit::MAX);
    assert!(Signed9Bit::MAX > Signed9Bit::MIN);
}

#[test]
fn test_signed9bit_eq() {
    let zero: Signed9Bit = Signed9Bit::from(0_i8);
    let one: Signed9Bit = Signed9Bit::from(1_i8);
    assert_eq!(zero, zero);
    assert_eq!(one, one);

    let another_one: Signed9Bit = Signed9Bit::from(1_i8);
    assert_eq!(
        one, another_one,
        "ensure we don't confuse identy with equality"
    );
}

#[test]
fn test_signed9bit_checked_add() {
    let zero: Signed9Bit = Signed9Bit::from(0_i8);
    let one: Signed9Bit = Signed9Bit::from(1_i8);

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(zero.checked_add(zero), Some(zero));
    assert_eq!(zero.checked_add(one), Some(one));
    assert_eq!(one.checked_add(zero), Some(one));
    assert_eq!(Signed9Bit::MAX.checked_add(zero), Some(Signed9Bit::MAX));
    assert_eq!(Signed9Bit::MIN.checked_add(zero), Some(Signed9Bit::MIN));

    // Test the basics: 1+1=2
    let two: Signed9Bit = Signed9Bit::from(2_i8);
    assert_eq!(one.checked_add(one), Some(two));

    // Verify that we correctly detect overflow
    assert_eq!(Signed9Bit::MAX.checked_add(one), None);

    let minus_one: Signed9Bit = Signed9Bit::from(-1_i8);
    assert!(dbg!(minus_one) < zero);
    assert_eq!(
        i16::from(Signed9Bit::MAX.checked_add(minus_one).unwrap()),
        254_i16
    );
    assert_eq!(zero.checked_add(minus_one).unwrap(), minus_one);
}

#[test]
fn test_signed9bit_checked_sub() {
    let zero: Signed9Bit = Signed9Bit::from(0_i8);
    let one: Signed9Bit = Signed9Bit::from(1_i8);
    let minus_one: Signed9Bit = Signed9Bit::from(-1_i8);

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(zero.checked_sub(zero), Some(zero));
    assert_eq!(one.checked_sub(zero), Some(one));
    assert_eq!(Signed9Bit::MAX.checked_sub(zero), Some(Signed9Bit::MAX));
    assert_eq!(Signed9Bit::MIN.checked_sub(zero), Some(Signed9Bit::MIN));

    // Test the basics: 2-1=1
    let two: Signed9Bit = Signed9Bit::from(2_i8);
    assert_eq!(two.checked_sub(one), Some(one));
    assert_eq!(two.checked_sub(two), Some(zero));

    // Verify that we correctly detect overflow
    assert_eq!(Signed9Bit::MIN.checked_sub(one), None);

    assert_eq!(
        i16::from(Signed9Bit::MAX.checked_sub(one).unwrap()),
        254_i16
    );
    assert_eq!(zero.checked_sub(one).unwrap(), minus_one);
}

#[test]
fn test_signed9bit_abs() {
    let zero: Signed9Bit = Signed9Bit::from(0_i8);
    let one: Signed9Bit = Signed9Bit::from(1_i8);
    let minus_one: Signed9Bit = Signed9Bit::from(-1_i8);
    assert_eq!(zero, zero.abs());
    assert_eq!(one, one.abs());
    assert_eq!(one, minus_one.abs());
}

#[test]
fn test_signed9bit_checked_abs() {
    let zero: Signed9Bit = Signed9Bit::from(0_i8);
    let one: Signed9Bit = Signed9Bit::from(1_i8);
    let minus_one: Signed9Bit = Signed9Bit::from(-1_i8);
    assert_eq!((zero, false), zero.overflowing_abs());
    assert_eq!((one, false), one.overflowing_abs());
    assert_eq!((one, false), minus_one.overflowing_abs());
}

#[test]
fn test_wrapping_add() {
    for left in -255_i16..255_i16 {
        for right in -255_i16..255_i16 {
            let expected = left.wrapping_add(right);
            let expected = i16::from(Signed9Bit::try_from(expected % 256).unwrap());

            let left_operand = Signed9Bit::try_from(left).unwrap();
            let right_operand = Signed9Bit::try_from(right).unwrap();
            let got = i16::from(left_operand.wrapping_add(right_operand));

            assert_eq!(
                expected, got,
                "Expected {left} + {right} = {expected}, got {left_operand:?} + {right_operand:?} = {got}",
            );
        }
    }
}

#[test]
fn test_wrapping_sub() {
    for left in -255_i16..255_i16 {
        for right in -255_i16..255_i16 {
            let expected = left.wrapping_sub(right);
            let expected = i16::from(Signed9Bit::try_from(expected % 256).unwrap());

            let left_operand = Signed9Bit::try_from(left).unwrap();
            let right_operand = Signed9Bit::try_from(right).unwrap();
            let got = i16::from(left_operand.wrapping_sub(right_operand));

            assert_eq!(
                expected, got,
                "Expected {left} + {right} = {expected}, got {left_operand:?} + {right_operand:?} = {got}",
            );
        }
    }
}
