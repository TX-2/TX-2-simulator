use super::{ConversionFailed, Signed18Bit};

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
fn test_signed18_max_value() {
    assert_eq!(u64::try_from(Signed18Bit::MAX), Ok(0o377_777_u64));
    assert_eq!(u32::try_from(Signed18Bit::MAX), Ok(0o377_777_u32));
    assert_eq!(i64::from(Signed18Bit::MAX), 0o377_777_i64);
    assert_eq!(i32::from(Signed18Bit::MAX), 0o377_777_i32);
}

#[test]
fn test_signed18_max_range() {
    assert!(u8::try_from(Signed18Bit::MAX).is_err());
    assert!(i8::try_from(Signed18Bit::MAX).is_err());
}

#[test]
fn test_signed18_min_value() {
    assert_eq!(i64::from(Signed18Bit::MIN), -0o377_777_i64);
    assert_eq!(i32::from(Signed18Bit::MIN), -0o377_777_i32);
}

#[test]
fn test_signed18_min_range() {
    assert!(u64::try_from(Signed18Bit::MIN).is_err());
    assert!(u32::try_from(Signed18Bit::MIN).is_err());
    assert!(u16::try_from(Signed18Bit::MIN).is_err());
    assert!(u8::try_from(Signed18Bit::MIN).is_err());
}

#[test]
fn test_from_u8() {
    assert_eq!(Signed18Bit::from(0_u8), Signed18Bit::ZERO);
    assert_eq!(Signed18Bit::from(1_u8), Signed18Bit::ONE);
    assert_eq!(Signed18Bit::from(0_u8).bits, 0_u32);
    assert_eq!(Signed18Bit::from(1_u8).bits, 1_u32);
    assert_eq!(Signed18Bit::from(0o377_u8).bits, 0o377_u32);
}

#[test]
fn test_try_from_signed18bit_u8() {
    assert_eq!(u8::try_from(Signed18Bit::ONE), Ok(1_u8));
    assert_eq!(u8::try_from(Signed18Bit::ZERO), Ok(0_u8));
    assert_eq!(u8::try_from(Signed18Bit::from(1_u8)), Ok(1_u8));
    assert_eq!(u8::try_from(Signed18Bit::from(0o377_u8)), Ok(0o377_u8));
    assert_eq!(
        u8::try_from(Signed18Bit {
            bits: 0b011_111_111_u32
        }),
        Ok(0o377_u8)
    );
    assert_eq!(
        u8::try_from(Signed18Bit {
            bits: 0o777_776_u32
        }), // -1
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        u8::try_from(Signed18Bit {
            bits: 0o777_677_u32
        }), // -127
        Err(ConversionFailed::TooSmall)
    );
}

#[test]
fn test_i8_round_tripping() {
    let mut prev: Option<Signed18Bit> = None;
    for i in i8::MIN..i8::MAX {
        let q: Signed18Bit = Signed18Bit::from(i);
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
fn test_i16_round_tripping() {
    let mut prev: Option<Signed18Bit> = None;
    for i in i16::MIN..i16::MAX {
        let q: Signed18Bit = Signed18Bit::from(i);
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
        match i16::try_from(q) {
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
    let mut prev: Option<Signed18Bit> = None;
    for i in u8::MIN..u8::MAX {
        let q: Signed18Bit = Signed18Bit::from(i);
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
fn test_u16_round_tripping() {
    let mut prev: Option<Signed18Bit> = None;
    for i in u16::MIN..u16::MAX {
        let q: Signed18Bit = Signed18Bit::from(i);
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
        match u16::try_from(q) {
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
fn test_convert_to_ones_complement() {
    assert_octal_eq!(Signed18Bit::convert_to_ones_complement(0_i32), 0_u32);
    assert_octal_eq!(Signed18Bit::convert_to_ones_complement(1_i32), 1_u32);
    assert_octal_eq!(
        Signed18Bit::convert_to_ones_complement(-1_i32),
        0o777_776_u32
    );
}

#[test]
fn test_from_i16_signed18bit() {
    assert_octal_eq!(Signed18Bit::ZERO.bits, 0_u32);
    assert_octal_eq!(Signed18Bit::ONE.bits, 1_u32);
    assert_octal_eq!(Signed18Bit::from(127_i16).bits, 127_u32);
    // octal because binary gets awkwardly long
    // Self::bits has 1 sign
    assert_octal_eq!(Signed18Bit::from(1_i16).bits, 0o000_001_u32); //  ( 2^0)
    assert_octal_eq!(Signed18Bit::from(2_i16).bits, 0o000_002_u32); //  ( 2^1)
    assert_octal_eq!(Signed18Bit::from(4_i16).bits, 0o000_004_u32); //  ( 2^2)
    assert_octal_eq!(Signed18Bit::from(8_i16).bits, 0o000_010_u32); //  ( 2^3)
    assert_octal_eq!(Signed18Bit::from(16_i16).bits, 0o000_020_u32); //  ( 2^4)
    assert_octal_eq!(Signed18Bit::from(32_i16).bits, 0o000_040_u32); //  ( 2^5)
    assert_octal_eq!(Signed18Bit::from(64_i16).bits, 0o000_100_u32); //  ( 2^6)
    assert_octal_eq!(Signed18Bit::from(128_i16).bits, 0o000_200_u32); //  ( 2^7)
    assert_octal_eq!(Signed18Bit::from(256_i16).bits, 0o000_400_u32); //  ( 2^8)
    assert_octal_eq!(Signed18Bit::from(512_i16).bits, 0o001_000_u32); //  ( 2^9)
    assert_octal_eq!(Signed18Bit::from(1024_i16).bits, 0o002_000_u32); //  (2^10)
    assert_octal_eq!(Signed18Bit::from(2048_i16).bits, 0o004_000_u32); //  (2^11)
    assert_octal_eq!(Signed18Bit::from(4096_i16).bits, 0o010_000_u32); //  (2^12)
    assert_octal_eq!(Signed18Bit::from(8192_i16).bits, 0o020_000_u32); //  (2^13)
    assert_octal_eq!(Signed18Bit::from(16384_i16).bits, 0o040_000_u32); //  (2^14)

    assert_octal_eq!(Signed18Bit::from(-1_i16).bits, 0o777_776_u32); // -( 2^0)
    assert_octal_eq!(Signed18Bit::from(-2_i16).bits, 0o777_775_u32); // -( 2^1)
    assert_octal_eq!(Signed18Bit::from(-4_i16).bits, 0o777_773_u32); // -( 2^2)
    assert_octal_eq!(Signed18Bit::from(-8_i16).bits, 0o777_767_u32); // -( 2^3)
    assert_octal_eq!(Signed18Bit::from(-16_i16).bits, 0o777_757_u32); // -( 2^4)
    assert_octal_eq!(Signed18Bit::from(-32_i16).bits, 0o777_737_u32); // -( 2^5)
    assert_octal_eq!(Signed18Bit::from(-64_i16).bits, 0o777_677_u32); // -( 2^6)
    assert_octal_eq!(Signed18Bit::from(-128_i16).bits, 0o777_577_u32); // -( 2^7)
    assert_octal_eq!(Signed18Bit::from(-256_i16).bits, 0o777_377_u32); // -( 2^8)
    assert_octal_eq!(Signed18Bit::from(-512_i16).bits, 0o776_777_u32); // -( 2^9)
    assert_octal_eq!(Signed18Bit::from(-1024_i16).bits, 0o775_777_u32); // -(2^10)
    assert_octal_eq!(Signed18Bit::from(-2048_i16).bits, 0o773_777_u32); // -(2^11)
    assert_octal_eq!(Signed18Bit::from(-4096_i16).bits, 0o767_777_u32); // -(2^12)
    assert_octal_eq!(Signed18Bit::from(-8192_i16).bits, 0o757_777_u32); // -(2^13)
    assert_octal_eq!(Signed18Bit::from(-16384_i16).bits, 0o737_777_u32); // -(2^14)
    assert_octal_eq!(Signed18Bit::from(-32768_i16).bits, 0o677_777_u32); // -(2^15)
}

#[test]
fn test_from_i32_signed18bit() {
    assert_octal_eq!(
        Signed18Bit::try_from(32768_i32).unwrap().bits,
        0o100_000_u32
    );
    assert_octal_eq!(
        Signed18Bit::try_from(65536_i32).unwrap().bits,
        0o200_000_u32
    );
}

#[test]
fn test_signed18bit_zero_values() {
    const MINUS_ZERO: Signed18Bit = Signed18Bit {
        bits: (1 << 18) - 1_u32,
    };
    assert_eq!(
        i8::try_from(MINUS_ZERO),
        Ok(0_i8),
        "-0 should convert to 0_i8"
    );
    const PLUS_ZERO: Signed18Bit = Signed18Bit {
        bits: 0b000_000_000_u32,
    };
    assert_eq!(
        i8::try_from(PLUS_ZERO),
        Ok(0_i8),
        "+0 should convert to 0_i8"
    );
    assert_eq!(PLUS_ZERO, MINUS_ZERO); // need to implement PartialEq first.
}

#[test]
fn test_from_signed18bit_to_i8() {
    assert_eq!(i8::try_from(Signed18Bit::ZERO), Ok(0_i8));
    assert_eq!(i8::try_from(Signed18Bit::ONE), Ok(1_i8));
    assert_eq!(i8::try_from(Signed18Bit { bits: 127_u32 }), Ok(127_i8));
    assert_eq!(
        i8::try_from(Signed18Bit {
            bits: 0o777_776_u32
        }),
        Ok(-1_i8)
    );
    assert_eq!(
        i8::try_from(Signed18Bit {
            bits: 0o777_775_u32
        }),
        Ok(-2_i8)
    );
    assert_eq!(
        i8::try_from(Signed18Bit {
            bits: 0o777_675_u32
        }),
        Ok(-66_i8)
    );
    assert_eq!(
        i8::try_from(Signed18Bit {
            bits: 0o777_600_u32
        }),
        Ok(-127_i8)
    );
    assert!(dbg!(i8::try_from(dbg!(Signed18Bit::MAX))).is_err());
    assert!(i8::try_from(Signed18Bit::MIN).is_err());
}

#[test]
fn test_from_signed18bit_to_i16() {
    assert_eq!(i16::try_from(Signed18Bit::ZERO), Ok(0_i16));
    assert_eq!(i16::try_from(Signed18Bit::ONE), Ok(1_i16));
    assert_eq!(i16::try_from(Signed18Bit { bits: 127_u32 }), Ok(127_i16));
    assert_eq!(
        i16::try_from(Signed18Bit { bits: 32767_u32 }),
        Ok(32767_i16)
    );
    assert!(i16::try_from(Signed18Bit::MAX).is_err());
    assert!(i16::try_from(Signed18Bit::MIN).is_err());
}

#[test]
fn test_from_u16_to_signed18bit() {
    assert_eq!(Signed18Bit::try_from(0_u16), Ok(Signed18Bit::ZERO));
    assert_eq!(Signed18Bit::try_from(1_u16), Ok(Signed18Bit::ONE));
    assert_eq!(Signed18Bit::from(0o377_u16).bits, 0o000_000_377_u32);
}

#[test]
fn test_from_signed18bit_to_u16() {
    assert_eq!(u16::try_from(Signed18Bit::ZERO), Ok(0));
    assert_eq!(u16::try_from(Signed18Bit::ONE), Ok(1));
    assert_eq!(
        u16::try_from(Signed18Bit { bits: 0o377_u32 }),
        Ok(0o377_u16)
    );
    assert_eq!(
        u16::try_from(Signed18Bit {
            bits: 0o400_000_u32
        }),
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        u16::try_from(Signed18Bit {
            bits: 0o477_000_u32
        }),
        Err(ConversionFailed::TooSmall)
    );
}

#[test]
fn test_signed18bit_ord() {
    assert!(Signed18Bit::ZERO < Signed18Bit::ONE);
    assert!(Signed18Bit::ONE >= Signed18Bit::ZERO);
    assert!(Signed18Bit::ZERO >= Signed18Bit::ZERO);
    assert!(Signed18Bit::ONE >= Signed18Bit::ONE);

    assert!(Signed18Bit::ONE > Signed18Bit::ZERO);
    assert!(Signed18Bit::ZERO <= Signed18Bit::ZERO);
    assert!(Signed18Bit::ONE <= Signed18Bit::ONE);
    assert!(Signed18Bit::ZERO <= Signed18Bit::ONE);

    assert!(Signed18Bit::MIN < Signed18Bit::MAX);
    assert!(Signed18Bit::MAX > Signed18Bit::MIN);
}

#[test]
fn test_signed18bit_eq() {
    assert_eq!(Signed18Bit::ZERO, Signed18Bit::ZERO);
    assert_eq!(Signed18Bit::ONE, Signed18Bit::ONE);

    let another_one: Signed18Bit = Signed18Bit::from(1_i8);
    assert_eq!(
        Signed18Bit::ONE,
        another_one,
        "ensure we don't confuse identity with equality"
    );
}

#[test]
fn test_signed18bit_checked_add() {
    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(
        Signed18Bit::ZERO.checked_add(Signed18Bit::ZERO),
        Some(Signed18Bit::ZERO)
    );
    assert_eq!(
        Signed18Bit::ZERO.checked_add(Signed18Bit::ONE),
        Some(Signed18Bit::ONE)
    );
    assert_eq!(
        Signed18Bit::ONE.checked_add(Signed18Bit::ZERO),
        Some(Signed18Bit::ONE)
    );
    assert_eq!(
        Signed18Bit::MAX.checked_add(Signed18Bit::ZERO),
        Some(Signed18Bit::MAX)
    );
    assert_eq!(
        Signed18Bit::MIN.checked_add(Signed18Bit::ZERO),
        Some(Signed18Bit::MIN)
    );

    // Test the basics: 1+1=2
    let two: Signed18Bit = Signed18Bit::from(2_i8);
    assert_eq!(Signed18Bit::ONE.checked_add(Signed18Bit::ONE), Some(two));

    // Verify that we correctly detect overflow
    assert_eq!(Signed18Bit::MAX.checked_add(Signed18Bit::ONE), None);

    let minus_one: Signed18Bit = Signed18Bit::from(-1_i8);
    assert!(dbg!(minus_one) < Signed18Bit::ZERO);
    assert_eq!(
        i32::from(Signed18Bit::MAX.checked_add(minus_one).unwrap()),
        0o377776_i32
    );
    assert_eq!(Signed18Bit::ZERO.checked_add(minus_one).unwrap(), minus_one);
}

#[test]
fn test_signed18bit_checked_sub() {
    let minus_one: Signed18Bit = Signed18Bit::from(-1_i8);

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(
        Signed18Bit::ZERO.checked_sub(Signed18Bit::ZERO),
        Some(Signed18Bit::ZERO)
    );
    assert_eq!(
        Signed18Bit::ONE.checked_sub(Signed18Bit::ZERO),
        Some(Signed18Bit::ONE)
    );
    assert_eq!(
        Signed18Bit::MAX.checked_sub(Signed18Bit::ZERO),
        Some(Signed18Bit::MAX)
    );
    assert_eq!(
        Signed18Bit::MIN.checked_sub(Signed18Bit::ZERO),
        Some(Signed18Bit::MIN)
    );

    // Test the basics: 2-1=1
    let two: Signed18Bit = Signed18Bit::from(2_i8);
    assert_eq!(two.checked_sub(Signed18Bit::ONE), Some(Signed18Bit::ONE));
    assert_eq!(two.checked_sub(two), Some(Signed18Bit::ZERO));

    // Verify that we correctly detect overflow
    assert_eq!(Signed18Bit::MIN.checked_sub(Signed18Bit::ONE), None);

    assert_eq!(
        i32::from(Signed18Bit::MAX.checked_sub(Signed18Bit::ONE).unwrap()),
        0o377776_i32
    );
    assert_eq!(
        Signed18Bit::ZERO.checked_sub(Signed18Bit::ONE).unwrap(),
        minus_one
    );
}

#[test]
fn test_signed18bit_abs() {
    let minus_one: Signed18Bit = Signed18Bit::from(-1_i8);
    assert_eq!(Signed18Bit::ZERO, Signed18Bit::ZERO.abs());
    assert_eq!(Signed18Bit::ONE, Signed18Bit::ONE.abs());
    assert_eq!(Signed18Bit::ONE, minus_one.abs());
}

#[test]
fn test_signed18bit_checked_abs() {
    let minus_one: Signed18Bit = Signed18Bit::from(-1_i8);
    assert_eq!(
        (Signed18Bit::ZERO, false),
        Signed18Bit::ZERO.overflowing_abs()
    );
    assert_eq!(
        (Signed18Bit::ONE, false),
        Signed18Bit::ONE.overflowing_abs()
    );
    assert_eq!((Signed18Bit::ONE, false), minus_one.overflowing_abs());
}
