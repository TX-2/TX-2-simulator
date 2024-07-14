use super::{ConversionFailed, Signed36Bit};

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
fn test_signed36_max_value() {
    assert_eq!(u64::try_from(Signed36Bit::MAX), Ok(0o377_777_777_777_u64));
    assert_eq!(i64::from(Signed36Bit::MAX), 0o377_777_777_777_i64);
}

#[test]
fn test_signed36_min_value() {
    assert_eq!(i64::from(Signed36Bit::MIN), -0o377_777_777_777_i64);
}

#[test]
fn test_signed36_min_range() {
    dbg!(&Signed36Bit::MIN);
    assert!(dbg!(u64::try_from(Signed36Bit::MIN)).is_err());
    assert!(dbg!(u32::try_from(Signed36Bit::MIN)).is_err());
    assert!(dbg!(u16::try_from(Signed36Bit::MIN)).is_err());
    assert!(dbg!(u8::try_from(Signed36Bit::MIN)).is_err());
}

#[test]
fn test_from_u8() {
    assert_eq!(Signed36Bit::from(0_u8).bits, 0_u64);
    assert_eq!(Signed36Bit::from(1_u8).bits, 1_u64);
    assert_eq!(Signed36Bit::from(0o377_u8).bits, 0o377_u64);
}

#[test]
fn test_try_from_signed36bit_u8() {
    assert_eq!(u8::try_from(Signed36Bit::from(0_u8)), Ok(0_u8));
    assert_eq!(u8::try_from(Signed36Bit::from(1_u8)), Ok(1_u8));
    assert_eq!(u8::try_from(Signed36Bit::from(0o377_u8)), Ok(0o377_u8));
    assert_eq!(u8::try_from(Signed36Bit::from(0o377_u32)), Ok(0o377_u8));
    assert_eq!(
        u8::try_from(Signed36Bit::from(-1_i8)),
        Err(ConversionFailed::TooSmall)
    );
    assert_eq!(
        u8::try_from(Signed36Bit::from(-127_i8)),
        Err(ConversionFailed::TooSmall)
    );
}

#[test]
fn test_i16_round_tripping() {
    let mut prev: Option<Signed36Bit> = None;
    for i in i16::MIN..i16::MAX {
        let q: Signed36Bit = Signed36Bit::from(i);
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
fn test_convert_to_ones_complement() {
    assert_octal_eq!(
        Signed36Bit::convert_to_ones_complement(-1_i64),
        0o777_777_777_776_u64
    );
}

#[test]
fn test_i32_round_tripping() {
    fn round_trip(input: i32) {
        let x = Signed36Bit::from(input);
        let result: i32 = x.try_into().expect("round-trip should work");
        assert_octal_eq!(input, result);
    }

    for bitpos in 0..32 {
        let input: i32 = 1_i32 << bitpos;
        let (negated, overflow) = input.overflowing_neg();
        round_trip(input);
        if !overflow {
            round_trip(negated);
        }
    }
}

#[test]
fn test_i64_round_tripping() {
    fn round_trip(input: i64) {
        match Signed36Bit::try_from(input) {
            Err(_) if input >= 0 => {
                assert!(input >= 1_i64 << 35);
            }
            Err(_) => {
                assert!(input <= -(1_i64 << 35));
            }
            Ok(x) => {
                let result: i64 = x.into();
                assert_octal_eq!(input, result);
            }
        }
    }

    for bitpos in 0..63 {
        let input: i64 = 1_i64 << bitpos;
        round_trip(input);
        round_trip(-input);
    }
}

#[test]
fn test_signed36_division() {
    let minus_two = Signed36Bit::from(-2_i8);
    let minus_one = Signed36Bit::from(-1_i8);
    let one = Signed36Bit::from(1_i8);
    let two = Signed36Bit::from(2_i8);
    let three = Signed36Bit::from(3_i8);
    let six = Signed36Bit::from(6_i8);

    assert_eq!(one.checked_div(one), Some(one));
    assert_eq!(six.checked_div(one), Some(six));
    assert_eq!(six.checked_div(three), Some(two));
    assert_eq!(three.checked_div(two), Some(one));
    assert_eq!(six.checked_div(Signed36Bit::ZERO), None);

    assert_eq!(minus_one.checked_div(minus_one), Some(one));
    assert_eq!(two.checked_div(minus_one), Some(minus_two));
    assert_eq!(three.checked_div(minus_two), Some(minus_one));
}

#[test]
fn test_signed36_is_zero() {
    assert!(Signed36Bit::ZERO.is_zero());
    assert!(Signed36Bit::ZERO.is_positive_zero());
    assert!(!Signed36Bit::ZERO.is_negative_zero());

    assert!(Signed36Bit::MINUS_ZERO.is_zero());
    assert!(Signed36Bit::MINUS_ZERO.is_negative_zero());
    assert!(!Signed36Bit::MINUS_ZERO.is_positive_zero());

    assert_eq!(Signed36Bit::ZERO, Signed36Bit::ZERO);
    assert_eq!(Signed36Bit::MINUS_ZERO, Signed36Bit::MINUS_ZERO);
    assert_eq!(Signed36Bit::MINUS_ZERO, Signed36Bit::ZERO);
}
