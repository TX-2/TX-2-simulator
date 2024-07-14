use super::Signed5Bit;

#[test]
fn test_from_u8() {
    assert_eq!(u8::try_from(Signed5Bit::try_from(1_u8).unwrap()), Ok(1_u8)); // 2^0
    assert_eq!(u8::try_from(Signed5Bit::try_from(2_u8).unwrap()), Ok(2_u8)); // 2^1
    assert_eq!(u8::try_from(Signed5Bit::try_from(4_u8).unwrap()), Ok(4_u8)); // 2^2
    assert_eq!(u8::try_from(Signed5Bit::try_from(8_u8).unwrap()), Ok(8_u8)); // 2^3
    assert!(dbg!(Signed5Bit::try_from(16_u8)).is_err());
}

#[test]
fn test_i8_round_tripping() {
    let mut prev: Option<Signed5Bit> = None;
    for i in -15_i8..15_i8 {
        let q: Signed5Bit = Signed5Bit::try_from(i).expect("input is in range");
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
        let out = i8::from(q);
        assert_eq!(i, out, "Round trip failed for {}->{:?}->{}", i, &q, out);
    }
}

#[test]
fn test_signed5bit_ord() {
    let zero: Signed5Bit = Signed5Bit::try_from(0_i8).unwrap();
    let one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();
    assert!(zero < one);
    assert!(one >= zero);
    assert!(zero >= zero);
    assert!(one >= one);

    assert!(one > zero);
    assert!(zero <= zero);
    assert!(one <= one);
    assert!(zero <= one);

    assert!(Signed5Bit::MIN < Signed5Bit::MAX);
    assert!(Signed5Bit::MAX > Signed5Bit::MIN);
}

#[test]
fn test_signed5bit_eq() {
    let zero: Signed5Bit = Signed5Bit::try_from(0_i8).unwrap();
    let one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();
    assert_eq!(zero, zero);
    assert_eq!(one, one);

    let another_one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();
    assert_eq!(
        one, another_one,
        "ensure we don't confuse identy with equality"
    );
}

#[test]
fn test_signed5bit_checked_add() {
    let zero: Signed5Bit = Signed5Bit::try_from(0_i8).unwrap();
    let one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(zero.checked_add(zero), Some(zero));
    assert_eq!(zero.checked_add(one), Some(one));
    assert_eq!(one.checked_add(zero), Some(one));
    assert_eq!(Signed5Bit::MAX.checked_add(zero), Some(Signed5Bit::MAX));
    assert_eq!(Signed5Bit::MIN.checked_add(zero), Some(Signed5Bit::MIN));

    // Test the basics: 1+1=2
    let two: Signed5Bit = Signed5Bit::try_from(2_i8).unwrap();
    assert_eq!(one.checked_add(one), Some(two));

    // Verify that we correctly detect overflow
    assert_eq!(Signed5Bit::MAX.checked_add(one), None);

    let minus_one: Signed5Bit = Signed5Bit::try_from(-1_i8).unwrap();
    assert!(dbg!(minus_one) < zero);

    // The max value is 15, so subtracting 1 from that shoudl give 14.
    let max: i8 = i8::from(Signed5Bit::MAX);
    assert_eq!(max, 15);
    assert_eq!(
        i8::from(Signed5Bit::MAX.checked_add(minus_one).unwrap()),
        14_i8
    );

    assert_eq!(zero.checked_add(minus_one).unwrap(), minus_one);
}

#[test]
fn test_signed5bit_checked_sub() {
    let zero: Signed5Bit = Signed5Bit::try_from(0_i8).unwrap();
    let one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();
    let minus_one: Signed5Bit = Signed5Bit::try_from(-1_i8).unwrap();

    // Test the basics: adding zero to something leaves it unchanged.
    assert_eq!(zero.checked_sub(zero), Some(zero));
    assert_eq!(one.checked_sub(zero), Some(one));
    assert_eq!(Signed5Bit::MAX.checked_sub(zero), Some(Signed5Bit::MAX));
    assert_eq!(Signed5Bit::MIN.checked_sub(zero), Some(Signed5Bit::MIN));

    // Test the basics: 2-1=1
    let two: Signed5Bit = Signed5Bit::try_from(2_i8).unwrap();
    assert_eq!(two.checked_sub(one), Some(one));
    assert_eq!(two.checked_sub(two), Some(zero));

    // Verify that we correctly detect overflow
    assert_eq!(Signed5Bit::MIN.checked_sub(one), None);

    assert_eq!(zero.checked_sub(one).unwrap(), minus_one);
}

#[test]
fn test_signed5bit_abs() {
    let zero: Signed5Bit = Signed5Bit::try_from(0_i8).unwrap();
    let one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();
    let minus_one: Signed5Bit = Signed5Bit::try_from(-1_i8).unwrap();
    assert_eq!(zero, zero.abs());
    assert_eq!(one, one.abs());
    assert_eq!(one, minus_one.abs());
}

#[test]
fn test_signed5bit_checked_abs() {
    let zero: Signed5Bit = Signed5Bit::try_from(0_i8).unwrap();
    let one: Signed5Bit = Signed5Bit::try_from(1_i8).unwrap();
    let minus_one: Signed5Bit = Signed5Bit::try_from(-1_i8).unwrap();
    assert_eq!((zero, false), zero.overflowing_abs());
    assert_eq!((one, false), one.overflowing_abs());
    assert_eq!((one, false), minus_one.overflowing_abs());
}
