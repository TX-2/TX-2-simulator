use std::ops::Shl;

use crate::onescomplement::unsigned::{Unsigned36Bit, Unsigned6Bit};

/// Loading a line of data from PETR in assembly mode has the effect
/// of first cycling the target word left by one bit position, and
/// then loading the incmoing bits into bit positions 0, 6, 12, 18,
/// 24, 30 (couting from the least significant bit).  If you repeat
/// that operation 6 times, you will load bits into all the positions
/// in a word.  This funciton performs this operation once (i.e. loads
/// 6 bits).
pub fn cycle_and_splay(target: Unsigned36Bit, bits: Unsigned6Bit) -> Unsigned36Bit {
    // The data goes into the following bit positions:
    // bit 1 (0 counting from 0) goes to 1.1 = 1 <<  0 (dec)
    // bit 2 (1 counting from 0) goes to 1.7 = 1 <<  6 (dec)
    // bit 3 (2 counting from 0) goes to 2.4 = 1 << 12 (dec)
    // bit 4 (3 counting from 0) goes to 3.1 = 1 << 18 (dec)
    // bit 5 (4 counting from 0) goes to 3.7 = 1 << 24 (dec)
    // bit 6 (5 counting from 0) goes to 4.4 = 1 << 30 (dec)
    let bits: Unsigned36Bit = bits.into();
    let mut updated = target.shl(1);
    for src_bit_pos in 0_u8..=5_u8 {
        let dest_bit_pos: Unsigned36Bit = (src_bit_pos * 6_u8).into();
        let srcmask: Unsigned36Bit = Unsigned36Bit::ONE.shl(Unsigned36Bit::from(src_bit_pos));
        let newbit: Unsigned36Bit = (bits & srcmask).shl(Unsigned36Bit::from(src_bit_pos * 5_u8));
        updated = updated & !(Unsigned36Bit::ONE.shl(dest_bit_pos)) | newbit;
    }
    updated
}

#[test]
fn test_cycle_and_splay() {
    assert_eq!(cycle_and_splay(Unsigned36Bit::ZERO, Unsigned6Bit::ZERO), 0);

    let ex: u64 = 1u64 << 0 | 1u64 << 6 | 1u64 << 12 | 1u64 << 18 | 1u64 << 24 | 1u64 << 30;
    let expected: Unsigned36Bit = Unsigned36Bit::try_from(ex).expect("test data should be valid");
    assert_eq!(
        cycle_and_splay(Unsigned36Bit::ZERO, Unsigned6Bit::MAX),
        expected
    );

    for bitpos in 0u8..=5u8 {
        let input_bit = Unsigned6Bit::try_from(1u8 << bitpos).expect("valid test data");
        let current: Unsigned36Bit = 2_u8.into();
        let expected_output = Unsigned36Bit::try_from(1u64 << (bitpos * 6))
            .expect("valid test data")
            | (current << Unsigned36Bit::ONE);
        assert_eq!(cycle_and_splay(current, input_bit), expected_output);
    }
}

/// This function reverses the effect of perfoming six calsl to
/// cycle_and_splay().
pub fn unsplay(source: Unsigned36Bit) -> [Unsigned6Bit; 6] {
    const ZERO: Unsigned6Bit = Unsigned6Bit::ZERO;
    let source = i64::from(source);
    let mut result: [Unsigned6Bit; 6] = [ZERO, ZERO, ZERO, ZERO, ZERO, ZERO];
    for (i, r) in result.iter_mut().enumerate() {
        let offset = (i + 1) % 6;
        let mut val = 0;
        for (destbit, srcbit) in (0..6).map(|destbit| (destbit, destbit * 6 + offset)) {
            if source & (1 << srcbit) != 0 {
                val |= 1 << destbit;
            }
        }
        *r = Unsigned6Bit::try_from(val).unwrap();
    }
    result
}

#[test]
fn test_unsplay() {
    const ZERO: Unsigned6Bit = Unsigned6Bit::ZERO;
    assert_eq!(
        unsplay(Unsigned36Bit::try_from(0o010101_010101_u64).expect("test data should be valid")),
        [ZERO, ZERO, ZERO, ZERO, ZERO, Unsigned6Bit::MAX]
    );
    assert_eq!(
        unsplay(Unsigned36Bit::try_from(0o020202_020202_u64).expect("test data should be valid")),
        [Unsigned6Bit::MAX, ZERO, ZERO, ZERO, ZERO, ZERO]
    );
    assert_eq!(
        unsplay(Unsigned36Bit::try_from(0o040404_040404_u64).expect("test data should be valid")),
        [ZERO, Unsigned6Bit::MAX, ZERO, ZERO, ZERO, ZERO]
    );
    assert_eq!(
        unsplay(Unsigned36Bit::try_from(1_u64 << 8).expect("test data should be valid")),
        [
            ZERO,
            Unsigned6Bit::try_from(2).expect("test data should be valid"),
            ZERO,
            ZERO,
            ZERO,
            ZERO
        ]
    );
}
