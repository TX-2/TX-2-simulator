use std::ops::Shl;

use super::onescomplement::unsigned::{Unsigned36Bit, Unsigned6Bit};
#[cfg(test)]
use super::u36;

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
    let src = u64::from(bits);
    let lowest_bits = Unsigned36Bit::from(0o010101010101_u32);
    let newbits: u64 = (src & 1)
        | ((src & 0o2) << 5)
        | ((src & 0o4) << 10)
        | ((src & 0o10) << 15)
        | ((src & 0o20) << 20)
        | ((src & 0o40) << 25);
    (target.shl(1) & !lowest_bits) | newbits
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

/// This function reverses the effect of perfoming six calls to
/// cycle_and_splay().
pub fn unsplay(source: Unsigned36Bit) -> [Unsigned6Bit; 6] {
    fn bits(
        b0: Unsigned36Bit,
        b1: Unsigned36Bit,
        b2: Unsigned36Bit,
        b3: Unsigned36Bit,
        b4: Unsigned36Bit,
        b5: Unsigned36Bit,
    ) -> Unsigned6Bit {
        let result: u8 = (if b0 == 0 { 0 } else { 0o01 })
            | (if b1 == 0 { 0 } else { 0o02 })
            | (if b2 == 0 { 0 } else { 0o04 })
            | (if b3 == 0 { 0 } else { 0o10 })
            | (if b4 == 0 { 0 } else { 0o20 })
            | (if b5 == 0 { 0 } else { 0o40 });
        Unsigned6Bit::try_from(result).unwrap()
    }

    let getbit = |n: u32| -> Unsigned36Bit { source & (1 << n) };
    [
        bits(
            getbit(5),
            getbit(11),
            getbit(17),
            getbit(23),
            getbit(29),
            getbit(35),
        ),
        bits(
            getbit(4),
            getbit(10),
            getbit(16),
            getbit(22),
            getbit(28),
            getbit(34),
        ),
        bits(
            getbit(3),
            getbit(9),
            getbit(15),
            getbit(21),
            getbit(27),
            getbit(33),
        ),
        bits(
            getbit(2),
            getbit(8),
            getbit(14),
            getbit(20),
            getbit(26),
            getbit(32),
        ),
        bits(
            getbit(1),
            getbit(7),
            getbit(13),
            getbit(19),
            getbit(25),
            getbit(31),
        ),
        bits(
            getbit(0),
            getbit(6),
            getbit(12),
            getbit(18),
            getbit(24),
            getbit(30),
        ),
    ]
}

#[test]
fn test_unsplay() {
    const ZERO: Unsigned6Bit = Unsigned6Bit::ZERO;
    const MAX: Unsigned6Bit = Unsigned6Bit::MAX;
    assert_eq!(
        unsplay(Unsigned36Bit::ZERO),
        [ZERO, ZERO, ZERO, ZERO, ZERO, ZERO]
    );
    assert_eq!(
        unsplay(u36!(0o777_777_777_777)),
        [MAX, MAX, MAX, MAX, MAX, MAX]
    );
}

#[cfg(test)]
fn round_trip(input: Unsigned36Bit) -> Result<(), String> {
    let unsplayed = unsplay(input);
    dbg!(&input);
    dbg!(&unsplayed);
    let mut output = Unsigned36Bit::ZERO;
    for (i, component) in unsplayed.into_iter().enumerate() {
        let next = cycle_and_splay(output, component);
        println!(
            "round_trip: splay iteration {i}: value {component:03o} changed word from {output:012o} to {next:012o}",
        );
        output = next;
    }
    dbg!(&output);
    if input == output {
        Ok(())
    } else {
        Err(format!("mismatch: input word {input:012o} unsplayed to {unsplayed:?}, which splayed to {output:012o}, which doesn't match",))
    }
}

#[test]
fn test_round_trip_selected() {
    for value in [
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ONE,
        Unsigned36Bit::from(0o2_u32),
        Unsigned36Bit::from(0o4_u32),
        Unsigned36Bit::from(0o3_u32),
        Unsigned36Bit::from(0o7_u32),
        Unsigned36Bit::from(0o77_u32),
        Unsigned36Bit::from(0o7700_u32),
        Unsigned36Bit::MAX,
        Unsigned36Bit::from(0o23574373_u32),
    ] {
        if let Err(e) = round_trip(value) {
            panic!("round_trip failed for {value:012o}: {e}");
        }
    }
}

#[test]
fn test_round_trip_bitcycle() {
    for bitpos in 0..36 {
        let input: Unsigned36Bit = Unsigned36Bit::ONE.shl(bitpos);
        if let Err(e) = round_trip(input) {
            panic!("round_trip failed for {input:012o}: {e}");
        }
    }
}
