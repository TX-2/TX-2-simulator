//! The Exchange Element governs data exchange between memory (via the
//! M register) and other parts of the central compute unit (including
//! the arithmetic element) via the E register.
//!
//! The way in which the exchange element behaves is governed by the
//! "System Configuration" which is a 9-bit value loaded from the
//! F-memory.  Which specific value is loaded from the F-memory is
//! determined by the 5-bit configuration field within the current
//! instruction; the instruction is loaded into the N register).
//!
//! The standard set-up of the F-memory is described in Table 7-2 of
//! the User Guide.
use std::fmt::{self, Display, Formatter, Octal};

use tracing::{event, Level};

use base::prelude::*;

// QuarterActivity has a 1 where a quarter is active (unlike the sense
// in the configuration values, which are 0 for active).  Quarters in
// QuarterActivity are numbered from 0.
#[derive(Clone, Copy, Debug)]
pub struct QuarterActivity(u8);

impl QuarterActivity {
    pub fn new(bits: u8) -> QuarterActivity {
        assert_eq!(bits & !0b1111, 0);
        QuarterActivity(bits)
    }

    pub fn is_active(&self, q: &u8) -> bool {
        assert!(*q < 4, "invalid quarter {}", q);
        let mask = 1 << *q;
        self.0 & mask != 0
    }

    pub fn first_active_quarter(&self) -> u8 {
        self.0.trailing_zeros() as u8
    }

    pub fn masked_by(&self, mask: u8) -> QuarterActivity {
        QuarterActivity::new(self.0 & mask)
    }

    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Permutation {
    P0 = 0,
    P1,
    P2,
    P3,
    P4,
    P5,
    P6,
    P7,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubwordForm {
    FullWord = 0, // 36
    Halves = 1,   // 18, 18
    ThreeOne = 2, // 27, 9
    Quarters = 3, //
}

/// The SystemConfiguration value specifies a global state of the
/// computer which determines how the AE (in modern wording,
/// arithmetic unit) communicates with memory.  The basic outline is
/// given in Fig. 9 (page 20) of "A Functional Description of the
/// Lincoln TX-2 Computer" by John M. Frankovitch and H. Philip
/// Peterson.  A more complete description (inclusing the
/// corresponding F-memory values) is given in tables 7-2 and 7-2A of
/// the TX-2 User's Handbook (pp 192-193 in my PDF copy).
///
/// The system configuration is a 9-bit value.  While Frankovitch and
/// Peterson describe most significant bit as being spare, table 7-2
/// appears to use it.
///
/// Figure 12-39 ("Configuration Block Diagram") (page 250) in Volume
/// 2 of the TX-2 Technical manual describes how a word from the CF
/// memory (a QKIRcf value) is decoded into permutation, activity
/// (which quarters are active) and fracture (which quarters are
/// considered to be separate).
#[derive(Clone, Copy, Debug)]
pub struct SystemConfiguration(Unsigned9Bit);

impl From<u8> for SystemConfiguration {
    fn from(n: u8) -> SystemConfiguration {
        SystemConfiguration(Unsigned9Bit::from(n))
    }
}

impl From<Unsigned9Bit> for SystemConfiguration {
    fn from(n: Unsigned9Bit) -> SystemConfiguration {
        SystemConfiguration(n)
    }
}

impl PartialEq for SystemConfiguration {
    fn eq(&self, other: &SystemConfiguration) -> bool {
        self.0.eq(&other.0)
    }
}

impl Display for SystemConfiguration {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        Octal::fmt(&self.0, f)
    }
}

impl Octal for SystemConfiguration {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        Octal::fmt(&self.0, f)
    }
}

impl SystemConfiguration {
    pub fn zero() -> SystemConfiguration {
        SystemConfiguration(Unsigned9Bit::ZERO)
    }

    fn permutation(&self) -> Permutation {
        match u16::from(self.0) & 0b111 {
            0 => Permutation::P0,
            1 => Permutation::P1,
            2 => Permutation::P2,
            3 => Permutation::P3,
            4 => Permutation::P4,
            5 => Permutation::P5,
            6 => Permutation::P6,
            7 => Permutation::P7,
            _ => unreachable!(),
        }
    }

    /// Extract a QuarterActivity value from the activity field of a system
    /// configuration value.
    ///
    /// Active quarters are signaled by a 0 in the appropriate bit
    /// position of the system configuration value.  A 1 signals that
    /// the corresponding quarter is inactive.
    ///
    /// The mapping between configuration values and which quarter is
    /// active is given in Table 12-4 in the technical manual (volume
    /// 2, page 12-22).
    ///
    fn active_quarters(&self) -> QuarterActivity {
        // CF7 CF6 CF5 CF4
        //   x   x   x   0 => ACT 1
        //   x   x   0   x => ACT 2
        //   x   0   x   x => ACT3
        //   0   x   x   x => ACT4
        //
        // These bit values are not mutually exclusive, so for example
        // 0010 means that quarters 4, 3 and 1 are active.
        let act_field: u16 = (!(u16::from(self.0) >> 3)) & 0b1111;
        let result = QuarterActivity::new(act_field as u8);
        event!(
            Level::TRACE,
            "active_quarters: system configuration {:>03o} -> result {:?}",
            self,
            result
        );
        result
    }

    fn subword_form(&self) -> SubwordForm {
        const MASK: u16 = 0o3 << 7;
        match u16::from(self.0) & MASK {
            0b000000000 => SubwordForm::FullWord, // 36
            0b010000000 => SubwordForm::Halves,   // 18,18
            0b100000000 => SubwordForm::ThreeOne, // 27,9
            0b110000000 => SubwordForm::Quarters, // 9,9,9,9
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
macro_rules! assert_octal_eq {
    ($left:expr, $right:expr $(,)?) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    panic!(
                        "Assertion failed: {:#>012o} != {:>#012o}",
                        left_val, right_val
                    );
                }
            }
        }
    }};
}

/// Compute the quarter number (starting at 0) of the source word from
/// which the values for `target_quarter` (also starting at 0) would
/// be taken if it were active.
///
/// Permutation behaviour is described in section 12-6.4 of Volume 2
/// of the Technical Manual.
fn permutation_source(permutation: &Permutation, target_quarter: u8) -> u8 {
    match permutation {
        Permutation::P0 => target_quarter % 4,
        Permutation::P1 => (target_quarter + 1) % 4,
        Permutation::P2 => (target_quarter + 2) % 4,
        Permutation::P3 => (target_quarter + 3) % 4,
        Permutation::P4 => target_quarter ^ 0b01,
        Permutation::P5 => target_quarter ^ 0b11,
        Permutation::P6 => match target_quarter {
            3 => 2,
            2 => 1,
            1 => 3,
            0 => 0,
            _ => unreachable!(),
        },
        Permutation::P7 => match target_quarter {
            3 => 1,
            2 => 3,
            1 => 2,
            0 => 0,
            _ => unreachable!(),
        },
    }
}

// TODO: add a unit test for sign extension in partially-active
// subwords, based on the example in Figures 12-41, 12-42 (technical
// manual, volume 2).

fn quarter_mask(n: u8) -> u64 {
    assert!(n < 4);
    0o777 << (n * 9)
}

fn apply_sign(word: u64, quarter_number_from: u8, quarter_number_to: u8) -> u64 {
    let signbit = word & (0o300 << (quarter_number_from * 9));
    let mask = quarter_mask(quarter_number_to);
    if signbit == 0 {
        word & !mask
    } else {
        word | mask
    }
}

fn sign_extend_quarters(
    w: &Unsigned36Bit,
    active_quarters: QuarterActivity,
    quarters: &[u8],
) -> Unsigned36Bit {
    let mut word: Unsigned36Bit = *w;
    if !active_quarters.is_empty() {
        let first_active = active_quarters.first_active_quarter();
        assert!(first_active < 4);
        let mut last_active = first_active;
        for q in quarters {
            if active_quarters.is_active(q) {
                last_active = *q;
            } else {
                let mut w64 = u64::from(word); // TODO: eliminate conversion
                w64 = apply_sign(w64, last_active, *q);
                word = Unsigned36Bit::try_from(w64).unwrap(); // TODO: eliminate conversion
            }
        }
    }
    word
}

pub fn sign_extend(
    form: &SubwordForm,
    mut word: Unsigned36Bit,
    active: QuarterActivity,
) -> Unsigned36Bit {
    match form {
        SubwordForm::FullWord => {
            let first = active.first_active_quarter();
            let quarters = &[first, (first + 1) % 4, (first + 2) % 4, (first + 3) % 4];
            sign_extend_quarters(&word, active, quarters)
        }
        SubwordForm::ThreeOne => {
            fn next(q: u8) -> u8 {
                match q {
                    1 | 2 => q + 1,
                    3 => 1,
                    _ => unreachable!(),
                }
            }
            if active.is_empty() {
                word
            } else {
                let first = active.first_active_quarter();
                let quarters = &[first, next(first), next(next(first))];
                sign_extend_quarters(&word, active.masked_by(0b1110), quarters)
            }
        }
        SubwordForm::Halves => {
            let a = active.masked_by(0b0011);
            if !a.is_empty() {
                fn next_right(q: u8) -> u8 {
                    match q {
                        0 => 1,
                        1 => 0,
                        _ => unreachable!(),
                    }
                }
                let first = a.first_active_quarter();
                word = sign_extend_quarters(&word, a, &[first, next_right(first)]);
            }
            let a = active.masked_by(0b1100);
            if !a.is_empty() {
                fn next_left(q: u8) -> u8 {
                    match q {
                        3 => 2,
                        2 => 3,
                        _ => unreachable!(),
                    }
                }
                let first = a.first_active_quarter();
                word = sign_extend_quarters(
                    &word,
                    active.masked_by(0b1100),
                    &[first, next_left(first)],
                );
            }
            word
        }
        SubwordForm::Quarters => word,
    }
}

#[test]
fn test_sign_extend_full_word() {
    use SubwordForm::*;

    fn word(val: u64) -> Unsigned36Bit {
        Unsigned36Bit::try_from(val).expect("valid test data")
    }

    // When all quarters are active, sign extension should make no difference.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            Unsigned36Bit::from(0_u8),
            QuarterActivity::new(0b1111)
        ),
        word(0)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o300_000_000_000_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o300_000_000_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o000_300_000_000_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o000_300_000_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o000_000_300_000_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o000_000_300_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o000_000_000_300_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o000_000_000_300_u64)
    );

    // If no quarters are active, there is nothing to sign-extend from, so sign extension is a no-op.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o444333222111_u64),
            QuarterActivity::new(0b0000)
        ),
        word(0o444333222111_u64)
    );

    // Sign-extending a positive quantity into a quarter should zero it.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_003_002_001_u64),
            QuarterActivity::new(0b0111)
        ),
        word(0o000_003_002_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_727_002_001_u64),
            QuarterActivity::new(0b1011)
        ),
        word(0o004_000_002_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_003_727_001_u64),
            QuarterActivity::new(0b1101)
        ),
        word(0o004_003_000_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_003_002_727_u64),
            QuarterActivity::new(0b1110)
        ),
        word(0o004_003_002_000_u64)
    );

    // Sign-extending a negative quantity into a quarter should fill it with ones.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o272_303_002_001_u64),
            QuarterActivity::new(0b0111)
        ),
        word(0o777_303_002_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_272_302_001_u64),
            QuarterActivity::new(0b1011)
        ),
        word(0o004_777_302_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_003_272_301_u64),
            QuarterActivity::new(0b1101)
        ),
        word(0o004_003_777_301_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o304_003_002_272_u64),
            QuarterActivity::new(0b1110)
        ),
        word(0o304_003_002_777_u64)
    );

    // We should be able to sign-extend over two consecutive quarters.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_003_002_727_u64),
            QuarterActivity::new(0b0110)
        ),
        word(0o000_003_002_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_727_002_001_u64),
            QuarterActivity::new(0b0011)
        ),
        word(0o000_000_002_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_727_727_001_u64),
            QuarterActivity::new(0b1001)
        ),
        word(0o004_000_000_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_003_727_727_u64),
            QuarterActivity::new(0b1100)
        ),
        word(0o004_003_000_000_u64)
    );

    // We should be able to sign-extend a positive value over three consecutive quarters.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_727_727_001_u64),
            QuarterActivity::new(0b0001)
        ),
        word(0o000_000_000_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_727_002_727_u64),
            QuarterActivity::new(0b0010)
        ),
        word(0o000_000_002_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_003_727_727_u64),
            QuarterActivity::new(0b0100)
        ),
        word(0o000_003_000_000_u64),
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o004_727_727_727_u64),
            QuarterActivity::new(0b1000)
        ),
        word(0o004_000_000_000_u64)
    );

    // We should be able to sign-extend a negative value over three consecutive quarters.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_727_727_301_u64),
            QuarterActivity::new(0b0001)
        ),
        word(0o777_777_777_301_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_727_302_727_u64),
            QuarterActivity::new(0b0010)
        ),
        word(0o777_777_302_777_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o727_303_727_727_u64),
            QuarterActivity::new(0b0100)
        ),
        word(0o777_303_777_777_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            word(0o304_727_727_727_u64),
            QuarterActivity::new(0b1000)
        ),
        word(0o304_777_777_777_u64),
    );
}

#[test]
fn test_sign_extend_halves() {
    use SubwordForm::*;
    fn word(val: u64) -> Unsigned36Bit {
        Unsigned36Bit::try_from(val).expect("valid test data")
    }

    // When all quarters are active, sign extension should make no difference.
    assert_octal_eq!(
        sign_extend(&Halves, word(0), QuarterActivity::new(0b1111)),
        word(0)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o300_000_000_000_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o300_000_000_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o000_300_000_000),
            QuarterActivity::new(0b1111)
        ),
        word(0o000_300_000_000),
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o000_000_300_000_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o000_000_300_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o000_000_000_300_u64),
            QuarterActivity::new(0b1111)
        ),
        word(0o000_000_000_300_u64)
    );

    // If no quarters are active, there is nothing to sign-extend from, so sign extension is a no-op.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o444333222111_u64),
            QuarterActivity::new(0b0000)
        ),
        word(0o444333222111_u64)
    );

    // Sign-extending a positive quantity into a quarter should zero it.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b0101)
        ),
        word(0o000_003_000_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b0001)
        ),
        word(0o004_003_000_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b1010)
        ),
        word(0o004_000_002_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b0110)
        ),
        word(0o000_003_002_000_u64)
    );

    // Sign-extending a negative quantity into a quarter should fill it with ones.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_303_302_001_u64),
            QuarterActivity::new(0b0110)
        ),
        word(0o777_303_302_777_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o304_003_302_001_u64),
            QuarterActivity::new(0b1010)
        ),
        word(0o304_777_302_777_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_303_002_301_u64),
            QuarterActivity::new(0b0101)
        ),
        word(0o777_303_777_301_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_301_u64),
            QuarterActivity::new(0b0001)
        ),
        word(0o004_003_777_301_u64)
    );

    // We should not be able to sign-extend over two consecutive
    // quarters (because the halves are only two quarters long).
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b0001)
        ),
        word(0o004_003_000_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b0010)
        ),
        word(0o004_003_002_000_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b0100)
        ),
        word(0o000_003_002_001_u64)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            word(0o004_003_002_001_u64),
            QuarterActivity::new(0b1000)
        ),
        word(0o004_000_002_001_u64)
    );
}

// TODO: add tests for (27,9) and maybe (9,9,9,9).

/// Determine which quarter of `source` gets permuted into
/// `target_quarter` (numbered from zero), without regard to activity.
/// Return the value of that quarter, shifted down into the lowest
/// quarter.
fn fetch_permuted_quarter(permutation: &Permutation, target_quarter: u8, source: &u64) -> u64 {
    let source_quarter = permutation_source(permutation, target_quarter);
    (source & quarter_mask(source_quarter)) >> (source_quarter * 9)
}

#[test]
fn test_fetch_permuted_quarter() {
    assert_octal_eq!(
        fetch_permuted_quarter(&Permutation::P0, 2, &0o444333222111),
        0o333
    );
}

/// Copy bits from `source` to `dest`, permuting them according to
/// `permutation`.  Only active quarters are modified.
fn permute(
    permutation: &Permutation,
    active_quarters: &QuarterActivity,
    source: &Unsigned36Bit,
    dest: &Unsigned36Bit,
) -> Unsigned36Bit {
    let mut result: u64 = (*dest).into();
    let source_bits: u64 = u64::from(*source);
    for target_quarter in 0_u8..4_u8 {
        if active_quarters.is_active(&target_quarter) {
            // `value` will be the value from the quarter we want,
            // shifted to the correct position.
            let value = fetch_permuted_quarter(permutation, target_quarter, &source_bits)
                << (target_quarter * 9);
            let target_mask: u64 = quarter_mask(target_quarter);
            result &= !target_mask;
            result |= target_mask & value;
        }
    }
    Unsigned36Bit::try_from(result).unwrap()
}

#[test]
fn test_permute() {
    fn word(val: u64) -> Unsigned36Bit {
        Unsigned36Bit::try_from(val).expect("valid test data")
    }

    assert_octal_eq!(
        permute(
            &Permutation::P0,
            &QuarterActivity::new(0b1111),
            &word(0o444333222111_u64),
            &word(0o777666555444_u64),
        ),
        word(0o444333222111_u64),
    );
    assert_octal_eq!(
        permute(
            &Permutation::P0,
            &QuarterActivity::new(0b1110),
            &word(0o444333222111_u64),
            &word(0o777666555444_u64),
        ),
        word(0o444333222444_u64),
    );
}

/// Perform an exchange operation; that is, emulate the operation of
/// the exchange unit. The operation of this unit is described in
/// section 12 (volume 2) of the Technical Manual.
pub fn exchanged_value(
    cfg: &SystemConfiguration,
    source: &Unsigned36Bit,
    dest: &Unsigned36Bit,
) -> Unsigned36Bit {
    let active_quarters = cfg.active_quarters();
    let permutation = cfg.permutation();
    let permuted_target = permute(&permutation, &active_quarters, source, dest);
    sign_extend(&cfg.subword_form(), permuted_target, active_quarters)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::get_standard_plugboard;

    fn standard_plugboard_f_memory_settings() -> Vec<u16> {
        let mut result = Vec::with_capacity(0o040);
        let plugboard = get_standard_plugboard();
        dbg!(&plugboard);
        for (i, spg_word) in plugboard.iter().enumerate() {
            for quarter in 0..4 {
                let index = (i * 4) + quarter;
                let value: u64 = u64::from(*spg_word) >> (quarter * 9);
                let value: u16 = (value & 0o777) as u16;
                event!(
                    Level::TRACE,
                    "F-memory index {:>03o} = {:>03o}",
                    index,
                    value
                );
                result.push(value);
            }
        }
        result
    }

    #[test]
    fn test_system_configuration_standard_config() {
        /// The standard configuration set of F-memory, taken from table 7-2
        /// (marked "OLD") of the TX-2 User's Guide (October 1961).
        const STANDARD_CONFIG: [u16; 32] = [
            0o000, 0o340, 0o342, 0o760, 0o761, 0o762, 0o763, 0o410, 0o411, 0o140, 0o142, 0o160,
            0o161, 0o162, 0o163, 0o202, 0o200, 0o230, 0o232, 0o732, 0o733, 0o730, 0o731, 0o605,
            0o600, 0o750, 0o670, 0o320, 0o333, 0o330, 0o331, 0o604,
        ];

        #[derive(Debug)]
        struct Expectation {
            config: Unsigned9Bit,
            perm: Permutation,
            form: SubwordForm,
            active: u8,
        }
        fn configval(n: u16) -> Unsigned9Bit {
            Unsigned9Bit::try_from(n).expect("valid test data")
        }
        use Permutation::*;
        use SubwordForm::*;
        let cases: [Expectation; 32] = [
            // should be size 32 when we're ready
            // Indexes 000 to 003
            Expectation {
                config: configval(0),
                // (4,3,2,1) -> (4,3,2,1)
                perm: P0,
                form: FullWord,
                active: 0b1111,
            },
            Expectation {
                config: configval(0o340),
                // (2,1)->(2,1) i.e. R->R
                perm: P0,
                form: Halves,
                active: 0b0011,
            },
            Expectation {
                config: configval(0o342),
                // (4,3) -> (2, 1), i.e. L->R
                perm: P2,
                form: Halves,
                active: 0b0011,
            },
            Expectation {
                config: configval(0o760),
                // (1) -> (1)
                perm: P0,
                form: Quarters,
                active: 0b0001,
            },
            // Indexes 004 to 007
            Expectation {
                config: configval(0o761),
                // (2) -> (1)
                perm: P1,
                form: Quarters,
                active: 0b0001,
            },
            Expectation {
                config: configval(0o762),
                // (3) -> (1)
                perm: P2,
                form: Quarters,
                active: 0b0001,
            },
            Expectation {
                config: configval(0o763),
                // (4) -> (1)
                perm: P3,
                form: Quarters,
                active: 0b0001,
            },
            Expectation {
                config: configval(0o410),
                // (4,3,2) -> (4,3,2)
                perm: P0,
                form: ThreeOne,
                active: 0b1110,
            },
            // Indexes 010 to 013
            Expectation {
                config: configval(0o411),
                // (1,4,3) -> (4,3,2)
                perm: P1,
                form: ThreeOne,
                active: 0b1110,
            },
            Expectation {
                config: configval(0o140),
                // (2,1) -> (2,1), i.e. R->R and sign extend into L
                perm: P0,
                form: FullWord,
                active: 0b0011,
            },
            Expectation {
                config: configval(0o142),
                // (4,3) -> (2,1), i.e. L->R and sign extend into L
                perm: P2,
                form: FullWord,
                active: 0b0011,
            },
            Expectation {
                config: configval(0o160),
                // (1) -> (1) and sign extend into full word
                perm: P0,
                form: FullWord,
                active: 0b0001,
            },
            // Indexes 014 to 017
            Expectation {
                config: configval(0o161),
                // (2) -> (1) and sign extend into full word
                perm: P1,
                form: FullWord,
                active: 0b0001,
            },
            Expectation {
                config: configval(0o162),
                // (3) -> (1) and sign extend into full word
                perm: P2,
                form: FullWord,
                active: 0b0001,
            },
            Expectation {
                config: configval(0o163),
                // (4) -> (1) and sign extend into full word
                perm: P3,
                form: FullWord,
                active: 0b0001,
            },
            Expectation {
                config: configval(0o202),
                //  (4,3),(2,1) -> (2,1),(4,3), i.e. L,R -> R,L
                perm: P2,
                form: Halves,
                active: 0b1111,
            },
            // Indexes 020 to 023
            Expectation {
                config: configval(0o200),
                // (4,3),(2,1) -> (4,3),(2,1), i.e. L,R->L,R
                perm: P0,
                form: Halves,
                active: 0b1111,
            },
            Expectation {
                config: configval(0o230),
                // (4,3) -> (4,3), i.e L->L
                perm: P0,
                form: Halves,
                active: 0b1100,
            },
            Expectation {
                config: configval(0o232),
                // (2,1) -> (4,3), i.e. R->L
                perm: P2,
                form: Halves,
                active: 0b1100,
            },
            Expectation {
                config: configval(0o732),
                // (1) -> (3)
                perm: P2,
                form: Quarters,
                active: 0b0100,
            },
            // Indexes 024 to 027
            Expectation {
                config: configval(0o733),
                // (2) -> (3)
                perm: P3,
                form: Quarters,
                active: 0b0100,
            },
            Expectation {
                config: configval(0o730),
                // (3) -> (3)
                perm: P0,
                form: Quarters,
                active: 0b0100,
            },
            Expectation {
                config: configval(0o731),
                // (4) -> (3)
                perm: P1,
                form: Quarters,
                active: 0b0100,
            },
            Expectation {
                config: configval(0o605),
                // (4),(3),(2),(1) -> (1),(2),(3),(4)
                perm: P5,
                form: Quarters,
                active: 0b1111,
            },
            // Indexes 030 to 033
            Expectation {
                config: configval(0o600),
                // (4),(3),(2),(1) -> (4),(3),(2),(1)
                perm: P0,
                form: Quarters,
                active: 0b1111,
            },
            Expectation {
                config: configval(0o750),
                // (2) -> (2)
                perm: P0,
                form: Quarters,
                active: 0b0010,
            },
            Expectation {
                config: configval(0o670),
                // (4) -> (4)
                perm: P0,
                form: Quarters,
                active: 0b1000,
            },
            Expectation {
                config: configval(0o320),
                // (3),(1) -> (3),(1); sign extend (1) into L, (3) into R
                perm: P0,
                form: Halves,
                active: 0b0101,
            },
            // Indexes 034 to 037
            Expectation {
                config: configval(0o333),
                // (2) -> (3) and sign extend into L
                perm: P3,
                form: Halves,
                active: 0b0100,
            },
            Expectation {
                config: configval(0o330),
                // (3) -> (3) and sign extend into L
                perm: P0,
                form: Halves,
                active: 0b0100,
            },
            Expectation {
                config: configval(0o331),
                // (4) -> (3) and sign extend into L
                perm: P1,
                form: Halves,
                active: 0b0100,
            },
            Expectation {
                config: configval(0o604),
                // (4),(3),(2),(1) -> (3),(4),(1),(2)
                perm: P4,
                form: Quarters,
                active: 0b1111,
            },
        ];

        // Validate the system configuration value in the current test
        // case against the values from table 7-2 in the user
        // handbook.
        for (index, case) in cases.iter().enumerate() {
            let cfg = Unsigned9Bit::try_from(STANDARD_CONFIG[index]).expect("valid test data");
            assert_eq!(
                cfg, case.config,
                "config in test case does not match standard config"
            );
        }

        let f_memory = standard_plugboard_f_memory_settings();
        for (index, case) in cases.iter().enumerate() {
            let expected = case.config;
            let got = f_memory[index];
            assert_eq!(
                expected, got,
                "config at index {} in test case does not match standard config: {:o} != {:o}",
                index, expected, got,
            );
        }

        for case in cases.iter() {
            let sysconfig = SystemConfiguration(case.config);
            assert_eq!(
                sysconfig.permutation(),
                case.perm,
                "non-matching permutation"
            );
            assert_eq!(
                sysconfig.subword_form(),
                case.form,
                "non-matching subword form"
            );
            for q in 0u8..4u8 {
                let expect_active = case.active & (1 << q) != 0;
                let got_active = sysconfig.active_quarters().is_active(&q);
                assert_eq!(
                    got_active,
                    expect_active,
                    "expected quarter activity {:?}, got quarter activity {:?}",
                    case.active,
                    sysconfig.active_quarters()
                );
            }
        }
    }
}
