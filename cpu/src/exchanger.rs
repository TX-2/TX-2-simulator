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
use std::fmt::{self, Binary, Display, Formatter, Octal};

use tracing::{event, Level};

use base::prelude::*;

/// The Exchange Element behaves differently in the M->E (i.e. load)
/// direction and the E->M (i.e. store) direction.  This enumeration
/// specifies the direction of the current transfer.
pub(crate) enum ExchangeDirection {
    /// Memory (M register) to AE (E register)
    ME,
    /// AE (E register) to Memory (M register)
    EM,
}

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

    pub fn first_active_quarter(&self) -> Option<u8> {
        let n = self.0.trailing_zeros() as u8;
        if n < 4 {
            Some(n)
        } else {
            None
        }
    }

    pub fn masked_by(&self, mask: u8) -> QuarterActivity {
        QuarterActivity::new(self.0 & mask)
    }
}

impl Binary for QuarterActivity {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:b}", self.0)
    }
}

#[test]
fn test_quarteractivity_first_active_quarter() {
    fn first_active_quarter(n: u8) -> Option<u8> {
        QuarterActivity(n).first_active_quarter()
    }
    assert_eq!(first_active_quarter(0), None);
    assert_eq!(first_active_quarter(0b0001), Some(0));
    assert_eq!(first_active_quarter(0b0011), Some(0));
    assert_eq!(first_active_quarter(0b1111), Some(0));
    assert_eq!(first_active_quarter(0b1110), Some(1));
    assert_eq!(first_active_quarter(0b0010), Some(1));
    assert_eq!(first_active_quarter(0b1100), Some(2));
    assert_eq!(first_active_quarter(0b0100), Some(2));
    assert_eq!(first_active_quarter(0b1000), Some(3));
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
    pub fn active_quarters(&self) -> QuarterActivity {
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
/// The numbering is for the load direction (i.e. data is travelling
/// _downwards_ in the standard permutation diagram in table 7-2 of
/// the Users Handbook).
///
/// Permutation behaviour is described in Volume 2 of the Technnical
/// Manual.  In particular see section 12-6.4 and figure 12-45 (page
/// 12-75), and figures 13-12 and 13-13 (pages 13-24 and 13-25).
fn permutation_source(
    permutation: &Permutation,
    direction: &ExchangeDirection,
    target_quarter: u8,
) -> u8 {
    match permutation {
        Permutation::P0 => target_quarter % 4,
        Permutation::P1 => match *direction {
            ExchangeDirection::ME => (target_quarter + 3) % 4,
            ExchangeDirection::EM => (target_quarter + 1) % 4,
        },
        Permutation::P2 => (target_quarter + 2) % 4,
        Permutation::P3 => match *direction {
            ExchangeDirection::ME => (target_quarter + 1) % 4,
            ExchangeDirection::EM => (target_quarter + 3) % 4,
        },
        Permutation::P4 => target_quarter ^ 0b01,
        Permutation::P5 => target_quarter ^ 0b11,
        Permutation::P6 => match (direction, target_quarter) {
            (&ExchangeDirection::ME, 3) => 2,
            (&ExchangeDirection::ME, 2) => 1,
            (&ExchangeDirection::ME, 1) => 3,
            (&ExchangeDirection::ME, 0) => 0,
            (&ExchangeDirection::EM, 3) => 1,
            (&ExchangeDirection::EM, 2) => 3,
            (&ExchangeDirection::EM, 1) => 2,
            (&ExchangeDirection::EM, 0) => 0,
            (_, _) => unreachable!(),
        },
        Permutation::P7 => match (direction, target_quarter) {
            (&ExchangeDirection::ME, 3) => 1,
            (&ExchangeDirection::ME, 2) => 3,
            (&ExchangeDirection::ME, 1) => 2,
            (&ExchangeDirection::ME, 0) => 0,
            (&ExchangeDirection::EM, 3) => 2,
            (&ExchangeDirection::EM, 2) => 1,
            (&ExchangeDirection::EM, 1) => 3,
            (&ExchangeDirection::EM, 0) => 0,
            (_, _) => unreachable!(),
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
    let signbit = word & (0o400 << (quarter_number_from * 9));
    let mask = quarter_mask(quarter_number_to);
    if signbit == 0 {
        word & !mask
    } else {
        word | mask
    }
}

fn sign_extend_quarters(
    w: Unsigned36Bit,
    activity: QuarterActivity,
    ordering: &[u8],
) -> Unsigned36Bit {
    let mut word: u64 = u64::from(w);
    if let Some(mut last_active) = activity.first_active_quarter() {
        for q in ordering {
            if activity.is_active(q) {
                last_active = *q;
            } else {
                word = apply_sign(word, last_active, *q);
            }
        }
        Unsigned36Bit::try_from(word).expect("result should be in range (this is a bug)")
    } else {
        w
    }
}

/// Perform sign extension.  From User Handbook, figure 13-14, "The
/// sign bit of an active quarter of a partially-active subword is
/// extended to the left until an active quarter is again met, this
/// must be interpreted in terms of the possible partially active
/// subwords".  I don't know what the second part of this sentence
/// means.  The accompanying diagram shows the sign bit being extended
/// into quarters that are to the right of an active quarter (in order
/// words the leftward extension wraps after it hits q4).
pub fn sign_extend(
    form: &SubwordForm,
    word: Unsigned36Bit,
    quarter_activity: QuarterActivity,
) -> Unsigned36Bit {
    match form {
        SubwordForm::FullWord => {
            // sign extension happens across all quarters.
            match quarter_activity.first_active_quarter() {
                Some(q) => {
                    let extend_order: Vec<u8> = (q..(q + 4)).map(|q| q % 4).collect();
                    sign_extend_quarters(word, quarter_activity, &extend_order)
                }
                None => word,
            }
        }
        SubwordForm::Halves => {
            // AABB: sign extension happens within AA and separately in BB
            let left_activity = quarter_activity.masked_by(0b1100);
            let sign_extended_on_lhs = match left_activity.first_active_quarter() {
                None => word,
                Some(first_active) => sign_extend_quarters(
                    word,
                    left_activity,
                    match first_active {
                        2 => &[2, 3],
                        3 => &[3, 2],
                        _ => unreachable!(),
                    },
                ),
            };
            let right_activity = quarter_activity.masked_by(0b0011);
            let sign_extended_on_rhs = match right_activity.first_active_quarter() {
                None => word,
                Some(first_active) => sign_extend_quarters(
                    word,
                    right_activity,
                    match first_active {
                        0 => &[0, 1],
                        1 => &[1, 0],
                        _ => unreachable!(),
                    },
                ),
            };
            join_halves(
                left_half(sign_extended_on_lhs),
                right_half(sign_extended_on_rhs),
            )
        }
        SubwordForm::ThreeOne => {
            // AAAB: sign extension happens within AAA
            let left_activity = quarter_activity.masked_by(0b1110);
            match left_activity.first_active_quarter() {
                None => word,
                Some(first_active) => sign_extend_quarters(
                    word,
                    left_activity,
                    match first_active {
                        1 => &[1, 2, 3],
                        2 => &[2, 3, 1],
                        3 => &[3, 1, 2],
                        _ => unreachable!(),
                    },
                ),
            }
        }
        SubwordForm::Quarters => {
            word // ABCD: Nothing to do.
        }
    }
}

#[test]
fn test_sign_extend_full_word() {
    use SubwordForm::*;

    // When all quarters are active, sign extension should make no difference.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            Unsigned36Bit::from(0_u8),
            QuarterActivity::new(0b1111)
        ),
        u36!(0)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o300_000_000_000),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o300_000_000_000)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o000_300_000_000),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o000_300_000_000)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o000_000_300_000),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o000_000_300_000)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o000_000_000_300),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o000_000_000_300)
    );

    // If no quarters are active, there is nothing to sign-extend from, so sign extension is a no-op.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o444333222111),
            QuarterActivity::new(0b0000)
        ),
        u36!(0o444333222111)
    );

    // Sign-extending a positive quantity into a quarter should zero it.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_003_002_001),
            QuarterActivity::new(0b0111)
        ),
        u36!(0o000_003_002_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_727_002_001),
            QuarterActivity::new(0b1011)
        ),
        u36!(0o004_000_002_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_003_727_001),
            QuarterActivity::new(0b1101)
        ),
        u36!(0o004_003_000_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_003_002_727),
            QuarterActivity::new(0b1110)
        ),
        u36!(0o004_003_002_000)
    );

    // Sign-extending a negative quantity into a quarter should fill it with ones.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o272_403_002_001),
            QuarterActivity::new(0b0111)
        ),
        u36!(0o777_403_002_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_272_402_001),
            QuarterActivity::new(0b1011)
        ),
        u36!(0o004_777_402_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_003_272_401),
            QuarterActivity::new(0b1101)
        ),
        u36!(0o004_003_777_401)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o404_003_002_272),
            QuarterActivity::new(0b1110)
        ),
        u36!(0o404_003_002_777)
    );

    // We should be able to sign-extend over two consecutive quarters.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_003_002_727),
            QuarterActivity::new(0b0110)
        ),
        u36!(0o000_003_002_000)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_727_002_001),
            QuarterActivity::new(0b0011)
        ),
        u36!(0o000_000_002_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_727_727_001),
            QuarterActivity::new(0b1001)
        ),
        u36!(0o004_000_000_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_003_727_727),
            QuarterActivity::new(0b1100)
        ),
        u36!(0o004_003_000_000)
    );

    // We should be able to sign-extend a positive value over three consecutive quarters.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_727_727_001),
            QuarterActivity::new(0b0001)
        ),
        u36!(0o000_000_000_001)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_727_002_727),
            QuarterActivity::new(0b0010)
        ),
        u36!(0o000_000_002_000)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_003_727_727),
            QuarterActivity::new(0b0100)
        ),
        u36!(0o000_003_000_000),
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o004_727_727_727),
            QuarterActivity::new(0b1000)
        ),
        u36!(0o004_000_000_000)
    );

    // We should be able to sign-extend a negative value over three consecutive quarters.
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_727_727_401),
            QuarterActivity::new(0b0001)
        ),
        u36!(0o777_777_777_401)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_727_402_727),
            QuarterActivity::new(0b0010)
        ),
        u36!(0o777_777_402_777)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o727_403_727_727),
            QuarterActivity::new(0b0100)
        ),
        u36!(0o777_403_777_777)
    );
    assert_octal_eq!(
        sign_extend(
            &FullWord,
            u36!(0o404_727_727_727),
            QuarterActivity::new(0b1000)
        ),
        u36!(0o404_777_777_777),
    );
}

#[test]
fn test_sign_extend_halves() {
    use SubwordForm::*;

    // When all quarters are active, sign extension should make no difference.
    assert_octal_eq!(
        sign_extend(&Halves, u36!(0), QuarterActivity::new(0b1111)),
        u36!(0)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o400_000_000_000),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o400_000_000_000)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o000_400_000_000),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o000_400_000_000),
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o000_000_400_000),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o000_000_400_000)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o000_000_000_400),
            QuarterActivity::new(0b1111)
        ),
        u36!(0o000_000_000_400)
    );

    // If no quarters are active, there is nothing to sign-extend from, so sign extension is a no-op.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o444_333_222_111),
            QuarterActivity::new(0b0000)
        ),
        u36!(0o444_333_222_111)
    );

    // Sign-extending a positive quantity into a quarter should zero it.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b0101)
        ),
        u36!(0o000_003_000_001)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b0001)
        ),
        u36!(0o004_003_000_001)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b1010)
        ),
        u36!(0o004_000_002_000)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b0110)
        ),
        u36!(0o000_003_002_000)
    );

    // Sign-extending a negative quantity into a quarter should fill it with ones.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            // Q3 is negative, so Q4 is set to 777
            // Q1 is positive, so Q2 is set to 000
            u36!(0o004_403_202_001),
            QuarterActivity::new(0b0110)
        ),
        u36!(0o777_403_202_000)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o404_003_402_001),
            QuarterActivity::new(0b1010)
        ),
        u36!(0o404_777_402_777)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_403_002_401),
            QuarterActivity::new(0b0101)
        ),
        u36!(0o777_403_777_401)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_401),
            QuarterActivity::new(0b0001)
        ),
        u36!(0o004_003_777_401)
    );

    // We should not be able to sign-extend over more than two
    // consecutive quarters (e.g. from Q1 to Q2 and then Q3), because
    // the halves are only two quarters long.
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b0001)
        ),
        u36!(0o004_003_000_001)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b0010)
        ),
        u36!(0o004_003_002_000)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b0100)
        ),
        u36!(0o000_003_002_001)
    );
    assert_octal_eq!(
        sign_extend(
            &Halves,
            u36!(0o004_003_002_001),
            QuarterActivity::new(0b1000)
        ),
        u36!(0o004_000_002_001)
    );
}

// TODO: add tests for (27,9) and maybe (9,9,9,9).

/// Determine which quarter of `source` gets permuted into
/// `target_quarter` (numbered from zero), without regard to activity.
/// Return the value of that quarter, shifted down into the lowest
/// quarter (Q1, aka. quarter 0 when using u8 to indicate quarters).
fn fetch_quarter(source_quarter: u8, source: &u64) -> u64 {
    (source & quarter_mask(source_quarter)) >> (source_quarter * 9)
}

#[test]
fn test_fetch_quarter() {
    assert_octal_eq!(fetch_quarter(2, &0o444333222111), 0o333);
}

/// Copy bits from `source` to `dest`, permuting them according to
/// `permutation`.  Only active quarters are modified.
fn permute(
    permutation: &Permutation,
    direction: &ExchangeDirection,
    active_quarters: &QuarterActivity,
    source: &Unsigned36Bit,
    dest: &Unsigned36Bit,
) -> Unsigned36Bit {
    let mut result: u64 = (*dest).into();
    let source_bits: u64 = u64::from(*source);
    for target_quarter in 0_u8..4_u8 {
        let source_quarter: u8 = permutation_source(permutation, direction, target_quarter);

        // The active quarters are specified according to the quarter
        // number in the E register.  Hence for M->E (load-type)
        // transfers, they are the quarters of the destination, but
        // for E->M (store-type) transfers, they are the quarters of
        // the source.  See the descriptions in the Users Handbook,
        // sections 13-4.1 and 13-4.2.
        let e_quarter: u8 = match *direction {
            ExchangeDirection::ME => target_quarter,
            ExchangeDirection::EM => source_quarter,
        };
        if active_quarters.is_active(&e_quarter) {
            // `value` will be the value from the quarter we want,
            // shifted to the correct position.
            let value = fetch_quarter(source_quarter, &source_bits) << (target_quarter * 9);
            let target_mask: u64 = quarter_mask(target_quarter);
            result &= !target_mask;
            result |= target_mask & value;
        }
    }
    Unsigned36Bit::try_from(result).unwrap()
}

#[test]
fn test_permute_p0() {
    // P0 behaves the same in the ME and EM directions (q0<->q0,
    // q1<->q1 etc.). Our choice of quarter activity here means that
    // sign extension won't make a difference, so we get the same
    // result for ME and EM.
    for direction in &[ExchangeDirection::ME, ExchangeDirection::EM] {
        assert_octal_eq!(
            permute(
                &Permutation::P0,
                direction,
                &QuarterActivity::new(0b1111),
                &u36!(0o444333222111),
                &u36!(0o777666555444),
            ),
            u36!(0o444333222111),
        );
        assert_octal_eq!(
            permute(
                &Permutation::P0,
                direction,
                &QuarterActivity::new(0b1110),
                &u36!(0o444333222111),
                &u36!(0o777666555444),
            ),
            u36!(0o444333222444),
        );
    }
}

/// Perform an exchange operation suitable for a load operation; that
/// is, emulate the operation of the exchange unit diring e.g. LDA.
pub fn exchanged_value_for_load(
    cfg: &SystemConfiguration,
    source: &Unsigned36Bit,
    dest: &Unsigned36Bit,
) -> Unsigned36Bit {
    let active_quarters = cfg.active_quarters();
    let permuted_target = permute(
        &cfg.permutation(),
        &ExchangeDirection::ME,
        &active_quarters,
        source,
        dest,
    );
    sign_extend(&cfg.subword_form(), permuted_target, active_quarters)
}

/// Perform an exchange operation suitable for a store operation; that
/// is, emulate the operation of the exchange unit diring e.g. STE.
///
/// I believe that in this direction there is no sign extension.  This
/// is based on my reading of Chapter 13 of the Technical Manual.
/// Section 13-4.1 (covering loads) says "The sign extension process
/// which follows step 4 is described in 13-4.3.". But section 13-4.2
/// (covering stores) contains no similar statement. I suspect this
/// means that sign extension does not happen for stores.
pub fn exchanged_value_for_store(
    cfg: &SystemConfiguration,
    source: &Unsigned36Bit,
    dest: &Unsigned36Bit,
) -> Unsigned36Bit {
    permute(
        &cfg.permutation(),
        &ExchangeDirection::EM,
        &cfg.active_quarters(),
        source,
        dest,
    )
    // No sign extension in this direction, see doc comment for
    // rationale.
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
