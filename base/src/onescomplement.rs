//! This module implements one's complement fixed-width signed types
//! for use in emulating the TX-2, plus related unsigned types of the
//! same width.
use test_strategy::Arbitrary;

pub mod error;
pub(crate) mod signed;
pub(crate) mod unsigned;

/// The sign of a number (mathematically, sgn(x)).  Although in a
/// one's-complement system all values have a sign, we treat zero
/// specially in order to simplify working with native types and
/// one's-complement types together.
#[derive(Arbitrary, Debug)]
pub(crate) enum Signum {
    Negative = -1, // <= -1
    Zero = 0,      // +0 or -0
    Positive = 1,  // >= +1
}

/// Trait common to both signed one's-complement types (defined in the
/// [`signed`] module) and unsigned types (defined in the [`unsigned`]
/// module).
pub(crate) trait WordCommon {
    fn signum(&self) -> Signum;
}
