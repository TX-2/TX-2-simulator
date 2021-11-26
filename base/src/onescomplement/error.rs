//! Basic error reporting.

use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};

/// Represents a failure to convert to or from one of the signed or
/// unsigned types defined in the base crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConversionFailed {
    TooLarge,
    TooSmall,
}

impl Error for ConversionFailed {}

impl Display for ConversionFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ConversionFailed::TooLarge => f.write_str("value is too large"),
            ConversionFailed::TooSmall => f.write_str("value is too small"),
        }
    }
}
