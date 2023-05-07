//! Basic error reporting.

use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};

/// Represents a failure to convert to or from one of the signed or
/// unsigned types defined in the base crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConversionFailed {
    // TODO: give more range-specific name
    TooLarge,
    TooSmall,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StringConversionFailed {
    Range(ConversionFailed),
    EmptyInput,
    NotOctal(char),
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

impl Display for StringConversionFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            StringConversionFailed::Range(e) => std::fmt::Display::fmt(&e, f),
            StringConversionFailed::NotOctal(ch) => {
                write!(f, "value contains a non-octal digit {ch}")
            }
            StringConversionFailed::EmptyInput => {
                f.write_str("an empty string is not a valid number")
            }
        }
    }
}
