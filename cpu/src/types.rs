use std::fmt::{self, Debug, Display, Formatter};

use base::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagChange {
    Raise,
}

/// A value of which bits 0..width are significant (0 being the least significant bit).
// Hence a six-bit value would be `MaskedWord { width: 6, value: u13!(0o77) }`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MaskedWord {
    pub bits: Unsigned36Bit,
    pub mask: Unsigned36Bit,
}

impl MaskedWord {
    pub fn apply(&self, dest: Unsigned36Bit) -> Unsigned36Bit {
        (dest & !self.mask) | (self.bits & self.mask)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransferMode {
    /// TSD instructions use the exchange unit (but not sign extension).
    Exchange,
    /// TSD instructions use assembly mode.
    Assembly,
}

#[derive(Debug)]
pub enum TransferFailed {
    BufferNotFree,
}

impl Display for TransferFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            TransferFailed::BufferNotFree => "Unit buffer not available for use by the CPU",
        })
    }
}

impl std::error::Error for TransferFailed {}

/// Determines whether a memory operation updates the E register.
#[derive(Debug)]
pub enum UpdateE {
    No,
    Yes,
}
