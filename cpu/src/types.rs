use std::fmt::Debug;

use serde::Serialize;

use base::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FlagChange {
    Raise(&'static str),
}

/// A value of which bits 0..width are significant (0 being the least
/// significant bit).  Hence a six-bit value would be `MaskedWord {
/// width: 6, value: u13!(0o77) }`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MaskedWord {
    pub bits: Unsigned36Bit,
    pub mask: Unsigned36Bit,
}

impl MaskedWord {
    #[must_use]
    pub fn apply(&self, dest: Unsigned36Bit) -> Unsigned36Bit {
        (dest & !self.mask) | (self.bits & self.mask)
    }
}

/// Determines how TSD instructions for Lincoln Writer seuenced behave.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransferMode {
    /// TSD instructions use the exchange unit (but not sign extension).
    Exchange,
    /// TSD instructions use assembly mode.
    Assembly,
}

/// Determines whether a memory operation updates the E register.
#[derive(Debug)]
pub enum UpdateE {
    No,
    Yes,
}
