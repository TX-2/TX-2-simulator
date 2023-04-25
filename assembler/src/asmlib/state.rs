#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NumeralMode {
    Octal,
    Decimal,
}

impl NumeralMode {
    pub(crate) fn radix(&self, alternate: bool) -> u32 {
        match (&self, alternate) {
            (&NumeralMode::Octal, false) | (&NumeralMode::Decimal, true) => 8,
            (&NumeralMode::Decimal, false) | (&NumeralMode::Octal, true) => 10,
        }
    }

    pub(crate) fn set_numeral_mode(&mut self, mode: NumeralMode) {
        *self = mode;
    }
}

// defeat derivable_impls here because if we simply derive Default
// it's unclear which value we get as the default.
#[allow(clippy::derivable_impls)]
impl Default for NumeralMode {
    fn default() -> NumeralMode {
        NumeralMode::Octal
    }
}
