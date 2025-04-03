#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum NumeralMode {
    #[default]
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

#[test]
fn test_numeral_mode_default() {
    assert_eq!(NumeralMode::default(), NumeralMode::Octal);
}
