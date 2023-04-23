use std::cell::RefCell;
use std::fmt::{self, Display, Formatter};

use super::parser::ErrorLocation;

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

#[derive(Debug, Clone)]
pub(crate) struct Error(pub(crate) ErrorLocation, pub(crate) String);

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self.0.column.as_ref() {
            None => write!(f, "{}: {}", self.0.line, self.1,),
            Some(col) => write!(f, "{}:{}: {}", self.0.line, col, self.1,),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct State {
    pub(crate) errors: Vec<Error>,
    pub(crate) radix: NumeralMode,
}

impl State {
    pub(crate) fn new() -> State {
        State {
            errors: Vec::new(),
            radix: NumeralMode::default(),
        }
    }

    pub(crate) fn report_error(&mut self, error: Error) {
        self.errors.push(error);
    }

    pub(crate) fn radix(&self, alternate: bool) -> u32 {
        self.radix.radix(alternate)
    }

    pub(crate) fn set_numeral_mode(&mut self, mode: NumeralMode) {
        self.radix.set_numeral_mode(mode)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct StateExtra<'b> {
    inner: &'b RefCell<State>,
}

impl<'b> StateExtra<'b> {
    pub(crate) fn new(state: &'b RefCell<State>) -> StateExtra<'b> {
        StateExtra { inner: state }
    }

    pub(crate) fn report_error(&self, error: Error) {
        self.inner.borrow_mut().report_error(error);
    }

    pub(crate) fn radix(&self, alternate: bool) -> u32 {
        self.inner.borrow().radix(alternate)
    }

    pub(crate) fn set_numeral_mode(&self, mode: NumeralMode) {
        self.inner.borrow_mut().set_numeral_mode(mode);
    }
}
