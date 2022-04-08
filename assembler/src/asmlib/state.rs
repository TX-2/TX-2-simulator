use std::cell::RefCell;
use std::fmt::{self, Display, Formatter};

use crate::parser::ErrorLocation;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumeralMode {
    Octal,
    Decimal,
}

impl Default for NumeralMode {
    fn default() -> NumeralMode {
        NumeralMode::Octal
    }
}

#[derive(Debug, Clone)]
pub struct Error(pub ErrorLocation, pub String);

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self.0.columns.as_ref() {
            None => write!(f, "{}: {}", self.0.line, self.1,),
            Some(cols) => write!(f, "{}:{}: {}", self.0.line, cols.start, self.1,),
        }
    }
}

#[derive(Clone, Debug)]
pub struct State {
    pub(crate) errors: Vec<Error>,
    pub(crate) radix: NumeralMode,
}

impl State {
    pub fn new() -> State {
        State {
            errors: Vec::new(),
            radix: NumeralMode::default(),
        }
    }

    pub fn report_error(&mut self, error: Error) {
        self.errors.push(error);
    }

    pub fn radix(&self, alternate: bool) -> u32 {
        match (&self.radix, alternate) {
            (&NumeralMode::Octal, false) | (&NumeralMode::Decimal, true) => 8,
            (&NumeralMode::Decimal, false) | (&NumeralMode::Octal, true) => 10,
        }
    }

    pub fn set_numeral_mode(&mut self, numeral_mode: NumeralMode) {
        self.radix = numeral_mode
    }
}

#[derive(Clone, Debug)]
pub struct StateExtra<'b> {
    inner: &'b RefCell<State>,
}

impl<'b> StateExtra<'b> {
    pub fn new(state: &'b RefCell<State>) -> StateExtra<'b> {
        StateExtra { inner: state }
    }

    pub fn report_error(&self, error: Error) {
        self.inner.borrow_mut().report_error(error);
    }

    pub fn radix(&self, alternate: bool) -> u32 {
        self.inner.borrow().radix(alternate)
    }

    pub fn set_numeral_mode(&self, numeral_mode: NumeralMode) {
        self.inner.borrow_mut().set_numeral_mode(numeral_mode);
    }
}
