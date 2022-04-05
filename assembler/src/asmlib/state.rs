use std::cell::RefCell;
use std::fmt::{self, Display, Formatter};

use crate::parser::ErrorLocation;

#[derive(Debug, Clone)]
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
pub struct State<'b> {
    pub(crate) errors: &'b RefCell<Vec<Error>>,
    pub(crate) radix: NumeralMode,
}

impl<'b> State<'b> {
    pub fn new(errors: &'b RefCell<Vec<Error>>) -> State {
        State {
            errors,
            radix: NumeralMode::default(),
        }
    }
    pub fn report_error(&self, error: Error) {
        self.errors.borrow_mut().push(error);
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
