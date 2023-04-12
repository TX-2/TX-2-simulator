use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;

use base::prelude::*;

use crate::ek;

/// LineNumber values are usually derived from
/// LocatedSpan::line_location() which returns a u32.
pub(crate) type LineNumber = u32;

#[derive(Debug)]
pub enum AssemblerFailure {
    Unimplemented(String),
    BadTapeBlock(String),
    IoErrorOnStdout {
        error: IoError,
    },
    IoErrorOnInput {
        filename: OsString,
        error: IoError,
        line_number: Option<LineNumber>,
    },
    IoErrorOnOutput {
        filename: OsString,
        error: IoError,
    },
    SyntaxError {
        line: LineNumber,
        column: Option<usize>,
        msg: String,
    },
}

fn write_os_string(f: &mut Formatter<'_>, s: &OsStr) -> Result<(), fmt::Error> {
    match s.to_str() {
        Some(unicode_name) => f.write_str(unicode_name),
        None => write!(
            f,
            "{} (some non-Unicode characters changed to make it printable)",
            s.to_string_lossy(),
        ),
    }
}

impl Display for AssemblerFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            AssemblerFailure::BadTapeBlock(explanation) => {
                write!(f, "bad tape block: {}", explanation)
            }
            AssemblerFailure::Unimplemented(explanation) => {
                write!(f, "use of unimplemented feature: {}", explanation)
            }
            AssemblerFailure::IoErrorOnStdout { error } => {
                write!(f, "error writing on stdout: {}", error)
            }
            AssemblerFailure::IoErrorOnInput {
                filename,
                error,
                line_number,
            } => {
                f.write_str("I/O error reading input file ")?;
                write_os_string(f, filename)?;
                if let Some(n) = line_number {
                    write!(f, " at line {}", n)?;
                }
                write!(f, ": {}", error)
            }
            AssemblerFailure::IoErrorOnOutput { filename, error } => {
                f.write_str("I/O error writing output file ")?;
                write_os_string(f, filename)?;
                write!(f, ": {}", error)
            }
            AssemblerFailure::SyntaxError { line, column, msg } => match column {
                Some(col) => {
                    // We count columns from 0 in the implementation, but 1 in error
                    // messages.
                    write!(f, "line {}, column {}: {}", line, col + 1, msg)
                }
                None => {
                    write!(f, "line {}: {}", line, msg)
                }
            },
        }
    }
}

impl Error for AssemblerFailure {}

#[derive(Debug)]
pub enum Fail {
    AsmFail(AssemblerFailure),
    InitialisationFailure(String),
}

impl Display for Fail {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Fail::AsmFail(assembler_failure) => assembler_failure.fmt(f),
            Fail::InitialisationFailure(msg) => f.write_str(msg.as_str()),
        }
    }
}

impl Error for Fail {}

/// Eventually we will support symbolic expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LiteralValue {
    elevation: Elevation,
    value: Unsigned36Bit,
}

impl LiteralValue {
    pub(crate) fn value(&self) -> Unsigned36Bit {
        self.value << self.elevation.shift()
    }
}

impl From<(Elevation, Unsigned36Bit)> for LiteralValue {
    fn from((elevation, value): (Elevation, Unsigned36Bit)) -> LiteralValue {
        LiteralValue { elevation, value }
    }
}

/// Eventually we will support symbolic expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Expression {
    Literal(LiteralValue),
}

impl Expression {
    fn value(&self) -> Unsigned36Bit {
        match self {
            Expression::Literal(literal) => literal.value(),
        }
    }
}

impl From<LiteralValue> for Expression {
    fn from(literal: LiteralValue) -> Expression {
        Expression::Literal(literal)
    }
}

impl From<(Elevation, Unsigned36Bit)> for Expression {
    fn from((e, v): (Elevation, Unsigned36Bit)) -> Expression {
        Expression::from(LiteralValue::from((e, v)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Elevation {
    Superscript, // e.g. config values
    Normal,      // e.g. the address part of an instruction
    Subscript,   // e.g. the index bits
}

impl Elevation {
    fn shift(&self) -> u32 {
        match self {
            Elevation::Superscript => 30, // This is a config value.
            Elevation::Subscript => 18,   // This is an index value
            Elevation::Normal => 0,       // e.g. an address value
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstructionFragment {
    pub(crate) value: Expression,
}

impl InstructionFragment {
    pub(crate) fn value(&self) -> Unsigned36Bit {
        self.value.value()
    }
}

impl From<(Elevation, Unsigned36Bit)> for InstructionFragment {
    fn from((e, v): (Elevation, Unsigned36Bit)) -> InstructionFragment {
        InstructionFragment {
            value: Expression::from((e, v)),
        }
    }
}

impl From<Expression> for InstructionFragment {
    fn from(e: Expression) -> Self {
        Self { value: e }
    }
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct SymbolName {
    pub(crate) canonical: String,
    // pub(crate) as_used: String,
}

impl PartialEq for SymbolName {
    fn eq(&self, other: &SymbolName) -> bool {
        self.canonical.eq(&other.canonical)
    }
}

impl<'a, 'b> SymbolName {
    // Symexes "TYPE A" and "TYPEA" are equivalent.
    fn canonical(span: &ek::LocatedSpan<'a, 'b>) -> String {
        (*span.fragment())
            .chars()
            .filter(|ch: &char| -> bool { *ch != ' ' })
            .collect()
    }
}

impl<'a, 'b> From<&ek::LocatedSpan<'a, 'b>> for SymbolName {
    fn from(location: &ek::LocatedSpan<'a, 'b>) -> SymbolName {
        SymbolName {
            canonical: SymbolName::canonical(location),
            //as_used: location.fragment().to_string(),
        }
    }
}

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug)]
pub(crate) struct SymbolTable {}
impl SymbolTable {
    pub(crate) fn new() -> SymbolTable {
        SymbolTable {}
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        true
    }

    pub(crate) fn list(&self) -> Result<(), std::io::Error> {
        Ok(())
    }
}
