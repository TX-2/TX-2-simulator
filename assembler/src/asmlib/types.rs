use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;

use base::prelude::*;

use crate::ek;

/// LineNumber values are usually derived from
/// LocatedSpan::line_location() which returns a u32.
pub type LineNumber = u32;

#[derive(Debug)]
pub enum AssemblerFailure {
    Unimplemented(String),
    IoErrorOnInput {
        filename: OsString,
        error: IoError,
        line_number: Option<LineNumber>,
    },
    SyntaxError {
        line: LineNumber,
        columns: Option<(usize, usize)>,
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
            AssemblerFailure::Unimplemented(explanation) => {
                write!(f, "use of unimplemented feature: {}", explanation)
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
            AssemblerFailure::SyntaxError { line, columns, msg } => match columns {
                Some((column_from, _)) => {
                    // We count columns from 0 in the implementation, but 1 in error
                    // messages.
                    write!(f, "line {}, column {}: {}", line, column_from + 1, msg)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elevation {
    Superscript, // e.g. config values
    Normal,      // e.g. the address part of an instruction
    Subscript,   // e.g. the index bits
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionFragment {
    pub elevation: Elevation,
    pub value: Unsigned36Bit,
}

#[derive(Debug, Clone, Eq)]
pub struct SymbolName {
    pub canonical: String,
    pub as_used: String,
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
            as_used: location.fragment().to_string(),
        }
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    // A symbol which has a reference but no definition is allowed,
// and we represent it by having it map to None.  The rules for
// how such symbols are assigned values are indicated in
// "Unassigned Symexes" in section 6-2.2 of the User Handbook.
//syms: HashMap<String, Option<SymbolDefinition>>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {}
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        // self.syms.is_empty()
        true
    }
}