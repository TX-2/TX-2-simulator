use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;
use std::path::PathBuf;

use super::driver::SymbolLookupFailure;
use super::symbol::SymbolName;
use base::prelude::{Address, Unsigned18Bit};

/// LineNumber values are usually derived from
/// LocatedSpan::line_location() which returns a u32.
pub(crate) type LineNumber = u32;

#[derive(Debug)]
pub enum AssemblerFailure {
    InternalError(String),
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
        filename: PathBuf,
        error: IoError,
    },
    SyntaxError {
        line: LineNumber,
        column: Option<usize>,
        msg: String,
    },
    ProgramTooBig(Address, usize),
    SymbolError(SymbolName, SymbolLookupFailure),
}

impl From<SymbolLookupFailure> for AssemblerFailure {
    fn from(f: SymbolLookupFailure) -> AssemblerFailure {
        let symbol = f.symbol_name();
        AssemblerFailure::SymbolError(symbol.clone(), f)
    }
}

impl From<AddressOverflow> for AssemblerFailure {
    fn from(e: AddressOverflow) -> AssemblerFailure {
        AssemblerFailure::ProgramTooBig(e.0, e.1)
    }
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
            AssemblerFailure::InternalError(msg) => {
                write!(f, "internal error: {msg}")
            }
            AssemblerFailure::SymbolError(symbol, e) => {
                write!(f, "symbol lookup failure for {symbol}: {e}")
            }
            AssemblerFailure::BadTapeBlock(explanation) => {
                write!(f, "bad tape block: {}", explanation)
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
                write!(
                    f,
                    "I/O error writing output file {}: {error}",
                    filename.display(),
                )
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
            AssemblerFailure::ProgramTooBig(base, block_size) => {
                write!(
                    f,
                    "Program goes not fit into TX-2 memory; a block has origin {base:o} and size {block_size:o} but the largest possible address is {:o}", Address::MAX
                )
            }
        }
    }
}

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

#[derive(Debug)]
pub(crate) struct AddressOverflow(pub(crate) Address, pub(crate) usize);

impl std::error::Error for AddressOverflow {}

impl Display for AddressOverflow {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "Adding {:o} to {:o} would generate a result which doesn't fit into an 18-bit address",
            self.0, self.1
        )
    }
}

pub(crate) fn offset_from_origin(
    origin: &Address,
    offset: usize,
) -> Result<Address, AddressOverflow> {
    let offset18 = Unsigned18Bit::try_from(offset).map_err(|_| AddressOverflow(*origin, offset))?;
    let (physical, _mark) = origin.split();
    match physical.checked_add(offset18) {
        Some(total) => Ok(Address::from(total)),
        None => Err(AddressOverflow(*origin, offset)),
    }
}
