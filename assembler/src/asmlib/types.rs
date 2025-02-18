use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;
use std::path::PathBuf;

use chumsky::prelude::SimpleSpan;

use super::symbol::SymbolName;
use base::prelude::{Address, Unsigned18Bit};

/// LineNumber values are usually derived from
/// LocatedSpan::line_location() which returns a u32.
pub(crate) type LineNumber = u32;

pub(crate) type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub(crate) struct OrderableSpan(pub(crate) Span);

impl From<Span> for OrderableSpan {
    fn from(span: Span) -> OrderableSpan {
        OrderableSpan(span)
    }
}

impl Ord for OrderableSpan {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.start.cmp(&other.0.start)
    }
}

impl PartialOrd for OrderableSpan {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.start.cmp(&other.0.start))
    }
}

impl PartialEq for OrderableSpan {
    fn eq(&self, other: &Self) -> bool {
        self.0.start.cmp(&other.0.start).is_eq()
    }
}

impl Eq for OrderableSpan {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MachineLimitExceededFailure {
    RanOutOfIndexRegisters(SymbolName),
    RcBlockTooLarge,
    BlockTooLarge {
        block_number: usize,
        block_origin: Address,
        offset: usize,
    },
}

impl Display for MachineLimitExceededFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            MachineLimitExceededFailure::RanOutOfIndexRegisters(name) => {
                write!(f, "there are not enough index registers to assign one as the default for the symbol {name}")
            }
            MachineLimitExceededFailure::RcBlockTooLarge => f.write_str("RC block is too large"),
            MachineLimitExceededFailure::BlockTooLarge {
                block_number,
                block_origin,
                offset,
            } => {
                write!(f, "program block {block_number} is too large; offset {offset} from block start {block_origin} does not fit in physical memory")
            }
        }
    }
}

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
    InvalidProgram {
        span: Span,
        msg: String,
    },
    // TODO: InvalidProgram perhaps should be an enum which includes SyntaxError.
    SyntaxError {
        line: LineNumber,
        column: Option<usize>,
        msg: String,
    },
    MachineLimitExceeded(MachineLimitExceededFailure),
}

impl From<MachineLimitExceededFailure> for AssemblerFailure {
    fn from(f: MachineLimitExceededFailure) -> AssemblerFailure {
        AssemblerFailure::MachineLimitExceeded(f)
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
            AssemblerFailure::InvalidProgram { span: _, msg } => {
                // TODO: converting a span into line and column
                // numbers requires access to the text of the input.
                // While we could include a str reference here for
                // this, we'd be inconsistent with the way that
                // SyntaxError is handled (which is that the line
                // numbers are already resolved).
                //
                // Perhaps we can do better by integrating Ariadne.
                write!(f, "error: {msg}")
            }
            AssemblerFailure::MachineLimitExceeded(fail) => {
                write!(f, "machine limit exceeded: {fail}")
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
pub(crate) struct AddressOverflow(pub(crate) Address, pub(crate) Unsigned18Bit);

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
    offset: Unsigned18Bit,
) -> Result<Address, AddressOverflow> {
    let (physical, _mark) = origin.split();
    match physical.checked_add(offset) {
        Some(total) => Ok(Address::from(total)),
        None => Err(AddressOverflow(*origin, offset)),
    }
}
