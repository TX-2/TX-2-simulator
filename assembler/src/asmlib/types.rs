use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;
use std::path::PathBuf;

use base::prelude::Address;

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
        filename: PathBuf,
        error: IoError,
    },
    SyntaxError {
        line: LineNumber,
        column: Option<usize>,
        msg: String,
    },
    ProgramTooBig(Address, usize),
    UnimplementedFeature(String),
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
            AssemblerFailure::UnimplementedFeature(explanation) => {
                write!(f, "Program uses an unimplemented feature: {}", explanation)
            }
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
