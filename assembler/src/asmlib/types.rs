use std::error::Error;
use std::ffi::OsStr;
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;
use std::path::PathBuf;

use base::prelude::Address;

use super::collections::OneOrMore;
use super::memorymap::RcWordSource;
use super::source::Source;
use super::source::{LineAndColumn, WithLocation};
use super::span::{Span, Spanned};
use super::symbol::SymbolName;

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct BlockIdentifier(usize);

impl From<usize> for BlockIdentifier {
    fn from(value: usize) -> Self {
        BlockIdentifier(value)
    }
}

impl From<BlockIdentifier> for usize {
    fn from(value: BlockIdentifier) -> usize {
        value.0
    }
}

impl BlockIdentifier {
    pub fn previous_block(&self) -> Option<BlockIdentifier> {
        self.0.checked_sub(1).map(BlockIdentifier)
    }
}

impl Display for BlockIdentifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "block {}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MachineLimitExceededFailure {
    RanOutOfIndexRegisters(Span, SymbolName),
    /// BlockTooLarge is used to report blocks whose length is not
    /// representable in an 18-bit halfword, or whose length is
    /// representable but whose start address wouild put the end of
    /// the block outside physical memory.
    BlockTooLarge {
        span: Span,
        block_id: BlockIdentifier,
        offset: usize,
    },
}

impl Spanned for MachineLimitExceededFailure {
    fn span(&self) -> Span {
        match self {
            MachineLimitExceededFailure::RanOutOfIndexRegisters(span, _)
            | MachineLimitExceededFailure::BlockTooLarge { span, .. } => *span,
        }
    }
}

impl Display for MachineLimitExceededFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            MachineLimitExceededFailure::RanOutOfIndexRegisters(_span, name) => {
                write!(
                    f,
                    "there are not enough index registers to assign one as the default for the symbol {name}"
                )
            }
            MachineLimitExceededFailure::BlockTooLarge {
                span: _,
                block_id,
                offset,
            } => {
                write!(
                    f,
                    "{block_id} is too large; offset {offset} does not fit in physical memory"
                )
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ProgramError {
    InconsistentTag {
        name: SymbolName,
        span: Span,
        msg: String,
    },
    SymbolDefinitionLoop {
        symbol_names: OneOrMore<SymbolName>,
        span: Span,
    },
    SyntaxError {
        msg: String,
        span: Span,
    },
    BlockTooLong(Span, MachineLimitExceededFailure),
    RcBlockTooLong {
        rc_word_source: RcWordSource,
        rc_word_span: Span,
    },
    FailedToAssignIndexRegister(Span, SymbolName),
}

impl Spanned for ProgramError {
    fn span(&self) -> Span {
        use ProgramError::*;
        match self {
            RcBlockTooLong {
                rc_word_span: span, ..
            }
            | FailedToAssignIndexRegister(span, _)
            | BlockTooLong(span, _)
            | InconsistentTag { span, .. }
            | SymbolDefinitionLoop { span, .. }
            | SyntaxError { span, .. } => *span,
        }
    }
}

impl Display for ProgramError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use ProgramError::*;
        match self {
            RcBlockTooLong {
                rc_word_source,
                rc_word_span: _,
            } => {
                write!(
                    f,
                    "RC-word block grew too long to allocate {rc_word_source}"
                )
            }
            FailedToAssignIndexRegister(_span, symbol_name) => {
                write!(
                    f,
                    "there are not enough index registers available to assign one for {symbol_name}"
                )
            }
            BlockTooLong(_span, mle) => {
                write!(f, "program block contains too many machine words: {mle}")
            }
            InconsistentTag { name, span: _, msg } => {
                write!(f, "inconsistent definitions for tag {name}: {msg}")
            }
            SymbolDefinitionLoop {
                symbol_names,
                span: _,
            } => {
                let (head, tail) = symbol_names.as_parts();
                write!(
                    f,
                    "symbol {head} is undefined because its definition forms a loop"
                )?;
                if !tail.is_empty() {
                    write!(f, ": {head}")?;
                    for name in tail.iter() {
                        write!(f, "->{name}")?;
                    }
                }
                Ok(())
            }
            SyntaxError { span: _, msg } => {
                write!(f, "{msg}")
            }
        }
    }
}

impl ProgramError {
    pub(crate) fn into_assembler_failure(self, source_file_body: &Source<'_>) -> AssemblerFailure {
        let span: Span = self.span();
        let location: LineAndColumn = source_file_body.location_of(span.start);
        AssemblerFailure::BadProgram(OneOrMore::new(WithLocation {
            location,
            inner: self,
        }))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum IoAction {
    Read,
    Write,
}

impl Display for IoAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            IoAction::Read => "read",
            IoAction::Write => "write",
        })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum IoTarget {
    File(PathBuf),
}

impl Display for IoTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            IoTarget::File(file_name) => {
                f.write_str("file ")?;
                write_os_string(f, file_name.as_os_str())
            }
        }
    }
}

#[derive(Debug)]
pub struct IoFailed {
    pub action: IoAction,
    pub target: IoTarget,
    pub error: IoError, // not cloneable, doesn't implement PartialEq
}

impl Display for IoFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let IoFailed {
            action,
            target,
            error,
        } = self;
        write!(f, "I/O error: {action} failed on {target}: {error}")
    }
}

impl PartialEq<IoFailed> for IoFailed {
    // We implement this ourselves since IoError does not implement PartialEq.
    fn eq(&self, other: &IoFailed) -> bool {
        self.action == other.action
            && self.target == other.target
            && self.error.to_string() == other.error.to_string()
    }
}

impl Eq for IoFailed {}

#[derive(Debug, PartialEq, Eq)]
pub enum AssemblerFailure {
    InternalError(String),
    BadTapeBlock {
        address: Address,
        length: usize,
        msg: String,
    },
    Io(IoFailed), // not cloneable
    BadProgram(OneOrMore<WithLocation<ProgramError>>),
    MachineLimitExceeded(MachineLimitExceededFailure),
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
            AssemblerFailure::BadProgram(errors) => {
                for e in errors.iter() {
                    write!(f, "error in user program: {e}")?;
                }
                Ok(())
            }
            AssemblerFailure::InternalError(msg) => {
                write!(f, "internal error: {msg}")
            }
            AssemblerFailure::BadTapeBlock {
                address,
                length,
                msg,
            } => {
                write!(
                    f,
                    "bad tape block of length {length} words at address {address}: {msg}"
                )
            }
            AssemblerFailure::Io(e) => write!(f, "{e}"),
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
