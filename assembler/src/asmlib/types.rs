use std::error::Error;
use std::ffi::OsStr;
use std::fmt::{self, Display, Formatter};
use std::io::Error as IoError;
use std::path::PathBuf;

use super::span::{Span, Spanned};
use super::symbol::SymbolName;
use base::prelude::{Address, Unsigned18Bit};

/// LineNumber values are usually derived from
/// LocatedSpan::line_location() which returns a u32.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct LineAndColumn {
    line: u32,
    column: u32,
    span: Span,
}

impl Display for LineAndColumn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, column {}", self.line, self.column)
    }
}

impl From<(&str, &Span)> for LineAndColumn {
    fn from((body, span): (&str, &Span)) -> Self {
        const START_COL: u32 = 1;
        const START_LINE: u32 = 1;

        let mut line = START_LINE;
        let mut column = START_COL;
        let pos = span.start;
        for (i, ch) in body.char_indices() {
            if i == pos {
                break;
            }
            match ch {
                '\n' => {
                    column = START_COL;
                    line += 1;
                }
                _ => {
                    column += 1;
                }
            }
        }
        LineAndColumn {
            span: *span,
            line,
            column,
        }
    }
}

pub trait Located {
    fn location(&self) -> LineAndColumn;
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct WithLocation<T> {
    pub(crate) inner: T,
    pub(crate) location: LineAndColumn,
}

impl<T> Located for WithLocation<T> {
    fn location(&self) -> LineAndColumn {
        self.location.clone()
    }
}

impl<T: Spanned> From<(&str, T)> for WithLocation<T> {
    fn from((body, item): (&str, T)) -> WithLocation<T> {
        let span: Span = item.span();
        let location = LineAndColumn::from((body, &span));
        WithLocation {
            inner: item,
            location,
        }
    }
}

impl<T: Located> From<T> for WithLocation<T> {
    fn from(inner: T) -> WithLocation<T> {
        WithLocation {
            location: inner.location().clone(),
            inner,
        }
    }
}

impl<T> WithLocation<T> {
    pub fn location(&self) -> &LineAndColumn {
        &self.location
    }
}

impl<T: Display> Display for WithLocation<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", &self.location, &self.inner)
    }
}

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

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct BlockIdentifier(usize);

impl From<usize> for BlockIdentifier {
    fn from(value: usize) -> Self {
        BlockIdentifier(value)
    }
}

impl BlockIdentifier {
    pub fn next_block(&self) -> Option<BlockIdentifier> {
        Some(
            self.0
                .checked_add(1)
                .map(BlockIdentifier)
                .expect("block count should not overflow"),
        )
    }

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
                write!(f, "there are not enough index registers to assign one as the default for the symbol {name}")
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
pub struct InconsistentOrigin {
    pub(crate) origin_name: SymbolName,
    pub(crate) span: Span,
    pub(crate) msg: String,
}

impl Display for InconsistentOrigin {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "inconsistent definitions for origin {}: {}",
            self.origin_name, self.msg,
        )
    }
}

impl Spanned for InconsistentOrigin {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug)]
pub enum ProgramError {
    InconsistentOriginDefinitions(InconsistentOrigin),
    InconsistentTag {
        name: SymbolName,
        span: Span,
        msg: String,
    },
    UnexpectedlyUndefinedSymbol {
        name: SymbolName,
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
            InconsistentOriginDefinitions(e) => e.span(),
            RcBlockTooLong {
                rc_word_span: span, ..
            }
            | FailedToAssignIndexRegister(span, _)
            | BlockTooLong(span, _)
            | InconsistentTag { span, .. }
            | UnexpectedlyUndefinedSymbol { span, .. }
            | SyntaxError { span, .. } => *span,
        }
    }
}

impl PartialEq<ProgramError> for ProgramError {
    fn eq(&self, other: &ProgramError) -> bool {
        use ProgramError::*;
        match (self, other) {
            (InconsistentOriginDefinitions(e1), InconsistentOriginDefinitions(e2)) if e1 == e2 => {
                true
            }
            (
                UnexpectedlyUndefinedSymbol { name: n1, span: p1 },
                UnexpectedlyUndefinedSymbol { name: n2, span: p2 },
            ) if n1 == n2 && p1 == p2 => true,
            (SyntaxError { msg: m1, span: p1 }, SyntaxError { msg: m2, span: p2 })
                if m1 == m2 && p1 == p2 =>
            {
                true
            }
            _ => false,
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
                write!(f, "there are not enough index registers available to assign one for {symbol_name}")
            }
            BlockTooLong(_span, mle) => {
                write!(f, "program block contains too many machine words: {mle}")
            }
            InconsistentTag { name, span: _, msg } => {
                write!(f, "inconsistent definitions for tag {name}: {msg}")
            }
            InconsistentOriginDefinitions(e) => write!(f, "{e}"),
            UnexpectedlyUndefinedSymbol { name, span: _ } => {
                write!(f, "unexpected undefined symbol: {name}")
            }
            SyntaxError { span: _, msg } => {
                write!(f, "{}", msg)
            }
        }
    }
}

impl ProgramError {
    pub(crate) fn into_assembler_failure(self, source_file_body: &str) -> AssemblerFailure {
        let span: Span = self.span();
        let location: LineAndColumn = LineAndColumn::from((source_file_body, &span));
        AssemblerFailure::BadProgram(vec![WithLocation {
            location,
            inner: self,
        }])
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    pub error: IoError,
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
    fn eq(&self, other: &IoFailed) -> bool {
        self.action == other.action
            && self.target == other.target
            && self.error.to_string() == other.error.to_string()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum RcWordSource {
    PipeConstruct(Span),
    Braces(Span),
    DefaultAssignment(Span, SymbolName),
}

impl Spanned for RcWordSource {
    fn span(&self) -> Span {
        match self {
            RcWordSource::PipeConstruct(span)
            | RcWordSource::Braces(span)
            | RcWordSource::DefaultAssignment(span, _) => *span,
        }
    }
}

impl Display for RcWordSource {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RcWordSource::PipeConstruct(_) => write!(f, "pipe construct"),
            RcWordSource::Braces(_) => write!(f, "RC-word"),
            RcWordSource::DefaultAssignment(_, name) => write!(f, "default-assignment of {name}"),
        }
    }
}

#[derive(Debug)]
pub enum AssemblerFailure {
    InternalError(String),
    BadTapeBlock {
        address: Address,
        length: usize,
        msg: String,
    },
    Io(IoFailed),
    BadProgram(Vec<WithLocation<ProgramError>>),
    MachineLimitExceeded(MachineLimitExceededFailure),
}

impl PartialEq<AssemblerFailure> for AssemblerFailure {
    fn eq(&self, other: &AssemblerFailure) -> bool {
        use AssemblerFailure::*;
        match (self, other) {
            (BadProgram(e1), BadProgram(e2)) if e1 == e2 => true,
            (InternalError(s1), InternalError(s2)) if s1 == s2 => true,
            (
                BadTapeBlock {
                    address: a1,
                    length: l1,
                    msg: s1,
                },
                BadTapeBlock {
                    address: a2,
                    length: l2,
                    msg: s2,
                },
            ) if a1 == a2 && l1 == l2 && s1 == s2 => true,
            (Io(e1), Io(e2)) if e1 == e2 => true,
            (MachineLimitExceeded(e1), MachineLimitExceeded(e2)) if e1 == e2 => true,
            _ => false,
        }
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
