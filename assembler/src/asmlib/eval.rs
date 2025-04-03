use std::collections::BTreeSet;
use std::fmt::{self, Debug, Display, Formatter, Write};

use base::{
    charset::Script,
    prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit},
};

use crate::symtab::{LookupOperation, SymbolTable};

use super::ast::{RcAllocator, UntaggedProgramInstruction};
use super::symbol::SymbolName;
use super::types::{BlockIdentifier, MachineLimitExceededFailure, OrderableSpan, Span};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum LookupTarget {
    Symbol(SymbolName, Span),
    MemRef(MemoryReference, Span),
    /// Attempt to look up "here", that is, '#'.
    Hash(Span),
}

impl From<(SymbolName, Span)> for LookupTarget {
    fn from((sym, span): (SymbolName, Span)) -> LookupTarget {
        LookupTarget::Symbol(sym, span)
    }
}

impl From<(MemoryReference, Span)> for LookupTarget {
    fn from((r, span): (MemoryReference, Span)) -> LookupTarget {
        LookupTarget::MemRef(r, span)
    }
}

impl Display for LookupTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            LookupTarget::Hash(_) => f.write_char('#'),
            LookupTarget::Symbol(name, _) => {
                write!(f, "symbol {name}")
            }
            LookupTarget::MemRef(
                MemoryReference {
                    block_id,
                    block_offset: _,
                },
                _,
            ) => {
                write!(f, "{block_id}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct MemoryReference {
    pub(crate) block_id: BlockIdentifier,
    pub(crate) block_offset: usize,
}

// SymbolValue is the result of a symbol table lookup.
//
// TODO: in some places we want to do further processing of the
// looked-up result in ways that require us to specify a span.  The
// span of interest will usually be the span at which the symbol was
// actually defined, so we should also return that in SymbolValue.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolValue {
    Final(Unsigned36Bit),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SymbolLookupFailureKind {
    Inconsistent(String),
    Loop { deps_in_order: Vec<SymbolName> },
    MachineLimitExceeded(MachineLimitExceededFailure),
    HereIsNotAllowedHere,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SymbolLookupFailure {
    pub(crate) target: LookupTarget,
    pub(crate) kind: SymbolLookupFailureKind,
}

impl Display for SymbolLookupFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let desc = self.target.to_string();
        match self.kind() {
            SymbolLookupFailureKind::Inconsistent(msg) => f.write_str(msg.as_str()),
            SymbolLookupFailureKind::Loop { deps_in_order } => {
                let names: Vec<String> = deps_in_order.iter().map(|dep| dep.to_string()).collect();
                write!(
                    f,
                    "definition of {desc} has a dependency loop ({})",
                    names.join("->")
                )
            }
            SymbolLookupFailureKind::MachineLimitExceeded(fail) => {
                write!(f, "machine limit exceeded: {fail}")
            }
            SymbolLookupFailureKind::HereIsNotAllowedHere => {
                f.write_str("'#' (representing the current address) is not allowed here")
            }
        }
    }
}

impl From<(SymbolName, Span, SymbolLookupFailureKind)> for SymbolLookupFailure {
    fn from(
        (symbol_name, span, kind): (SymbolName, Span, SymbolLookupFailureKind),
    ) -> SymbolLookupFailure {
        SymbolLookupFailure {
            target: LookupTarget::Symbol(symbol_name, span),
            kind,
        }
    }
}

impl SymbolLookupFailure {
    pub(crate) fn kind(&self) -> &SymbolLookupFailureKind {
        &self.kind
    }
}

impl std::error::Error for SymbolLookupFailure {}

pub(crate) trait SymbolLookup {
    type Operation<'a>;

    fn lookup_with_op<R: RcAllocator>(
        &mut self,
        name: &SymbolName,
        span: Span, // TODO: use &Span?
        target_address: &HereValue,
        rc_allocator: &mut R,
        context: &SymbolContext,
        op: &mut Self::Operation<'_>,
    ) -> Result<SymbolValue, SymbolLookupFailure>;
}

/// HereValue specifies the value used for '#'
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum HereValue {
    /// '#' refers to an address
    Address(Address),
    /// NotAllowed is for when '#' is not allowed (this is used
    /// when evaluating an origin).
    NotAllowed,
}

impl HereValue {
    pub(crate) fn get_address(&self, span: &Span) -> Result<Address, SymbolLookupFailure> {
        match self {
            HereValue::Address(addr) => Ok(*addr),
            HereValue::NotAllowed => Err(SymbolLookupFailure {
                target: LookupTarget::Hash(*span),
                kind: SymbolLookupFailureKind::HereIsNotAllowedHere,
            }),
        }
    }
}

pub(crate) trait Evaluate {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure>;
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolUse {
    Reference(SymbolContext),
    Definition(SymbolDefinition),
    Origin(SymbolName, BlockIdentifier),
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum SymbolContextMergeError {
    ConflictingOrigin(BlockIdentifier, BlockIdentifier),
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub(crate) struct SymbolContext {
    // The "All members are false" context is the one in which we list
    // the values of symbols in the program listing.
    configuration: bool,
    index: bool,
    address: bool,
    origin_of_block: Option<BlockIdentifier>,
    uses: BTreeSet<OrderableSpan>, // Span does not implement Hash
}

impl SymbolContext {
    pub(crate) fn bits(&self) -> [bool; 4] {
        [
            self.configuration,
            self.index,
            self.address,
            self.origin_of_block.is_some(),
        ]
    }

    pub(crate) fn configuration() -> SymbolContext {
        SymbolContext {
            configuration: true,
            ..Default::default()
        }
    }

    pub(crate) fn also_set_index(&mut self) {
        self.index = true;
    }

    pub(crate) fn is_address(&self) -> bool {
        self.address
    }

    fn uses(span: Span) -> BTreeSet<OrderableSpan> {
        [OrderableSpan(span)].into_iter().collect()
    }

    pub(crate) fn origin(block_id: BlockIdentifier, span: Span) -> SymbolContext {
        SymbolContext {
            origin_of_block: Some(block_id),
            uses: SymbolContext::uses(span),
            ..Default::default()
        }
    }

    fn merge(&mut self, mut other: SymbolContext) -> Result<(), SymbolContextMergeError> {
        let origin = match (self.origin_of_block, other.origin_of_block) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x),
            (Some(x), Some(y)) => {
                if x == y {
                    Some(x)
                } else {
                    return Err(SymbolContextMergeError::ConflictingOrigin(x, y));
                }
            }
        };
        let result = SymbolContext {
            configuration: self.configuration || other.configuration,
            index: self.index || other.index,
            address: self.address || other.address,
            origin_of_block: origin,
            uses: {
                let mut u = BTreeSet::new();
                u.append(&mut self.uses);
                u.append(&mut other.uses);
                u
            },
        };
        *self = result;
        Ok(())
    }
}

impl From<(&Script, Span)> for SymbolContext {
    fn from((elevation, span): (&Script, Span)) -> SymbolContext {
        let (configuration, index, address) = match elevation {
            Script::Super => (true, false, false),
            Script::Sub => (false, true, false),
            Script::Normal => (false, false, true),
        };
        SymbolContext {
            configuration,
            index,
            address,
            origin_of_block: None,
            uses: SymbolContext::uses(span),
        }
    }
}

impl From<(Script, Span)> for SymbolContext {
    fn from((elevation, span): (Script, Span)) -> SymbolContext {
        SymbolContext::from((&elevation, span))
    }
}

#[derive(PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Tag {
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
        span: Span,
    },
    Origin(Address),
    Equality(UntaggedProgramInstruction),
    Undefined(SymbolContext),
    DefaultAssigned(Unsigned36Bit, SymbolContext),
}

impl Debug for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Origin(address) => write!(f, "Origin({address:o})"),
            SymbolDefinition::Tag {
                block_id,
                block_offset,
                span: _,
            } => {
                write!(
                    f,
                    "Tag {{block_id:{block_id:?}, block_offset:{block_offset}}}"
                )
            }
            SymbolDefinition::Equality(expr) => f.debug_tuple("Equality").field(expr).finish(),
            SymbolDefinition::DefaultAssigned(value, _) => {
                write!(f, "DefaultAssigned({value:o})")
            }
            SymbolDefinition::Undefined(context) => {
                f.debug_tuple("Undefined").field(context).finish()
            }
        }
    }
}

impl Display for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::DefaultAssigned(value, _) => {
                write!(f, "default-assigned as {value}")
            }
            SymbolDefinition::Origin(addr) => {
                write!(f, "{addr:06o}")
            }
            SymbolDefinition::Tag {
                block_id,
                block_offset,
                span: _,
            } => {
                write!(
                    f,
                    "tag at offset {block_offset} in {block_id} with unspecified address"
                )
            }
            SymbolDefinition::Equality(inst) => {
                // TODO: print the assigned value, too?
                write!(f, "assignment with value {inst:#?}")
            }
            SymbolDefinition::Undefined(_context) => f.write_str("undefined"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum BadSymbolDefinition {
    Incompatible(SymbolDefinition, SymbolDefinition),
}

impl Display for BadSymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BadSymbolDefinition::Incompatible(previous, new) => {
                write!(f, "it is not allowed to override symbol definition {previous} with a new definition {new}")
            }
        }
    }
}

impl std::error::Error for BadSymbolDefinition {}

impl SymbolDefinition {
    pub(crate) fn merge_context(&mut self, context: SymbolContext) {
        if let SymbolDefinition::Undefined(current) = self {
            match current.merge(context) {
                Ok(_) => (),
                Err(e) => {
                    panic!("cannot have an origin block number conflict if one of the merge sides has no block number: {e:?}")
                }
            }
        }
    }

    pub(crate) fn override_with(
        &mut self,
        update: SymbolDefinition,
    ) -> Result<(), BadSymbolDefinition> {
        match (self, update) {
            (current @ SymbolDefinition::Equality(_), new @ SymbolDefinition::Equality(_)) => {
                // This is always OK.
                *current = new;
                Ok(())
            }
            (current @ SymbolDefinition::Undefined(_), new) => {
                // This is always OK.
                *current = new;
                Ok(())
            }
            (current, new) => {
                if current == &new {
                    Ok(()) // nothing to do.
                } else {
                    Err(BadSymbolDefinition::Incompatible(current.clone(), new))
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct RcBlock {
    pub(crate) address: Address,
    pub(crate) words: Vec<(Span, Unsigned36Bit)>,
}

impl RcAllocator for RcBlock {
    fn allocate(&mut self, span: Span, value: Unsigned36Bit) -> Address {
        match Unsigned18Bit::try_from(self.words.len()) {
            Ok(offset) => {
                let addr = self.address.index_by(offset);
                self.words.push((span, value));
                addr
            }
            Err(_) => {
                panic!("program is too large"); // TODO: fixme: use Result
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn make_empty_rc_block_for_test(location: Address) -> RcBlock {
    RcBlock {
        address: location,
        words: Vec::new(),
    }
}
