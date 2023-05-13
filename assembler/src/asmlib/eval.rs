use std::fmt::{self, Debug, Display, Formatter};

use base::{charset::Script, prelude::Unsigned36Bit};

use super::ast::Expression;
use super::symbol::SymbolName;

pub(crate) trait SymbolLookup {
    type Error;
    fn lookup(
        &mut self,
        name: &SymbolName,
        context: &SymbolContext,
    ) -> Result<Unsigned36Bit, Self::Error>;
}

pub(crate) trait Evaluate {
    fn evaluate<S: SymbolLookup>(&self, symtab: &mut S) -> Result<Unsigned36Bit, S::Error>;
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolUse {
    Reference(SymbolContext),
    Definition(SymbolDefinition),
    Origin(SymbolName, usize),
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum SymbolContextMergeError {
    ConflictingOrigin(usize, usize),
}

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
pub(crate) struct SymbolContext {
    // The "All members are false" context is the one in which we list
    // the values of symbols in the program listing.
    configuration: bool,
    index: bool,
    address: bool,
    origin_of_block: Option<usize>,
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

    pub(crate) fn origin(block_number: usize) -> SymbolContext {
        SymbolContext {
            origin_of_block: Some(block_number),
            ..Default::default()
        }
    }

    pub(crate) fn includes(&self, other: &SymbolContext) -> bool {
        other
            .bits()
            .into_iter()
            .zip(self.bits().into_iter())
            .all(|(otherbit, selfbit)| selfbit || !otherbit)
    }

    fn merge(&mut self, other: SymbolContext) -> Result<SymbolContext, SymbolContextMergeError> {
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
        };
        *self = result;
        Ok(result)
    }
}

impl From<&Script> for SymbolContext {
    fn from(elevation: &Script) -> SymbolContext {
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
        }
    }
}

impl From<Script> for SymbolContext {
    fn from(elevation: Script) -> SymbolContext {
        SymbolContext::from(&elevation)
    }
}

#[derive(PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Tag { block: usize, offset: usize },
    Equality(Expression),
    Undefined(SymbolContext),
    DefaultAssigned(Unsigned36Bit),
}

impl Debug for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Tag { block, offset } => {
                write!(f, "Tag {{block:{block}, offset:{offset}}}")
            }
            SymbolDefinition::Equality(expr) => f.debug_tuple("Equality").field(expr).finish(),
            SymbolDefinition::DefaultAssigned(value) => {
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
            SymbolDefinition::DefaultAssigned(value) => {
                write!(f, "default-assigned as {value}")
            }
            SymbolDefinition::Tag { block, offset } => {
                write!(f, "tag at offset {offset} in block {block}")
            }
            SymbolDefinition::Equality(expression) => {
                write!(f, "assignment with value {expression}")
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
