use std::collections::BTreeSet;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::hash::{Hash, Hasher};

use base::charset::Script;

use super::span::Span;
use super::types::{BlockIdentifier, OrderableSpan};

#[derive(Clone, Eq, PartialOrd, Ord)]
pub struct SymbolName {
    pub(crate) canonical: String,
    // pub(crate) as_used: String,
}

impl From<String> for SymbolName {
    fn from(s: String) -> SymbolName {
        SymbolName { canonical: s }
    }
}

impl From<&str> for SymbolName {
    fn from(s: &str) -> SymbolName {
        SymbolName::from(s.to_string())
    }
}

impl Display for SymbolName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.canonical, f)
    }
}

impl Debug for SymbolName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "SymbolName {{ canonical: \"{}\" }}", self.canonical)
    }
}

impl PartialEq for SymbolName {
    fn eq(&self, other: &SymbolName) -> bool {
        self.canonical.eq(&other.canonical)
    }
}

impl Hash for SymbolName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical.hash(state)
    }
}

#[derive(Clone, Eq, PartialOrd, Ord, PartialEq, Debug)]
pub(crate) enum SymbolOrHere {
    Named(SymbolName),
    Here,
}

impl From<&str> for SymbolOrHere {
    fn from(value: &str) -> Self {
        match value {
            "#" => SymbolOrHere::Here,
            name => SymbolOrHere::Named(SymbolName {
                canonical: name.to_owned(),
            }),
        }
    }
}

impl Display for SymbolOrHere {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolOrHere::Named(name) => write!(f, "{name}"),
            SymbolOrHere::Here => f.write_char('#'),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolContextMergeError {
    ConflictingOrigin(BlockIdentifier, BlockIdentifier),
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub(crate) struct SymbolContext {
    // The "All members are false" context is the one in which we list
    // the values of symbols in the program listing.
    configuration: bool,
    index: bool,
    address: bool,
    pub(super) origin_of_block: Option<BlockIdentifier>,
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

    pub(crate) fn merge(
        &mut self,
        mut other: SymbolContext,
    ) -> Result<(), SymbolContextMergeError> {
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

    pub(super) fn requires_rc_word_allocation(&self) -> bool {
        self.address
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
