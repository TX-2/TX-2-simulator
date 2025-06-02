use std::collections::BTreeSet;
use std::error::Error;
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
    ConflictingOrigin(SymbolName, BlockIdentifier, BlockIdentifier),
}

impl Display for SymbolContextMergeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolContextMergeError::ConflictingOrigin(
                name,
                block_identifier_1,
                block_identifier_2,
            ) => {
                write!(f, "symbol {} cannot simultaneously be the origin for block {} and block {}; names must be unique",
                       name, block_identifier_1, block_identifier_2)
            }
        }
    }
}

impl Error for SymbolContextMergeError {}

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub(crate) enum ConfigUse {
    #[default]
    NotConfig,
    IncludesConfig,
}

impl ConfigUse {
    fn or(&self, other: ConfigUse) -> ConfigUse {
        match (self, other) {
            (ConfigUse::IncludesConfig, _) | (_, ConfigUse::IncludesConfig) => {
                ConfigUse::IncludesConfig
            }
            _ => ConfigUse::NotConfig,
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub(crate) enum IndexUse {
    #[default]
    NotIndex,
    IncludesIndex,
}

impl IndexUse {
    fn or(&self, other: IndexUse) -> IndexUse {
        match (self, other) {
            (IndexUse::IncludesIndex, _) | (_, IndexUse::IncludesIndex) => IndexUse::IncludesIndex,
            _ => IndexUse::NotIndex,
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub(crate) enum AddressUse {
    #[default]
    NotAddress,
    IncludesAddress,
}

impl AddressUse {
    fn or(&self, other: AddressUse) -> AddressUse {
        match (self, other) {
            (AddressUse::IncludesAddress, _) | (_, AddressUse::IncludesAddress) => {
                AddressUse::IncludesAddress
            }
            _ => AddressUse::NotAddress,
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub(crate) enum OriginUse {
    #[default]
    NotOrigin,
    IncludesOrigin,
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub(crate) struct SymbolContext {
    // The "All members are false" context is the one in which we list
    // the values of symbols in the program listing.
    configuration: ConfigUse,
    index: IndexUse,
    address: AddressUse,
    pub(super) origin_of_block: Option<BlockIdentifier>,
    uses: BTreeSet<OrderableSpan>, // Span does not implement Hash
}

impl SymbolContext {
    fn check_invariants(&self) {
        assert!(!self.uses.is_empty());
    }

    fn check_invariants_passthrough(self) -> SymbolContext {
        self.check_invariants();
        self
    }

    pub(crate) fn parts(&self) -> (ConfigUse, IndexUse, AddressUse, OriginUse) {
        use OriginUse::*;
        (
            self.configuration,
            self.index,
            self.address,
            if self.origin_of_block.is_some() {
                IncludesOrigin
            } else {
                NotOrigin
            },
        )
    }

    pub(crate) fn configuration(span: Span) -> SymbolContext {
        SymbolContext {
            configuration: ConfigUse::IncludesConfig,
            uses: SymbolContext::uses(span),
            ..Default::default()
        }
        .check_invariants_passthrough()
    }

    pub(crate) fn also_set_index(&mut self) {
        self.index = IndexUse::IncludesIndex;
    }

    pub(crate) fn is_address(&self) -> bool {
        self.address == AddressUse::IncludesAddress
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
        .check_invariants_passthrough()
    }

    pub(crate) fn merge(
        &mut self,
        name: &SymbolName,
        mut other: SymbolContext,
    ) -> Result<(), SymbolContextMergeError> {
        let origin = match (self.origin_of_block, other.origin_of_block) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x),
            (Some(x), Some(y)) => {
                if x == y {
                    Some(x)
                } else {
                    return Err(SymbolContextMergeError::ConflictingOrigin(
                        name.clone(),
                        x,
                        y,
                    ));
                }
            }
        };
        let result = SymbolContext {
            configuration: self.configuration.or(other.configuration),
            index: self.index.or(other.index),
            address: self.address.or(other.address),
            origin_of_block: origin,
            uses: {
                let mut u = BTreeSet::new();
                u.append(&mut self.uses);
                u.append(&mut other.uses);
                u
            },
        };
        *self = result;
        self.check_invariants();
        Ok(())
    }

    pub(super) fn requires_rc_word_allocation(&self) -> bool {
        self.address == AddressUse::IncludesAddress
    }

    pub(super) fn any_span(&self) -> &Span {
        match self.uses.first() {
            Some(orderable_span) => orderable_span.as_span(),
            None => {
                panic!("invariant broken in SymbolContext::any_span(): SymbolContext contains empty uses");
            }
        }
    }
}

impl From<(&Script, Span)> for SymbolContext {
    fn from((elevation, span): (&Script, Span)) -> SymbolContext {
        let (configuration, index, address) = match elevation {
            Script::Super => (
                ConfigUse::IncludesConfig,
                IndexUse::NotIndex,
                AddressUse::NotAddress,
            ),
            Script::Sub => (
                ConfigUse::NotConfig,
                IndexUse::IncludesIndex,
                AddressUse::NotAddress,
            ),
            Script::Normal => (
                ConfigUse::NotConfig,
                IndexUse::NotIndex,
                AddressUse::IncludesAddress,
            ),
        };
        SymbolContext {
            configuration,
            index,
            address,
            origin_of_block: None,
            uses: SymbolContext::uses(span),
        }
        .check_invariants_passthrough()
    }
}

impl From<(Script, Span)> for SymbolContext {
    fn from((elevation, span): (Script, Span)) -> SymbolContext {
        SymbolContext::from((&elevation, span)).check_invariants_passthrough()
    }
}
