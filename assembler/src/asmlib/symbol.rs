use std::collections::BTreeSet;
use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::hash::{Hash, Hasher};

use base::charset::Script;

use super::ast::Origin;
use super::span::Spanned;
use super::span::{OrderableSpan, Span};
use super::types::BlockIdentifier;

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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum ConfigOrIndexUsage {
    Configuration,
    Index,
    ConfigurationAndIndex,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum InconsistentSymbolUse {
    ConflictingOrigin(
        SymbolName,
        Box<Origin>,
        BlockIdentifier,
        Box<Origin>,
        BlockIdentifier,
    ),
    MixingOrigin(SymbolName, Box<Origin>, ConfigOrIndexUsage),
}

impl Spanned for InconsistentSymbolUse {
    fn span(&self) -> Span {
        match self {
            InconsistentSymbolUse::ConflictingOrigin(_, _origin1, _, origin2, _) => origin2.span(),
            InconsistentSymbolUse::MixingOrigin(_, origin, _) => origin.span(),
        }
    }
}

impl Display for InconsistentSymbolUse {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            InconsistentSymbolUse::ConflictingOrigin(
                name,
                _origin_1,
                block_identifier_1,
                _origin_2,
                block_identifier_2,
            ) => {
                write!(f, "symbol {name} cannot simultaneously be the origin for {block_identifier_1} and {block_identifier_2}; names must be unique")
            }
            InconsistentSymbolUse::MixingOrigin(name, _origin, _incompatibility) => {
                write!(f, "symbols (in this case {name}) cannot be used as an origin name and a configuration or index value")
            }
        }
    }
}

impl Error for InconsistentSymbolUse {}

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub(crate) enum ConfigUse {
    #[default]
    NotConfig,
    IncludesConfig,
}

impl ConfigUse {
    fn or(&self, other: &ConfigUse) -> ConfigUse {
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
    fn or(&self, other: &IndexUse) -> IndexUse {
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
    fn or(&self, other: &AddressUse) -> AddressUse {
        match (self, other) {
            (AddressUse::IncludesAddress, _) | (_, AddressUse::IncludesAddress) => {
                AddressUse::IncludesAddress
            }
            _ => AddressUse::NotAddress,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum OriginUse {
    /// Use of a symbol in configuration or index context prohibits
    /// use in an origin context.
    NotOrigin { config: ConfigUse, index: IndexUse },
    /// Use of a symbol in origin context prohibits use in
    /// configuration or index context.
    IncludesOrigin(BlockIdentifier, Origin),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct SymbolContext {
    pub(super) address: AddressUse,
    pub(super) origin: OriginUse,
    pub(super) uses: BTreeSet<OrderableSpan>, // Span does not implement Hash
}

impl SymbolContext {
    fn check_invariants(&self) {
        assert!(!self.uses.is_empty());
    }

    fn check_invariants_passthrough(self) -> SymbolContext {
        self.check_invariants();
        self
    }

    pub(crate) fn configuration(span: Span) -> SymbolContext {
        SymbolContext {
            address: AddressUse::NotAddress,
            origin: OriginUse::NotOrigin {
                config: ConfigUse::IncludesConfig,
                index: IndexUse::NotIndex,
            },
            uses: SymbolContext::uses(span),
        }
        .check_invariants_passthrough()
    }

    pub(crate) fn also_set_index(
        &mut self,
        name: &SymbolName,
        span: Span,
    ) -> Result<(), InconsistentSymbolUse> {
        match &mut self.origin {
            OriginUse::IncludesOrigin(_block_identifier, origin) => {
                Err(InconsistentSymbolUse::MixingOrigin(
                    name.clone(),
                    Box::new(origin.clone()),
                    ConfigOrIndexUsage::Index,
                ))
            }
            OriginUse::NotOrigin { index, .. } => {
                *index = IndexUse::IncludesIndex;
                self.uses.insert(OrderableSpan(span));
                Ok(())
            }
        }
    }

    pub(crate) fn is_address(&self) -> bool {
        self.address == AddressUse::IncludesAddress
    }

    pub(crate) fn get_origin(&self) -> Option<(&BlockIdentifier, &Origin)> {
        match self.origin {
            OriginUse::IncludesOrigin(ref block_identifier, ref origin) => {
                Some((block_identifier, origin))
            }
            OriginUse::NotOrigin { .. } => None,
        }
    }

    fn uses(span: Span) -> BTreeSet<OrderableSpan> {
        [OrderableSpan(span)].into_iter().collect()
    }

    pub(crate) fn origin(block_id: BlockIdentifier, origin: Origin) -> SymbolContext {
        let span = origin.span();
        SymbolContext {
            address: AddressUse::NotAddress,
            origin: OriginUse::IncludesOrigin(block_id, origin),
            uses: SymbolContext::uses(span),
        }
        .check_invariants_passthrough()
    }

    pub(crate) fn merge(
        &mut self,
        name: &SymbolName,
        mut other: SymbolContext,
    ) -> Result<(), InconsistentSymbolUse> {
        fn mix_err(
            name: &SymbolName,
            origin: Origin,
            _block_id: BlockIdentifier,
            configuration: ConfigUse,
            index: IndexUse,
        ) -> InconsistentSymbolUse {
            let incompatiblity: ConfigOrIndexUsage = match (configuration, index) {
                (ConfigUse::IncludesConfig, IndexUse::IncludesIndex) => {
                    ConfigOrIndexUsage::ConfigurationAndIndex
                }
                (ConfigUse::IncludesConfig, IndexUse::NotIndex) => {
                    ConfigOrIndexUsage::Configuration
                }
                (ConfigUse::NotConfig, IndexUse::IncludesIndex) => ConfigOrIndexUsage::Index,
                (ConfigUse::NotConfig, IndexUse::NotIndex) => {
                    unreachable!("enclosing match already eliminated this case")
                }
            };
            InconsistentSymbolUse::MixingOrigin(name.clone(), Box::new(origin), incompatiblity)
        }

        let origin: OriginUse = match (&self.origin, &other.origin) {
            (
                OriginUse::NotOrigin {
                    config: my_config_use,
                    index: my_index_use,
                },
                OriginUse::NotOrigin {
                    config: their_config_use,
                    index: their_index_use,
                },
            ) => OriginUse::NotOrigin {
                config: my_config_use.or(their_config_use),
                index: my_index_use.or(their_index_use),
            },
            (
                OriginUse::IncludesOrigin(my_block, my_origin),
                OriginUse::IncludesOrigin(their_block, their_origin),
            ) => {
                if my_block == their_block && my_origin.has_same_specification(their_origin) {
                    // If one of the origins is a deduced origin, that
                    // has more information, so retain that one.
                    //
                    // We merge symbol usage information from deduced
                    // origins because we specifically call
                    // record_deduced_origin_value() in order to do
                    // this.
                    let chosen: &Origin = match (&my_origin, &their_origin) {
                        (deduced @ Origin::Deduced(_, _, _), _)
                        | (_, deduced @ Origin::Deduced(_, _, _)) => deduced,
                        _ => my_origin,
                    };
                    OriginUse::IncludesOrigin(*my_block, chosen.clone())
                } else {
                    return Err(InconsistentSymbolUse::ConflictingOrigin(
                        name.clone(),
                        Box::new(my_origin.clone()),
                        *my_block,
                        Box::new(their_origin.clone()),
                        *their_block,
                    ));
                }
            }
            (
                OriginUse::IncludesOrigin(my_block, my_origin),
                OriginUse::NotOrigin {
                    config: their_config,
                    index: their_index,
                },
            ) => {
                return Err(mix_err(
                    name,
                    my_origin.clone(),
                    *my_block,
                    *their_config,
                    *their_index,
                ));
            }
            (
                OriginUse::NotOrigin {
                    config: my_config,
                    index: my_index,
                },
                OriginUse::IncludesOrigin(their_block, their_origin),
            ) => {
                return Err(mix_err(
                    name,
                    their_origin.clone(),
                    *their_block,
                    *my_config,
                    *my_index,
                ));
            }
        };
        let result = SymbolContext {
            address: self.address.or(&other.address),
            origin,
            uses: {
                let mut u = BTreeSet::new();
                u.append(&mut self.uses);
                u.append(&mut other.uses);
                u
            },
        };
        result.check_invariants();
        *self = result;
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

#[test]
fn test_deduced_origin_merge() {
    use super::span::span;
    use base::prelude::Address;
    use base::u18;
    let span = span(0..4);
    let block = BlockIdentifier::from(0);
    let name = SymbolName::from("OGN");
    let address = Address::from(u18!(0o200_000));
    let mut current = SymbolContext::origin(block, Origin::Symbolic(span, name.clone()));
    let new_use = SymbolContext::origin(block, Origin::Deduced(span, name.clone(), address));
    assert_eq!(current.merge(&name, new_use.clone()), Ok(()));
    assert_eq!(current, new_use);
}

impl From<(&Script, Span)> for SymbolContext {
    fn from((elevation, span): (&Script, Span)) -> SymbolContext {
        let (config, index, address) = match elevation {
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
            address,
            origin: OriginUse::NotOrigin { config, index },
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
