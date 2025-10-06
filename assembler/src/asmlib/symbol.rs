use std::collections::BTreeSet;
use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};

use base::charset::Script;

use super::ast::Origin;
use super::span::Spanned;
#[cfg(test)]
use super::span::span;
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
        self.canonical.hash(state);
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
    ConflictingOrigin {
        name: SymbolName,
        first: (Span, BlockIdentifier),
        second: (Span, BlockIdentifier),
    },
    MixingOrigin(SymbolName, Span, ConfigOrIndexUsage),
}

impl Spanned for InconsistentSymbolUse {
    fn span(&self) -> Span {
        match self {
            InconsistentSymbolUse::ConflictingOrigin {
                name: _,
                first: _,
                second: (origin2_span, _),
            } => *origin2_span,
            InconsistentSymbolUse::MixingOrigin(_, span, _) => *span,
        }
    }
}

impl Display for InconsistentSymbolUse {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            InconsistentSymbolUse::ConflictingOrigin {
                name,
                first: (_, block_identifier_1),
                second: (_, block_identifier_2),
            } => {
                write!(
                    f,
                    "symbol {name} cannot simultaneously be the origin for {block_identifier_1} and {block_identifier_2}; names must be unique"
                )
            }
            InconsistentSymbolUse::MixingOrigin(name, _, incompatibility) => {
                let what: &'static str = match incompatibility {
                    ConfigOrIndexUsage::Configuration => {
                        "a configuration value (though using it as an index value would also be incorrect)"
                    }
                    ConfigOrIndexUsage::Index => {
                        "an index value (though using it as a configuration value would also be incorrect)"
                    }
                    ConfigOrIndexUsage::ConfigurationAndIndex => {
                        "a configuration or index value (though in this case it was used as both)"
                    }
                };
                write!(f, "symbols (in this case {name}) cannot be used as {what}")
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
            (AddressUse::NotAddress, AddressUse::NotAddress) => AddressUse::NotAddress,
            _ => AddressUse::IncludesAddress,
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
                    origin.span(),
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
            // All origins are (implicitly) uses of the symbol as an
            // address.
            address: AddressUse::IncludesAddress,
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
            InconsistentSymbolUse::MixingOrigin(name.clone(), origin.span(), incompatiblity)
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
                if my_block == their_block {
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
                    return Err(InconsistentSymbolUse::ConflictingOrigin {
                        name: name.clone(),
                        first: (my_origin.span(), *my_block),
                        second: (their_origin.span(), *their_block),
                    });
                }
            }
            (
                OriginUse::IncludesOrigin(my_block, my_origin),
                OriginUse::NotOrigin { config, index },
            ) => {
                if config == &ConfigUse::IncludesConfig || index == &IndexUse::IncludesIndex {
                    return Err(mix_err(name, my_origin.clone(), *my_block, *config, *index));
                } else {
                    OriginUse::IncludesOrigin(*my_block, my_origin.clone())
                }
            }
            (
                OriginUse::NotOrigin { config, index },
                OriginUse::IncludesOrigin(their_block, their_origin),
            ) => {
                if config == &ConfigUse::IncludesConfig || index == &IndexUse::IncludesIndex {
                    return Err(mix_err(
                        name,
                        their_origin.clone(),
                        *their_block,
                        *config,
                        *index,
                    ));
                } else {
                    OriginUse::IncludesOrigin(*their_block, their_origin.clone())
                }
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
        if self.address == AddressUse::IncludesAddress {
            if matches!(&self.origin, &OriginUse::IncludesOrigin(_, _)) {
                // This symbol is used in address contexts, but it is
                // the name used for an origin.  Therefore we do not
                // need to allocate an RC-word for it.
                false
            } else {
                // This name is used in an address context but it is
                // not the name of an origin, so when there is no tag
                // definition for it, we will need to allocate an
                // RC-word for it.
                true
            }
        } else {
            // Since nothing expects this symbol to refer to an
            // address, there is no need to allocate an RC-word.
            false
        }
    }

    pub(super) fn any_span(&self) -> &Span {
        match self.uses.first() {
            Some(orderable_span) => orderable_span.as_span(),
            None => {
                panic!(
                    "invariant broken in SymbolContext::any_span(): SymbolContext contains empty uses"
                );
            }
        }
    }
}

#[test]
fn test_origin_can_be_used_as_address() {
    // Given a symbol usage as an origin name
    let name = SymbolName::from("BEGIN");
    let make_origin_context = || {
        SymbolContext::origin(
            BlockIdentifier::from(0),
            Origin::Symbolic(span(10..15), name.clone()),
        )
    };
    // And a symbol usage in an address context.
    let make_address_context = || SymbolContext {
        address: AddressUse::IncludesAddress,
        origin: OriginUse::NotOrigin {
            config: ConfigUse::NotConfig,
            index: IndexUse::NotIndex,
        },
        uses: SymbolContext::uses(span(20..25)),
    };

    // When we merge these two uses of the same symbol, this should
    // succeed.
    let mut fwd = make_origin_context();
    assert_eq!(fwd.merge(&name, make_address_context()), Ok(()));

    let mut rev = make_address_context();
    assert_eq!(rev.merge(&name, make_origin_context()), Ok(()));

    // We should get the same result in either case.
    assert_eq!(fwd, rev);
}

#[test]
fn test_origin_cannot_be_used_as_an_index_value() {
    // Given a symbol usage as an origin name
    let name = SymbolName::from("BEGIN");
    let make_origin_context = || {
        SymbolContext::origin(
            BlockIdentifier::from(0),
            Origin::Symbolic(span(10..15), name.clone()),
        )
    };
    // And a symbol usage in an index context.
    let make_index_context = || SymbolContext {
        address: AddressUse::NotAddress,
        origin: OriginUse::NotOrigin {
            config: ConfigUse::NotConfig,
            index: IndexUse::IncludesIndex,
        },
        uses: SymbolContext::uses(span(20..25)),
    };

    // When we merge these two uses of the same symbol, this should
    // fail (as this combination is not allowed)
    let expected_msg = "symbols (in this case BEGIN) cannot be used as an index value (though using it as a configuration value would also be incorrect)";
    let mut fwd = make_origin_context();
    match fwd.merge(&name, make_index_context()) {
        Ok(()) => {
            panic!(
                "failed to detect incompatibility in the use of a symbol as both origin and index"
            );
        }
        Err(e) => {
            assert_eq!(e.to_string(), expected_msg);
        }
    }

    let mut rev = make_index_context();
    match rev.merge(&name, make_origin_context()) {
        Ok(()) => {
            panic!(
                "failed to detect incompatibility in the use of a symbol as both origin and index"
            );
        }
        Err(e) => {
            assert_eq!(e.to_string(), expected_msg);
        }
    }
}

#[test]
fn test_origin_cannot_be_used_as_a_configuration_value() {
    // Given a symbol usage as an origin name
    let name = SymbolName::from("BEGIN");
    let make_origin_context = || {
        SymbolContext::origin(
            BlockIdentifier::from(0),
            Origin::Symbolic(span(10..15), name.clone()),
        )
    };
    // And a symbol usage in a configuration context.
    let make_configuration_context = || SymbolContext {
        address: AddressUse::NotAddress,
        origin: OriginUse::NotOrigin {
            config: ConfigUse::IncludesConfig,
            index: IndexUse::NotIndex,
        },
        uses: SymbolContext::uses(span(20..25)),
    };

    // When we merge these two uses of the same symbol, this should
    // fail (as this combination is not allowed)
    let expected_msg = "symbols (in this case BEGIN) cannot be used as a configuration value (though using it as an index value would also be incorrect)";
    let mut fwd = make_origin_context();
    match fwd.merge(&name, make_configuration_context()) {
        Ok(()) => {
            panic!(
                "failed to detect incompatibility in the use of a symbol as both origin and index"
            );
        }
        Err(e) => {
            assert_eq!(e.to_string(), expected_msg);
        }
    }

    let mut rev = make_configuration_context();
    match rev.merge(&name, make_origin_context()) {
        Ok(()) => {
            panic!(
                "failed to detect incompatibility in the use of a symbol as both origin and configuration value"
            );
        }
        Err(e) => {
            assert_eq!(e.to_string(), expected_msg);
        }
    }
}

#[test]
fn test_deduced_origin_merge() {
    struct Contexts {
        reference: SymbolContext,
        origin_definition: SymbolContext,
        expected_merge: SymbolContext,
    }
    // Convenience function for creating the test input and expected output.
    fn make_symbolic_and_deduced_origin_contexts(
        name: SymbolName,
        is_forward_reference: bool,
    ) -> Contexts {
        let block = BlockIdentifier::from(0);

        let deduced_origin_span: Span = span(1000..1010);
        let symbol_span = if is_forward_reference {
            // The reference appears before the origin specification
            span(10..20)
        } else {
            // The reference appears after the origin specification
            span(2000..2020)
        };

        // In our examples, the deduced origin value is a
        // symbolically-defined origin to which we would deduced
        // address (from the locations and sizes of the blocks
        // preceding it).
        let deduced_origin_context = SymbolContext {
            address: AddressUse::IncludesAddress,
            origin: OriginUse::IncludesOrigin(
                block,
                Origin::Symbolic(deduced_origin_span, name.clone()),
            ),
            uses: SymbolContext::uses(deduced_origin_span),
        };

        // The symbolic context is is simply a reference to the
        // origin, either preceding (is_forward_reference) or
        // following (!is_forward_reference) the definition of the
        // origin.
        let reference_context = SymbolContext {
            address: AddressUse::IncludesAddress,
            // Although this use of the symbol will turn out to be a
            // reference to an origin, we cannot tell that at the
            // reference site, and so the context in which this symbol
            // is used at that point is not an origin context.
            origin: OriginUse::NotOrigin {
                config: ConfigUse::NotConfig,
                index: IndexUse::NotIndex,
            },
            uses: SymbolContext::uses(symbol_span),
        };

        Contexts {
            reference: reference_context,
            origin_definition: deduced_origin_context,
            expected_merge: SymbolContext {
                address: AddressUse::IncludesAddress,
                origin: OriginUse::IncludesOrigin(
                    BlockIdentifier::from(0),
                    Origin::Symbolic(deduced_origin_span, name.clone()),
                ),
                uses: [
                    OrderableSpan(deduced_origin_span),
                    OrderableSpan(symbol_span),
                ]
                .into_iter()
                .collect(),
            },
        }
    }
    let name = SymbolName::from("OGNX");
    // Set up contexts for the forward-reference and the backward-reference cases.
    let contexts_backward_ref = make_symbolic_and_deduced_origin_contexts(name.clone(), false);
    let contexts_forward_ref = make_symbolic_and_deduced_origin_contexts(name.clone(), true);
    // The value in expected_merge is not the same in each case, since
    // although the span of the origin definition is fixed, the span
    // of the reference to it is different for the forward-reference
    // and backward-reference cases.

    // Merge for the defined-then-used direction (where we encouter
    // the origin defintiion and later a reference to it).
    let mut current = contexts_backward_ref.origin_definition.clone();
    assert_eq!(
        current.merge(&name, contexts_backward_ref.reference.clone()),
        Ok(())
    );
    assert_eq!(current, contexts_backward_ref.expected_merge);

    // Merge in forward-reference direction (where we find a reference
    // to the origin address of a block before we have seen the origin
    // definition of that block).
    //
    let mut current = contexts_forward_ref.reference.clone(); // we find the fwd ref first
    assert_eq!(
        current.merge(&name, contexts_forward_ref.origin_definition.clone()),
        Ok(())
    );
    assert_eq!(current, contexts_forward_ref.expected_merge);
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
