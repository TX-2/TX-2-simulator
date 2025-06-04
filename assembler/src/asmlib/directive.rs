use std::collections::BTreeMap;

use base::prelude::Address;

use super::ast::Equality;
use super::ast::Origin;
use super::memorymap::LocatedBlock;
use super::types::BlockIdentifier;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Directive {
    // items must be in manuscript order, because RC block addresses
    // are assigned in the order they appear in the code, and
    // similarly for undefined origins (e.g. "FOO| JMP ..." where FOO
    // has no definition).
    pub(crate) blocks: BTreeMap<BlockIdentifier, LocatedBlock>,
    pub(crate) equalities: Vec<Equality>,
    pub(crate) entry_point: Option<Address>,
}

impl Directive {
    pub(crate) fn new(
        blocks: BTreeMap<BlockIdentifier, LocatedBlock>,
        equalities: Vec<Equality>,
        entry_point: Option<Address>,
    ) -> Self {
        Self {
            blocks,
            equalities,
            entry_point,
        }
    }

    pub(super) fn position_rc_block(&mut self) -> Address {
        self.blocks
            .values()
            .map(|block| block.following_addr())
            .max()
            .unwrap_or_else(Origin::default_address)
    }

    pub(crate) fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }
}
