use std::collections::BTreeMap;

use base::prelude::Address;

use super::ast::Equality;
use super::ast::Origin;
use super::memorymap::LocatedBlock;
use super::types::BlockIdentifier;

/// The `Directive` is the abstract syntax representation of the
/// user's program (i.e. the assembler's input).  A `Directive` is
/// generated (from a [`super::manuscript::SourceFile`] instance) by
/// the assembler once it has deduced the absolute address at which
/// each block will be located.
///
/// Symbolic information is included in the equalities table, but also
/// within the blocks of the program itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Directive {
    // items must be in manuscript order, because RC block addresses
    // are assigned in the order they appear in the code, and
    // similarly for undefined origins (e.g. "FOO| JMP ..." where FOO
    // has no definition).
    pub(crate) blocks: BTreeMap<BlockIdentifier, LocatedBlock>,

    /// Equalities (we use the term from the [TX-2 Users
    /// Handbook](https://archive.org/details/tx-2-users-handbook-nov-63/page/n157/mode/1up)).
    /// In more modern terminology, these would be assignments.  An
    /// equality can be re-assigned, and the last value assigned takes
    /// effect everywhere in the program.
    ///
    ///
    /// When evaluated, however, the value of an equality can vary in
    /// different places, because it can refer to local tags (which
    /// may be dfefined differently inside macro bodies) or (directly
    /// or indirectly) to `#` which is the address of the word
    /// currently being assembled.
    pub(crate) equalities: Vec<Equality>,

    /// The address at which execution should begin, as specified by
    /// the `☛☛PUNCH` meta-command, if one was given.  See [Users
    /// Handbook, section
    /// 6-3.4](https://archive.org/details/tx-2-users-handbook-nov-63/page/n175/mode/1up)
    /// and [`super::manuscript::ManuscriptMetaCommand::Punch`].
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

    /// Determine the address of the RC-block.
    ///
    /// The real TX-2 assembler ("M4") allowed the program optionally
    /// to select a location using the[`☛☛RC` meta
    /// command](https://archive.org/details/tx-2-users-handbook-nov-63/page/n176/mode/1up),
    /// but this is not yet supported.
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
