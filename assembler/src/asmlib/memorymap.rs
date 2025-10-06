use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter};

use base::Unsigned18Bit;
use base::Unsigned36Bit;
use base::prelude::Address;
use base::prelude::IndexBy;

use super::ast::InstructionSequence;
use super::ast::Origin;
use super::ast::RcUpdater;
use super::listing::Listing;
use super::source::Source;
use super::span::{Span, Spanned};
use super::symbol::SymbolName;
use super::symtab::{
    ExplicitSymbolTable, FinalSymbolTable, ImplicitSymbolTable, IndexRegisterAssigner,
};
use super::types::AssemblerFailure;
use super::types::BlockIdentifier;
use super::types::ProgramError;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum RcWordKind {
    // Ivan Sutherland calls PipeConstruct "double addressing"
    PipeConstruct,
    Braces,
    DefaultAssignment,
}

/// Indicates why we allocated an RC-word.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RcWordSource {
    pub span: Span,
    pub kind: RcWordKind,
}

impl Spanned for RcWordSource {
    fn span(&self) -> Span {
        self.span
    }
}

impl Display for RcWordKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            RcWordKind::PipeConstruct => "pipe construct",
            RcWordKind::Braces => "RC-word",
            RcWordKind::DefaultAssignment => "default-assignment",
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum RcWordAllocationFailure {
    RcBlockTooBig {
        source: RcWordSource,
        rc_block_len: usize,
    },
    InconsistentTag {
        tag_name: SymbolName,
        span: Span,
        explanation: String,
    },
}

impl Display for RcWordAllocationFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RcWordAllocationFailure::RcBlockTooBig {
                source: RcWordSource { kind, .. },
                rc_block_len,
            } => {
                write!(
                    f,
                    "failed to allocate RC word for {kind}; RC block is already {rc_block_len} words long"
                )
            }
            RcWordAllocationFailure::InconsistentTag {
                tag_name,
                span: _,
                explanation,
            } => {
                write!(f, "failed to define tag {tag_name}: {explanation}")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BlockPosition {
    pub(super) block_identifier: BlockIdentifier,
    // span is either the span of the origin specification if there is
    // one, or otherwise the span of the first thing in the block.
    pub(super) span: Span,
    pub(super) origin: Option<Origin>,
    pub(super) block_address: Option<Address>,
    pub(super) block_size: Unsigned18Bit,
}

impl Spanned for BlockPosition {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct MemoryMap {
    blocks: Vec<BlockPosition>,
}

impl MemoryMap {
    pub(crate) fn get(&self, block: &BlockIdentifier) -> Option<&BlockPosition> {
        let pos = usize::from(*block);
        self.blocks.get(pos)
    }

    pub(crate) fn set_block_position(&mut self, block: BlockIdentifier, location: Address) {
        match self.blocks.get_mut(usize::from(block)) {
            Some(pos) => pos.block_address = Some(location),
            None => {
                unreachable!("attempted to set location of nonexistent block {block}");
            }
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &BlockPosition> {
        self.blocks.iter()
    }

    pub(crate) fn new<I>(block_sizes: I) -> MemoryMap
    where
        I: IntoIterator<Item = (Span, Option<Origin>, Unsigned18Bit)>,
    {
        let blocks = block_sizes
            .into_iter()
            .enumerate()
            .map(|(i, (span, maybe_origin, block_size))| {
                if i > 0 {
                    // The presence of an origin specification is what
                    // prompts the creation of a second or later
                    // block, so only the first block is allowed not
                    // to have an origin.
                    assert!(maybe_origin.is_some());
                }
                BlockPosition {
                    block_identifier: BlockIdentifier::from(i),
                    span,
                    origin: maybe_origin,
                    block_address: None,
                    block_size,
                }
            })
            .collect();
        MemoryMap { blocks }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocatedBlock {
    pub(crate) origin: Option<Origin>,
    pub(crate) location: Address,
    pub(crate) sequences: Vec<InstructionSequence>,
}

impl LocatedBlock {
    pub(super) fn emitted_word_count(&self) -> Unsigned18Bit {
        self.sequences
            .iter()
            .map(|seq| seq.emitted_word_count())
            .sum()
    }

    pub(super) fn following_addr(&self) -> Address {
        self.location.index_by(self.emitted_word_count())
    }

    pub(super) fn allocate_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        for seq in &mut self.sequences {
            seq.allocate_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_binary_block<R: RcUpdater>(
        &self,
        location: Address,
        explicit_symtab: &ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        memory_map: &MemoryMap,
        index_register_assigner: &mut IndexRegisterAssigner,
        rc_allocator: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &Source,
        listing: &mut Listing,
        undefined_symbols: &mut BTreeMap<SymbolName, ProgramError>,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let word_count: usize = self
            .sequences
            .iter()
            .map(|seq| usize::from(seq.emitted_word_count()))
            .sum();
        let mut result: Vec<Unsigned36Bit> = Vec::with_capacity(word_count);
        for seq in &self.sequences {
            let current_block_len: Unsigned18Bit = result
                .len()
                .try_into()
                .expect("assembled code block should fit within physical memory");
            let mut words: Vec<Unsigned36Bit> = seq.build_binary_block(
                location,
                current_block_len,
                explicit_symtab,
                implicit_symtab,
                memory_map,
                index_register_assigner,
                rc_allocator,
                final_symbols,
                body,
                listing,
                undefined_symbols,
            )?;
            result.append(&mut words);
        }
        Ok(result)
    }
}

impl Error for RcWordAllocationFailure {}

pub(crate) trait RcAllocator {
    fn allocate(
        &mut self,
        source: RcWordSource,
        value: Unsigned36Bit,
    ) -> Result<Address, RcWordAllocationFailure>;
}
