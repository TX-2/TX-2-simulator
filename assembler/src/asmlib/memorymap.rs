use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter};

use base::prelude::Address;
use base::prelude::IndexBy;
use base::Unsigned18Bit;
use base::Unsigned36Bit;

use super::ast::InstructionSequence;
use super::ast::Origin;
use super::ast::RcUpdater;
use super::listing::Listing;
use super::span::{Span, Spanned};
use super::symbol::SymbolName;
use super::symtab::{
    ExplicitDefinition, ExplicitSymbolTable, FinalSymbolTable, ImplicitSymbolTable,
    IndexRegisterAssigner, TagDefinition,
};
use super::types::AssemblerFailure;
use super::types::BlockIdentifier;
use super::types::ProgramError;

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum RcWordAllocationFailure {
    RcBlockTooBig {
        source: RcWordSource,
        rc_block_len: usize,
    },
    InconsistentTag {
        tag_name: SymbolName,
        span: Span,
        existing: Box<ExplicitDefinition>,
        proposed: Box<TagDefinition>,
    },
}

impl Display for RcWordAllocationFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RcWordAllocationFailure::RcBlockTooBig {
                source,
                rc_block_len,
            } => {
                write!(f, "failed to allocate RC word for {source}; RC block is already {rc_block_len} words long")
            }
            RcWordAllocationFailure::InconsistentTag {
                tag_name,
                span: _,
                existing,
                proposed,
            } => {
                write!(
                    f,
                    "failed to define tag {tag_name} because it already had a previous definition: {existing} versus {proposed}"
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BlockPosition {
    // span is either the span of the origin specification if there is
    // one, or otherwise the span of the first thing in the block.
    pub(super) span: Span,
    pub(super) origin: Option<Origin>,
    pub(super) block_address: Option<Address>,
    pub(super) block_size: Unsigned18Bit,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct MemoryMap {
    blocks: BTreeMap<BlockIdentifier, BlockPosition>,
}

impl MemoryMap {
    pub(crate) fn get(&self, block: &BlockIdentifier) -> Option<&BlockPosition> {
        self.blocks.get(block)
    }

    pub(crate) fn set_block_position(&mut self, block: BlockIdentifier, location: Address) {
        match self.blocks.get_mut(&block) {
            Some(pos) => pos.block_address = Some(location),
            None => {
                unreachable!("attempted to set location of nonexistent block");
            }
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&BlockIdentifier, &BlockPosition)> {
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
                let block_id = BlockIdentifier::from(i);
                (
                    block_id,
                    BlockPosition {
                        span,
                        origin: maybe_origin,
                        block_address: None,
                        block_size,
                    },
                )
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
        for seq in self.sequences.iter_mut() {
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
        body: &str,
        listing: &mut Listing,
        undefined_symbols: &mut BTreeMap<SymbolName, ProgramError>,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let word_count: usize = self
            .sequences
            .iter()
            .map(|seq| usize::from(seq.emitted_word_count()))
            .sum();
        let mut result: Vec<Unsigned36Bit> = Vec::with_capacity(word_count);
        for seq in self.sequences.iter() {
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
