use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::prelude::*;
use base::subword;

use super::ast::{EqualityValue, Origin, RcAllocator, RcUpdater, RcWordAllocationFailure};
use super::eval::{Evaluate, EvaluationContext, SymbolLookupFailure};
use super::span::*;
use super::symbol::{SymbolContext, SymbolName};
use super::types::{
    offset_from_origin, BlockIdentifier, MachineLimitExceededFailure, RcWordSource,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BlockPosition {
    // span is either the span of the origin specification if there is
    // one, or otherwise the span of the first thing in the block.
    pub(super) span: Span,
    pub(super) origin: Option<Origin>,
    pub(super) block_address: Option<Address>,
    pub(super) block_size: Unsigned18Bit,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct InternalSymbolDef {
    // Where the definition exists
    span: Span,
    // What the definition is.
    def: SymbolDefinition,
}

impl From<(SymbolDefinition, Span)> for InternalSymbolDef {
    fn from((def, span): (SymbolDefinition, Span)) -> InternalSymbolDef {
        InternalSymbolDef { def, span }
    }
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

#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct IndexRegisterAssigner {
    index_registers_used: Unsigned6Bit,
}

impl IndexRegisterAssigner {
    pub(crate) fn assign_index_register(&mut self) -> Option<Unsigned6Bit> {
        // These start at 0, but we can't assign X0 (since it is
        // always zero), and this is why we increment
        // `index_registers_used` first.
        if let Some(n) = self.index_registers_used.checked_add(u6!(1)) {
            self.index_registers_used = n;
            Some(n)
        } else {
            None
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.index_registers_used == 0
    }
}

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct SymbolTable {
    definitions: BTreeMap<SymbolName, InternalSymbolDef>,
}

#[derive(Debug, Default)]
pub(crate) struct LookupOperation {
    pub(super) depends_on: HashSet<SymbolName>,
    pub(super) deps_in_order: Vec<SymbolName>,
}

impl Spanned for (&Span, &SymbolName, &SymbolDefinition) {
    fn span(&self) -> Span {
        *self.0
    }
}

impl Evaluate for (&Span, &SymbolName, &SymbolDefinition) {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let (span, name, def): (&Span, &SymbolName, &SymbolDefinition) = *self;
        match def {
            SymbolDefinition::Implicit(ImplicitDefinition::DefaultAssigned(value, _)) => Ok(*value),
            SymbolDefinition::Explicit(ExplicitDefinition::Origin(
                Origin::Symbolic(_span, name),
                _block_id,
            )) => {
                unreachable!("symbolic origin {name} should already have been deduced")
            }
            SymbolDefinition::Explicit(ExplicitDefinition::Origin(
                Origin::Literal(_span, address),
                _block_id,
            ))
            | SymbolDefinition::Explicit(ExplicitDefinition::Origin(
                Origin::Deduced(_span, _, address),
                _block_id,
            )) => Ok((*address).into()),
            SymbolDefinition::Explicit(ExplicitDefinition::Tag(TagDefinition::Resolved {
                span: _,
                address,
            })) => Ok(address.into()),
            SymbolDefinition::Explicit(ExplicitDefinition::Tag(TagDefinition::Unresolved {
                block_id,
                block_offset,
                span,
            })) => {
                if let Some(block_position) = ctx.memory_map.get(block_id).cloned() {
                    let what: (&BlockIdentifier, &BlockPosition) = (block_id, &block_position);
                    let block_origin: Address = subword::right_half(what.evaluate(ctx)?).into();
                    match offset_from_origin(&block_origin, *block_offset) {
                        Ok(computed_address) => Ok(computed_address.into()),
                        Err(_overflow_error) => Err(SymbolLookupFailure::BlockTooLarge(
                            *span,
                            MachineLimitExceededFailure::BlockTooLarge {
                                span: *span,
                                block_id: *block_id,
                                offset: (*block_offset).into(),
                            },
                        )),
                    }
                } else {
                    panic!(
                        "Tag named {name} at {span:?} refers to unknown block {block_id}: {def:?}"
                    );
                }
            }
            SymbolDefinition::Explicit(ExplicitDefinition::Equality(expression)) => {
                expression.evaluate(ctx)
            }
            SymbolDefinition::Implicit(ImplicitDefinition::Undefined(context_union)) => {
                Err(SymbolLookupFailure::Missing {
                    name: name.to_owned(),
                    span: *span,
                    uses: context_union.clone(),
                })
            }
        }
    }
}

impl SymbolTable {
    pub(crate) fn new() -> SymbolTable {
        SymbolTable {
            definitions: Default::default(),
        }
    }

    pub(crate) fn get(&self, name: &SymbolName) -> Option<&SymbolDefinition> {
        self.definitions.get(name).map(|internal| &internal.def)
    }

    pub(crate) fn get_clone(&mut self, name: &SymbolName) -> Option<SymbolDefinition> {
        self.get(name).cloned()
    }

    pub(crate) fn is_defined(&self, name: &SymbolName) -> bool {
        self.definitions.contains_key(name)
    }

    pub(crate) fn define(
        &mut self,
        span: Span,
        name: SymbolName,
        new_definition: SymbolDefinition,
    ) -> Result<(), BadSymbolDefinition> {
        dbg!(&new_definition);
        if let Some(existing) = self.definitions.get_mut(&name) {
            dbg!(&existing);
            if matches!(
                &new_definition,
                SymbolDefinition::Implicit(ImplicitDefinition::Undefined(_)),
            ) {
                event!(Level::DEBUG, "skipping redefinition of symbol {name} with undefined value because it already has a definition, {}", existing.def);
                Ok(())
            } else {
                existing.def.override_with(name, span, new_definition)
            }
        } else {
            self.definitions.insert(
                name,
                InternalSymbolDef {
                    span,
                    def: new_definition,
                },
            );
            Ok(())
        }
    }

    pub(crate) fn record_usage_context(
        &mut self,
        name: SymbolName,
        span: Span,
        context: SymbolContext,
    ) {
        self.definitions
            .entry(name)
            .and_modify(|def| {
                def.def.merge_context(context.clone());
            })
            .or_insert_with(|| InternalSymbolDef {
                span,
                def: SymbolDefinition::Implicit(ImplicitDefinition::Undefined(context.clone())),
            });
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FinalSymbolType {
    Tag,
    Equality,
    Default,
}

#[derive(Debug)]
pub(crate) enum FinalSymbolDefinition {
    PositionIndependent(Unsigned36Bit),
    PositionDependent,
}

#[derive(Debug, Default)]
pub(crate) struct FinalSymbolTable {
    definitions: BTreeMap<SymbolName, (FinalSymbolType, String, FinalSymbolDefinition)>,
}

impl FinalSymbolTable {
    pub(crate) fn define(
        &mut self,
        name: SymbolName,
        sym_type: FinalSymbolType,
        rep: String,
        def: FinalSymbolDefinition,
    ) {
        self.definitions.insert(name, (sym_type, rep, def));
    }

    pub(crate) fn define_if_undefined(
        &mut self,
        name: SymbolName,
        sym_type: FinalSymbolType,
        rep: String,
        def: FinalSymbolDefinition,
    ) {
        self.definitions.entry(name).or_insert((sym_type, rep, def));
    }
}

impl Display for FinalSymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let show = |f: &mut std::fmt::Formatter<'_>,
                    sym_type_wanted: FinalSymbolType,
                    title: &str|
         -> std::fmt::Result {
            writeln!(f)?;
            writeln!(f, "** {title}")?;
            for (name, (_final_symbol_type, representation, definition)) in self
                .definitions
                .iter()
                .filter(|(_, (symtype, _, _))| symtype == &sym_type_wanted)
            {
                match definition {
                    FinalSymbolDefinition::PositionIndependent(word) => {
                        writeln!(f, "{name:20} = {word:012} ** {representation:>20}")?;
                    }
                    FinalSymbolDefinition::PositionDependent => {
                        writeln!(f, "{name:20} = {representation}")?;
                    }
                }
            }
            Ok(())
        };

        show(f, FinalSymbolType::Tag, "Tags")?;
        show(f, FinalSymbolType::Equality, "Equalities")?;
        show(f, FinalSymbolType::Default, "Default-assigned values")?;
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum TagDefinition {
    Unresolved {
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
        span: Span,
    },
    Resolved {
        address: Address,
        span: Span,
    },
}

impl Display for TagDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TagDefinition::Unresolved {
                block_id,
                block_offset,
                span: _,
            } => {
                write!(
                    f,
                    "tag at offset {block_offset} in {block_id} with unspecified address"
                )
            }
            TagDefinition::Resolved { address, span: _ } => {
                write!(f, "tag with address {address:06o}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum ExplicitDefinition {
    Tag(TagDefinition),
    Equality(EqualityValue),
    Origin(Origin, BlockIdentifier),
}

impl Display for ExplicitDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ExplicitDefinition::Origin(origin, _block_identifier) => {
                write!(f, "{origin}")
            }
            ExplicitDefinition::Tag(tagdef) => {
                write!(f, "{tagdef}")
            }
            ExplicitDefinition::Equality(inst) => {
                // TODO: print the assigned value, too?
                write!(f, "assignment with value {inst:#?}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum ImplicitDefinition {
    Undefined(SymbolContext),
    DefaultAssigned(Unsigned36Bit, SymbolContext),
}

impl Display for ImplicitDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use ImplicitDefinition::*;
        match self {
            Undefined(_context) => f.write_str("undefined"),
            DefaultAssigned(value, _) => {
                write!(f, "default-assigned as {value}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Explicit(ExplicitDefinition),
    Implicit(ImplicitDefinition),
}

impl Display for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Implicit(definition) => write!(f, "{}", definition),
            SymbolDefinition::Explicit(definition) => write!(f, "{}", definition),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum BadSymbolDefinition {
    Incompatible(SymbolName, Span, SymbolDefinition, SymbolDefinition),
}

impl BadSymbolDefinition {
    pub(crate) fn symbol(&self) -> &SymbolName {
        match self {
            BadSymbolDefinition::Incompatible(name, _, _, _) => name,
        }
    }
}

impl Spanned for BadSymbolDefinition {
    fn span(&self) -> Span {
        match self {
            BadSymbolDefinition::Incompatible(_, span, _, _) => *span,
        }
    }
}

impl Display for BadSymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BadSymbolDefinition::Incompatible(
                name,
                _,
                SymbolDefinition::Explicit(ExplicitDefinition::Tag(td1)),
                SymbolDefinition::Explicit(ExplicitDefinition::Tag(td2)),
            ) => {
                write!(
                    f,
                    "{name} is defined more than once (tag defitions are {td1} and {td2})"
                )
            }
            BadSymbolDefinition::Incompatible(name, _, previous, new) => {
                write!(f, "it is not allowed to override the symbol definition of {name} as {previous} with a new definition {new}")
            }
        }
    }
}

impl std::error::Error for BadSymbolDefinition {}

impl SymbolDefinition {
    pub(crate) fn merge_context(&mut self, context: SymbolContext) {
        if let SymbolDefinition::Implicit(ImplicitDefinition::Undefined(current)) = self {
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
        name: SymbolName,
        span: Span,
        update: SymbolDefinition,
    ) -> Result<(), BadSymbolDefinition> {
        use SymbolDefinition::{Explicit, Implicit};
        match (self, update) {
            (
                current @ Explicit(ExplicitDefinition::Equality(_)),
                new @ Explicit(ExplicitDefinition::Equality(_)),
            ) => {
                // This is always OK.
                *current = new;
                Ok(())
            }
            (current @ Implicit(ImplicitDefinition::Undefined(_)), new) => {
                // This is always OK.
                *current = new;
                Ok(())
            }
            (current, new) => {
                if current == &new {
                    Ok(()) // nothing to do.
                } else {
                    Err(BadSymbolDefinition::Incompatible(
                        name,
                        span,
                        current.clone(),
                        new,
                    ))
                }
            }
        }
    }
}

pub(super) fn assign_default_rc_word_tags<R: RcAllocator>(
    symtab: &mut SymbolTable,
    rcblock: &mut R,
    final_symbols: &mut FinalSymbolTable,
) -> Result<(), RcWordAllocationFailure> {
    for (name, def) in symtab.definitions.iter_mut() {
        *def = match &def {
            InternalSymbolDef {
                span,
                def: SymbolDefinition::Implicit(ImplicitDefinition::Undefined(context)),
            } if context.requires_rc_word_allocation() => {
                let value = Unsigned36Bit::ZERO;
                let addr = rcblock
                    .allocate(RcWordSource::DefaultAssignment(*span, name.clone()), value)?;
                final_symbols.define(
                    name.clone(),
                    FinalSymbolType::Equality,
                    value.to_string(),
                    FinalSymbolDefinition::PositionIndependent(value),
                );

                InternalSymbolDef {
                    span: *span,
                    def: SymbolDefinition::Implicit(ImplicitDefinition::DefaultAssigned(
                        addr.into(),
                        context.clone(),
                    )),
                }
            }
            other => (*other).clone(),
        }
    }
    Ok(())
}
