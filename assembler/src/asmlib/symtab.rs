use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::prelude::*;
use base::subword;

use super::ast::{EqualityValue, Origin, RcAllocator, RcUpdater, RcWordAllocationFailure};
use super::eval::{
    Evaluate, HereValue, LookupTarget, SymbolLookup, SymbolLookupFailure, SymbolLookupFailureKind,
    SymbolValue,
};
use super::span::*;
use super::symbol::{SymbolContext, SymbolName};
use super::types::{
    offset_from_origin, BlockIdentifier, InconsistentOrigin, MachineLimitExceededFailure,
    RcWordSource,
};

#[derive(Debug, Clone)]
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

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug)]
pub(crate) struct SymbolTable {
    definitions: BTreeMap<SymbolName, InternalSymbolDef>,
    blocks: BTreeMap<BlockIdentifier, BlockPosition>,
    index_registers_used: Unsigned6Bit,
}

#[derive(Debug, Default)]
pub(crate) struct LookupOperation {
    depends_on: HashSet<SymbolName>,
    deps_in_order: Vec<SymbolName>,
}

impl Spanned for (&Span, &SymbolName, &SymbolDefinition) {
    fn span(&self) -> Span {
        *self.0
    }
}

impl Evaluate for (&Span, &SymbolName, &SymbolDefinition) {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let (span, name, def): (&Span, &SymbolName, &SymbolDefinition) = *self;
        match def {
            SymbolDefinition::DefaultAssigned(value, _) => Ok(*value),
            SymbolDefinition::Origin(addr) => Ok((*addr).into()),
            SymbolDefinition::Tag(TagDefinition::Resolved { span: _, address }) => {
                Ok(address.into())
            }
            SymbolDefinition::Tag(TagDefinition::Unresolved {
                block_id,
                block_offset,
                span,
            }) => {
                if let Some(block_position) = symtab.get_block_position(block_id).cloned() {
                    let what: (&BlockIdentifier, &BlockPosition) = (block_id, &block_position);
                    let block_origin: Address = subword::right_half(what.evaluate(
                        target_address,
                        symtab,
                        rc_updater,
                        op,
                    )?)
                    .into();
                    match offset_from_origin(&block_origin, *block_offset) {
                        Ok(computed_address) => Ok(computed_address.into()),
                        Err(_overflow_error) => Err(SymbolLookupFailure {
                            target: LookupTarget::Symbol(name.clone(), *span),
                            kind: SymbolLookupFailureKind::MachineLimitExceeded(
                                MachineLimitExceededFailure::BlockTooLarge {
                                    span: *span,
                                    block_id: *block_id,
                                    offset: (*block_offset).into(),
                                },
                            ),
                        }),
                    }
                } else {
                    panic!(
                        "Tag named {name} at {span:?} refers to unknown block {block_id}: {def:?}"
                    );
                }
            }
            SymbolDefinition::Equality(expression) => {
                expression.evaluate(target_address, symtab, rc_updater, op)
            }
            SymbolDefinition::Undefined(context_union) => Err(SymbolLookupFailure {
                target: LookupTarget::Symbol(name.to_owned(), *span),
                kind: SymbolLookupFailureKind::Missing {
                    uses: context_union.clone(),
                },
            }),
        }
    }
}

fn final_lookup_helper_body<R: RcUpdater>(
    symtab: &mut SymbolTable,
    name: &SymbolName,
    span: Span,
    target_address: &HereValue,
    rc_updater: &mut R,
    op: &mut LookupOperation,
) -> Result<SymbolValue, SymbolLookupFailure> {
    if let Some(def) = symtab.get_clone(name) {
        let what = (&span, name, &def);
        match what.evaluate(target_address, symtab, rc_updater, op) {
            Ok(value) => Ok(SymbolValue::Final(value)),
            Err(SymbolLookupFailure {
                target: _,
                // This symbol was used as a block origin, but there
                // is no definition for it.  So we position this block
                // (and determine the value for this origin) by taking
                // into account the position and length of the
                // previous block.
                kind:
                    SymbolLookupFailureKind::Missing {
                        uses:
                            SymbolContext {
                                origin_of_block: Some(block_identifier),
                                ..
                            },
                    },
            }) => {
                if let Some(block_position) = symtab.blocks.get(&block_identifier).cloned() {
                    // If we simply try to pass block_position to
                    // evaluate() we will loop and diagnose this as an
                    // undefined symbol.  While the symbol has no
                    // definition via assignment, we can determine the
                    // position of the block by appending it to the
                    // previous block.  So we evaluate the block's
                    // position as if it had no origin specification.
                    let pos_with_unspecified_origin: BlockPosition = BlockPosition {
                        origin: None,
                        ..block_position
                    };
                    let what: (&BlockIdentifier, &BlockPosition) =
                        (&block_identifier, &pos_with_unspecified_origin);
                    match what.evaluate(target_address, symtab, rc_updater, op) {
                        Ok(value) => {
                            let address: Address = subword::right_half(value).into();
                            match symtab.define(
                                span,
                                name.clone(),
                                SymbolDefinition::Origin(address),
                            ) {
                                Ok(()) => Ok(SymbolValue::Final(value)),
                                Err(e) => {
                                    panic!("got a bad symbol definition error ({e}) on a previously undefined origin symbol, which should be impossible");
                                }
                            }
                        }
                        Err(e) => Err(e),
                    }
                } else {
                    unreachable!("symbol {name} was used as an origin for block {block_identifier} but this is not a known block");
                }
            }
            Err(SymbolLookupFailure {
                target: _,
                kind:
                    SymbolLookupFailureKind::Missing {
                        uses: context_union,
                    },
            }) => match symtab.get_default_value(name, &span, &context_union) {
                Ok(value) => {
                    match symtab.define(
                        span,
                        name.clone(),
                        SymbolDefinition::DefaultAssigned(value, context_union),
                    ) {
                        Err(e) => {
                            panic!("got a bad symbol definition error ({e}) on a previously undefined symbol, which should be impossible");
                        }
                        Ok(()) => Ok(SymbolValue::Final(value)),
                    }
                }
                Err(e) => Err(e),
            },
            Err(other) => Err(other),
        }
    } else {
        panic!("final symbol lookup of symbol '{name}' happened in an evaluation context which was not previously returned by SourceFile::global_symbol_references(): {op:?}");
    }
}

impl SymbolTable {
    pub(crate) fn new<I>(block_sizes: I) -> SymbolTable
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

        SymbolTable {
            definitions: Default::default(),
            blocks,
            index_registers_used: Unsigned6Bit::ZERO,
        }
    }

    pub(crate) fn get(&self, name: &SymbolName) -> Option<&SymbolDefinition> {
        self.definitions.get(name).map(|internal| &internal.def)
    }

    pub(crate) fn get_clone(&mut self, name: &SymbolName) -> Option<SymbolDefinition> {
        self.get(name).cloned()
    }

    pub(crate) fn get_block_position(&self, block: &BlockIdentifier) -> Option<&BlockPosition> {
        self.blocks.get(block)
    }

    pub(crate) fn blocks_iter(&self) -> impl Iterator<Item = (&BlockIdentifier, &BlockPosition)> {
        self.blocks.iter()
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
        if let Some(existing) = self.definitions.get_mut(&name) {
            if matches!(&new_definition, SymbolDefinition::Undefined(_),) {
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
                def: SymbolDefinition::Undefined(context.clone()),
            });
    }

    /// Assign a default value for a symbol, using the rules from
    /// section 6-2.2 of the Users Handbook ("SYMEX DEFINITON - TAGS -
    /// EQUALITIES - AUTOMATIC ASSIGNMENT").
    ///
    /// Values which refer to addresses (and which therefore should
    /// point to a zero-initialised RC-word) should already have a
    /// default value assigned.
    pub(crate) fn get_default_value(
        &mut self,
        name: &SymbolName,
        span: &Span,
        contexts_used: &SymbolContext,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let get_target = || LookupTarget::Symbol(name.clone(), *span);
        event!(
            Level::DEBUG,
            "assigning default value for {name} used in contexts {contexts_used:?}"
        );
        match contexts_used.bits() {
            [false, false, _, true] => {
                // origin only or address and origin
                unreachable!("get_default_value should not be called for origin speicifations; attempted to assign default value for {name} (used in contexts: {contexts_used:?}")
            }
            [true, _, _, true] | [_, true, _, true] => {
                // origin and either config or index
                Err(SymbolLookupFailure {
                    target: get_target(),
                    kind: SymbolLookupFailureKind::InconsistentOrigins(InconsistentOrigin {
                        origin_name: name.clone(),
                        span: *span,
                        msg: format!("symbol {name} was used in both origin and other contexts"),
                    }),
                })
            }
            [false, false, false, false] => unreachable!(), // apparently no usage at all
            [true, _, _, false] => Ok(Unsigned36Bit::ZERO), // configuration (perhaps in combo with others)
            [false, true, _, false] => {
                // Index but not also configuration. Assign the next
                // index register.  This count start at 0, but we
                // Can't assign X0, so we increment first (as X0 is
                // always 0 and we can't assign it).
                match self.index_registers_used.checked_add(u6!(1)) {
                    Some(n) => {
                        self.index_registers_used = n;
                        Ok(n.into())
                    }
                    None => Err(SymbolLookupFailure {
                        target: get_target(),
                        kind: SymbolLookupFailureKind::MachineLimitExceeded(
                            MachineLimitExceededFailure::RanOutOfIndexRegisters(
                                *span,
                                name.clone(),
                            ),
                        ),
                    }),
                }
            }
            [false, false, true, false] => {
                unreachable!("default assignments for address-context symexes should be assigned before evaluation starts")
            }
        }
    }

    // evaluate_with_temporary_tag_overrides is commented out because
    // it is not required for RC-words, but it (or something similar)
    // will be required for macro bodies.
    //
    //pub(crate) fn evaluate_with_temporary_tag_overrides<E, R>(
    //    &mut self,
    //    tag_overrides: BTreeMap<&Tag, Address>,
    //    item: &E,
    //    target_address: &HereValue,
    //    rc_allocator: &mut R,
    //    op: &mut LookupOperation,
    //) -> Result<Unsigned36Bit, SymbolLookupFailure>
    //where
    //    E: Evaluate,
    //    R: RcUpdater,
    //{
    //    let temporarily_overridden = |symtab: &mut SymbolTable,
    //                                  (Tag { name, span }, addr): (&Tag, Address)|
    //     -> (SymbolName, Option<InternalSymbolDef>) {
    //        let restore: Option<InternalSymbolDef> = symtab.definitions.insert(
    //            name.clone(),
    //            InternalSymbolDef {
    //                span: *span,
    //                def: SymbolDefinition::TagOverride(addr),
    //            },
    //        );
    //        (name.clone(), restore)
    //    };
    //
    //    let to_restore: Vec<(SymbolName, Option<InternalSymbolDef>)> = tag_overrides
    //        .into_iter()
    //        .map(|(tag, addr)| temporarily_overridden(self, (tag, addr)))
    //        .collect();
    //
    //    // Important not to use '?' here as we need to restore
    //    // the original definition.
    //    let result = item.evaluate(target_address, self, rc_allocator, op);
    //
    //    for prior_definition in to_restore.into_iter() {
    //        match prior_definition {
    //            (name, None) => {
    //                self.definitions.remove(&name);
    //            }
    //            (name, Some(prior_definition)) => {
    //                self.definitions.insert(name.clone(), prior_definition);
    //            }
    //        }
    //    }
    //    result
    //}
}

impl SymbolLookup for SymbolTable {
    type Operation<'a> = LookupOperation;

    fn lookup_with_op<R: RcUpdater>(
        &mut self,
        name: &SymbolName,
        span: Span,
        target_address: &HereValue,
        rc_updater: &mut R,
        op: &mut Self::Operation<'_>,
    ) -> Result<SymbolValue, SymbolLookupFailure> {
        op.deps_in_order.push(name.clone());
        if !op.depends_on.insert(name.clone()) {
            // `name` was already in `depends_on`; in other words,
            // we have a loop.
            return Err(SymbolLookupFailure::from((
                name.clone(),
                span,
                SymbolLookupFailureKind::Loop {
                    deps_in_order: op.deps_in_order.to_vec(),
                },
            )));
        }
        let result = final_lookup_helper_body(self, name, span, target_address, rc_updater, op);
        op.deps_in_order.pop();
        op.depends_on.remove(name);
        result
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

#[derive(PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Tag(TagDefinition),
    Origin(Address),
    Equality(EqualityValue),
    Undefined(SymbolContext),
    DefaultAssigned(Unsigned36Bit, SymbolContext),
}

impl Debug for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Origin(address) => write!(f, "Origin({address:o})"),
            SymbolDefinition::Tag(tagdef) => {
                write!(f, "Tag({tagdef:?})")
            }
            SymbolDefinition::Equality(expr) => f.debug_tuple("Equality").field(expr).finish(),
            SymbolDefinition::DefaultAssigned(value, _) => {
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
            SymbolDefinition::DefaultAssigned(value, _) => {
                write!(f, "default-assigned as {value}")
            }
            SymbolDefinition::Origin(address)
            | SymbolDefinition::Tag(TagDefinition::Resolved { address, .. }) => {
                write!(f, "{address:06o}")
            }
            SymbolDefinition::Tag(TagDefinition::Unresolved {
                block_id,
                block_offset,
                span: _,
            }) => {
                write!(
                    f,
                    "tag at offset {block_offset} in {block_id} with unspecified address"
                )
            }
            SymbolDefinition::Equality(inst) => {
                // TODO: print the assigned value, too?
                write!(f, "assignment with value {inst:#?}")
            }
            SymbolDefinition::Undefined(_context) => f.write_str("undefined"),
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
            BadSymbolDefinition::Incompatible(name, _, previous, new) => {
                write!(f, "it is not allowed to override symbol definition of {name} as {previous} with a new definition {new}")
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
        name: SymbolName,
        span: Span,
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
                def: SymbolDefinition::Undefined(context),
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
                    def: SymbolDefinition::DefaultAssigned(addr.into(), context.clone()),
                }
            }
            other => (*other).clone(),
        }
    }
    Ok(())
}
