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
    offset_from_origin, BlockIdentifier, MachineLimitExceededFailure, RcWordSource,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum DefaultValueAssignmentError {
    Inconsistency(String),
    MachineLimitExceeded(MachineLimitExceededFailure),
}

impl Display for DefaultValueAssignmentError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            DefaultValueAssignmentError::Inconsistency(msg) => f.write_str(msg.as_str()),
            DefaultValueAssignmentError::MachineLimitExceeded(mlef) => {
                write!(f, "machine limit exceeded: {mlef}")
            }
        }
    }
}

impl std::error::Error for DefaultValueAssignmentError {}

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
                span: _,
            }) => match symtab.finalise_origin(*block_id, rc_updater, Some(op)) {
                Ok(address) => {
                    let computed_address: Address = address.index_by(*block_offset);
                    Ok(computed_address.into())
                }
                Err(e) => {
                    panic!("failed to finalise origin of {block_id}: {e}");
                }
            },
            SymbolDefinition::Equality(expression) => {
                // The target address does not matter below
                // since assignments are not allowed to use
                // '#' on the right-hand-side of the
                // assignment.
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
        match what
            .evaluate(target_address, symtab, rc_updater, op)
            .map(SymbolValue::Final)
        {
            Ok(value) => Ok(value),
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

    pub(crate) fn finalise_origin<R: RcUpdater>(
        &mut self,
        block_id: BlockIdentifier,
        rc_updater: &mut R,
        maybe_op: Option<&mut LookupOperation>,
    ) -> Result<Address, DefaultValueAssignmentError> {
        let mut newdef: Option<(SymbolName, SymbolDefinition, Span)> = None;
        match self
            .blocks
            .get(&block_id)
            .expect("request to finalise origin of non-existent block")
            .clone()
        {
            BlockPosition {
                origin: _,
                block_address: Some(address),
                ..
            }
            | BlockPosition {
                origin: Some(Origin::Literal(_, address)),
                ..
            } => Ok(address),
            BlockPosition {
                origin: None,
                block_address: None,
                ..
            } => {
                let mut new_op = LookupOperation::default();
                let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                self.assign_default_for_block(block_id, rc_updater, op)
            }
            BlockPosition {
                origin: Some(Origin::Symbolic(span, symbol_name)),
                block_address: None,
                span: block_span,
                ..
            } => {
                // The block hasn't yet been assigned an address, but it has a symbolic name.
                // If the name has a definition, that's the address to use.  Otherwise, we
                // assign an address and then update the symbol table.
                match self.get_clone(&symbol_name) {
                    Some(SymbolDefinition::Equality(rhs)) => {
                        let mut new_op = LookupOperation::default();
                        let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                        match rhs.evaluate(&HereValue::NotAllowed, self, rc_updater, op) {
                            Ok(value) => Ok(Address::from(subword::right_half(value))),
                            Err(e) => {
                                panic!("no code to handle symbol lookup failure in finalise_origin: {e}"); // TODO
                            }
                        }
                    }
                    Some(SymbolDefinition::Origin(addr)) => Ok(addr),
                    Some(SymbolDefinition::Tag(TagDefinition::Resolved{span: _, address})) => Ok(address),
                    Some(SymbolDefinition::Tag(TagDefinition::Unresolved { .. })) => {
                        // e.g.
                        //     FOO|FOO-> 1
                        // or
                        //     BAR-> 2
                        //     BAR|  3
                        //
                        // The second case is certainly a
                        // problem as it can give rise to a
                        // single memory location having two
                        // different contents (here, 2 or 3).
                        //
                        // TODO: handle this without a panic.
                        panic!("origin of block {block_id} is defined as {symbol_name} but this is a tag, and that is not allowed");
                    }
                    Some(SymbolDefinition::DefaultAssigned(value, _)) => {
                        Ok(Address::from(subword::right_half(value)))
                    }
                    None => {
                        let context = SymbolContext::origin(block_id, span);
                        let mut new_op = LookupOperation::default();
                        let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                        let addr = self.assign_default_for_block(block_id, rc_updater, op)?;
                        newdef = Some((symbol_name.clone(), SymbolDefinition::DefaultAssigned(addr.into(), context), span));
                        Ok(addr)
                    }
                    Some(SymbolDefinition::Undefined(context)) => {
                        let mut new_op = LookupOperation::default();
                        let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                        let addr = self.assign_default_for_block(block_id, rc_updater, op)?;
                        newdef = Some((symbol_name.clone(), SymbolDefinition::DefaultAssigned(addr.into(), context), block_span));
                        Ok(addr)
                    }
                }
            }
        }.and_then(|addr| {
            match self.blocks.get_mut(&block_id) {
                Some(block_pos) => {
                    block_pos.block_address = Some(addr);
                    Ok(addr)
                }
                None => Err(DefaultValueAssignmentError::Inconsistency(
                    format!("request to finalise origin of {block_id} but there is no such block"))),
            }
        }).inspect(|_a| {
            if let Some((symbol_name, def, span)) = newdef {
                self.definitions.insert(symbol_name, InternalSymbolDef {
                    span,
                    def,
                });
            }
        })
    }

    fn assign_default_for_block<R: RcUpdater>(
        &mut self,
        block_id: BlockIdentifier,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Address, DefaultValueAssignmentError> {
        let address = match block_id.previous_block() {
            None => {
                // This is the first block.
                Ok(Origin::default_address())
            }
            Some(previous_block) => match self.blocks.get(&previous_block).cloned() {
                Some(previous) => {
                    let previous_block_origin =
                        self.finalise_origin(previous_block, rc_updater, Some(op))?;
                    match offset_from_origin(&previous_block_origin, previous.block_size) {
                        Ok(addr) => Ok(addr),
                        Err(_) => Err(DefaultValueAssignmentError::MachineLimitExceeded(
                            MachineLimitExceededFailure::BlockTooLarge {
                                block_id: previous_block,
                                offset: previous.block_size.into(),
                            },
                        )),
                    }
                }
                None => {
                    panic!("{previous_block} is missing from the block layout");
                }
            },
        }?;
        if let Some(pos) = self.blocks.get_mut(&block_id) {
            pos.block_address = Some(address);
        } else {
            panic!("{block_id} is missing from the block layout");
        }
        Ok(address)
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
                todo!("assign origin value")
            }
            [true, _, _, true] | [_, true, _, true] => {
                // origin and either config or index
                Err(SymbolLookupFailure {
                    target: get_target(),
                    kind: SymbolLookupFailureKind::InconsistentOrigins {
                        name: name.clone(),
                        span: *span,
                        msg: format!("symbol {name} was used in both origin and other contexts"),
                    },
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
                            MachineLimitExceededFailure::RanOutOfIndexRegisters(name.clone()),
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
                let addr =
                    rcblock.allocate(RcWordSource::DefaultAssignment(name.clone()), value)?;
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
