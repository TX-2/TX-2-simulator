use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::prelude::*;
use base::subword;

use super::ast::{EqualityValue, Origin, RcAllocator, RcWordSource, Tag};
use super::eval::{
    Evaluate, HereValue, LookupTarget, SymbolLookup, SymbolLookupFailure, SymbolLookupFailureKind,
    SymbolValue,
};
use super::span::*;
use super::symbol::{SymbolContext, SymbolName};
use super::types::{offset_from_origin, BlockIdentifier, MachineLimitExceededFailure};

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

fn final_lookup_helper_body<R: RcAllocator>(
    t: &mut SymbolTable,
    name: &SymbolName,
    span: Span,
    target_address: &HereValue,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<SymbolValue, SymbolLookupFailure> {
    if let Some(def) = t.get_clone(name) {
        match def {
            SymbolDefinition::DefaultAssigned(value, _) => Ok(SymbolValue::Final(value)),
            SymbolDefinition::Origin(addr) => Ok(SymbolValue::Final(addr.into())),
            SymbolDefinition::Tag {
                block_id,
                block_offset,
                span: _,
            } => match t.finalise_origin(block_id, rc_allocator, Some(op)) {
                Ok(address) => {
                    let computed_address: Address = address.index_by(block_offset);
                    Ok(SymbolValue::Final(computed_address.into()))
                }
                Err(e) => {
                    panic!("failed to finalise origin of {block_id}: {e}");
                }
            },
            SymbolDefinition::TagOverride(address) => Ok(SymbolValue::Final(address.into())),
            SymbolDefinition::Equality(expression) => {
                // The target address does not matter below
                // since assignments are not allowed to use
                // '#' on the right-hand-side of the
                // assignment.
                expression
                    .evaluate(expression.span(), target_address, t, rc_allocator, op)
                    .map(SymbolValue::Final)
            }
            SymbolDefinition::Undefined(context_union) => {
                match t.get_default_value(name, &span, &context_union, rc_allocator) {
                    Ok(value) => {
                        match t.define(
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
                }
            }
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
                existing.def.override_with(new_definition)
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

    pub(crate) fn finalise_origin<R: RcAllocator>(
        &mut self,
        block_id: BlockIdentifier,
        rc_allocator: &mut R,
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
                self.assign_default_for_block(block_id, rc_allocator, op)
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
                        match rhs.evaluate(rhs.span(), &HereValue::NotAllowed, self, rc_allocator, op) {
                            Ok(value) => Ok(Address::from(subword::right_half(value))),
                            Err(e) => {
                                panic!("no code to handle symbol lookup failure in finalise_origin: {e}"); // TODO
                            }
                        }
                    }
                    Some(SymbolDefinition::Origin(addr)) => Ok(addr),
                    Some(SymbolDefinition::TagOverride(_)) => {
                        unreachable!("{symbol_name} was used as an origin for {block_id}, but its definition is a temporary tag override, which is not supposed to be in effect at the time we're computing the origins for blocks")
                    }
                    Some(SymbolDefinition::Tag { .. }) => {
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
                        let addr = self.assign_default_for_block(block_id, rc_allocator, op)?;
                        newdef = Some((symbol_name.clone(), SymbolDefinition::DefaultAssigned(addr.into(), context), span));
                        Ok(addr)
                    }
                    Some(SymbolDefinition::Undefined(context)) => {
                        let mut new_op = LookupOperation::default();
                        let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                        let addr = self.assign_default_for_block(block_id, rc_allocator, op)?;
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

    fn assign_default_for_block<R: RcAllocator>(
        &mut self,
        block_id: BlockIdentifier,
        rc_allocator: &mut R,
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
                        self.finalise_origin(previous_block, rc_allocator, Some(op))?;
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
    pub(crate) fn get_default_value<R: RcAllocator>(
        &mut self,
        name: &SymbolName,
        span: &Span,
        contexts_used: &SymbolContext,
        rc_allocator: &mut R,
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
                    kind: SymbolLookupFailureKind::Inconsistent(format!(
                        "symbol {name} was used in both origin and other contexts"
                    )),
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
                // address only, assign the next RC word.
                let rc_addr: Address = rc_allocator.allocate(
                    RcWordSource::DefaultAssignment(name.clone()),
                    Unsigned36Bit::ZERO,
                );
                let symbol_value: Unsigned36Bit = Unsigned36Bit::from(rc_addr);
                Ok(symbol_value)
            }
        }
    }

    pub(crate) fn evaluate_with_temporary_tag_override<E, R>(
        &mut self,
        tag_override: Option<(&Tag, Address)>,
        item: &E,
        item_span: Span,
        target_address: &HereValue,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure>
    where
        E: Evaluate,
        R: RcAllocator,
    {
        match tag_override {
            None => item.evaluate(item_span, target_address, self, rc_allocator, op),
            Some((Tag { name, span }, addr)) => {
                let to_restore: Option<InternalSymbolDef> = self.definitions.remove(name);
                self.definitions.insert(
                    name.clone(),
                    InternalSymbolDef {
                        span: *span,
                        def: SymbolDefinition::TagOverride(addr),
                    },
                );
                // Important not to use '?' here as we need to restore
                // the original definition.
                let result = item.evaluate(item_span, target_address, self, rc_allocator, op);
                if let Some(prior_definition) = to_restore {
                    self.definitions.insert(name.clone(), prior_definition);
                }
                result
            }
        }
    }
}

impl SymbolLookup for SymbolTable {
    type Operation<'a> = LookupOperation;

    fn lookup_with_op<R: RcAllocator>(
        &mut self,
        name: &SymbolName,
        span: Span,
        target_address: &HereValue,
        rc_allocator: &mut R,
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
        let result = final_lookup_helper_body(self, name, span, target_address, rc_allocator, op);
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
pub(crate) struct FinalSymbolDefinition {
    value: Unsigned36Bit,
    representation: String,
    sym_type: FinalSymbolType,
}

impl FinalSymbolDefinition {
    pub(crate) fn new(
        value: Unsigned36Bit,
        sym_type: FinalSymbolType,
        representation: String,
    ) -> Self {
        FinalSymbolDefinition {
            value,
            sym_type,
            representation,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct FinalSymbolTable {
    definitions: BTreeMap<SymbolName, FinalSymbolDefinition>,
}

impl FinalSymbolTable {
    pub(crate) fn define(&mut self, name: SymbolName, def: FinalSymbolDefinition) {
        self.definitions.insert(name, def);
    }

    pub(crate) fn define_if_undefined(&mut self, name: SymbolName, def: FinalSymbolDefinition) {
        self.definitions.entry(name).or_insert(def);
    }

    pub(crate) fn import_all_defined(&mut self, symtab: &SymbolTable) {
        fn make_final_def(name: &SymbolName, def: &SymbolDefinition) -> FinalSymbolDefinition {
            match def {
                SymbolDefinition::DefaultAssigned(value, _context) => FinalSymbolDefinition {
                    value: *value,
                    representation: value.to_string(),
                    sym_type: FinalSymbolType::Default,
                },
                SymbolDefinition::Undefined(_symbol_context) => unreachable!(),
                _ => unimplemented!(
                    "symbol table entry for {name} (with definition {def:?}) had not been copied into the final symbol table"
                ),
            }
        }

        for (name, definition) in symtab.definitions.iter() {
            self.definitions
                .entry(name.clone())
                .or_insert_with(|| make_final_def(name, &definition.def));
        }
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
            for (
                name,
                FinalSymbolDefinition {
                    value,
                    sym_type,
                    representation,
                },
            ) in self.definitions.iter()
            {
                if sym_type == &sym_type_wanted {
                    writeln!(f, "{name:20} = {value:012} ** {representation:>20}")?;
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

#[derive(PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Tag {
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
        span: Span,
    },
    TagOverride(Address),
    Origin(Address),
    Equality(EqualityValue),
    Undefined(SymbolContext),
    DefaultAssigned(Unsigned36Bit, SymbolContext),
}

impl Debug for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Origin(address) => write!(f, "Origin({address:o})"),
            SymbolDefinition::TagOverride(address) => write!(f, "TagOverride({address:o})"),
            SymbolDefinition::Tag {
                block_id,
                block_offset,
                span: _,
            } => {
                write!(
                    f,
                    "Tag {{block_id:{block_id:?}, block_offset:{block_offset}}}"
                )
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
            SymbolDefinition::Origin(addr) | SymbolDefinition::TagOverride(addr) => {
                write!(f, "{addr:06o}")
            }
            SymbolDefinition::Tag {
                block_id,
                block_offset,
                span: _,
            } => {
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
    Incompatible(SymbolDefinition, SymbolDefinition),
}

impl Display for BadSymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BadSymbolDefinition::Incompatible(previous, new) => {
                write!(f, "it is not allowed to override symbol definition {previous} with a new definition {new}")
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
                    Err(BadSymbolDefinition::Incompatible(current.clone(), new))
                }
            }
        }
    }
}

#[test]
fn test_loop_detection() {
    use super::ast::*;
    use super::eval::RcBlock;
    use base::charset::Script;
    let blocks = [(span(0..10), None, u18!(2))];
    let mut symtab = SymbolTable::new(blocks);

    // define "A"
    symtab
        .define(
            span(0..1),
            SymbolName::from("A"),
            SymbolDefinition::Equality(EqualityValue::from((
                span(0..1),
                vec![CommaDelimitedInstruction {
                    leading_commas: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(0..1),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from(ArithmeticExpression::from(
                            SymbolOrLiteral::Symbol(
                                Script::Normal,
                                SymbolName::from("B"),
                                span(2..3),
                            ),
                        )),
                    },
                    trailing_commas: None,
                }],
            ))),
        )
        .expect("definition of A should be correct");
    // define "B"
    symtab
        .define(
            span(4..5),
            SymbolName::from("B"),
            SymbolDefinition::Equality(EqualityValue::from((
                span(4..5),
                vec![CommaDelimitedInstruction {
                    leading_commas: None,
                    instruction: UntaggedProgramInstruction {
                        span: span(4..5),
                        holdbit: HoldBit::Unspecified,
                        inst: InstructionFragment::from(ArithmeticExpression::from(
                            SymbolOrLiteral::Symbol(
                                Script::Normal,
                                SymbolName::from("A"),
                                span(6..7),
                            ),
                        )),
                    },
                    trailing_commas: None,
                }],
            ))),
        )
        .expect("definition of B should be correct");

    let mut rc_block = RcBlock::default();

    // An attempt to look up A should fail because we detect a loop.
    let mut op = Default::default();
    let r = symtab.lookup_with_op(
        &SymbolName::from("A"),
        span(0..1),
        &HereValue::NotAllowed,
        &mut rc_block,
        &mut op,
    );
    dbg!(&r);
    assert!(matches!(
        r,
        Err(SymbolLookupFailure {
            target: _,
            kind: SymbolLookupFailureKind::Loop { .. }
        })
    ));
}
