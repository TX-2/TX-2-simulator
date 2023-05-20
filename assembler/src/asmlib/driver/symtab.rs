use std::collections::HashMap;

use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::prelude::*;
use base::subword;

use super::super::ast::Origin;
use super::super::eval::{
    BadSymbolDefinition, Evaluate, MemoryReference, SymbolContext, SymbolDefinition, SymbolLookup,
    SymbolValue,
};
use super::super::symbol::SymbolName;
use super::super::types::Span;
use super::super::types::{offset_from_origin, MachineLimitExceededFailure};
use super::LookupTarget;
use super::{SymbolLookupFailure, SymbolLookupFailureKind};

/// Instances of Infallible cannot be created as it has no variants.
/// When the never type (`!`) is stabilised, we should use that
/// instead.
#[derive(Debug)]
pub(crate) enum Infallible {}

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

/// FinalSymbolTable has final values for all identifiers.
#[derive(Debug, Default)]
pub(crate) struct FinalSymbolTable {
    entries: HashMap<SymbolName, Unsigned36Bit>,
    block_origins: BTreeMap<usize, Address>,
}

impl FinalSymbolTable {
    pub(crate) fn list(&self) -> Vec<(SymbolName, Unsigned36Bit)> {
        let mut result: Vec<(SymbolName, Unsigned36Bit)> = self
            .entries
            .iter()
            .map(|(name, val)| (name.clone(), *val))
            .collect();
        result.sort();
        result
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn get_block_origin(&self, block_number: &usize) -> Option<&Address> {
        self.block_origins.get(block_number)
    }
}

impl SymbolLookup for FinalSymbolTable {
    type Error = Infallible;
    type Operation<'a> = ();

    fn lookup_with_op(
        &mut self,
        name: &SymbolName,
        _span: Span,
        _: &SymbolContext,
        _op: &mut Self::Operation<'_>,
    ) -> Result<SymbolValue, Self::Error> {
        match self.entries.get(name) {
            Some(value) => Ok(SymbolValue::Final(*value)),
            None => {
                panic!("no value was found in the final symbol table for symbol {name}");
            }
        }
    }
    fn lookup(
        &mut self,
        name: &SymbolName,
        span: Span,
        context: &SymbolContext,
    ) -> Result<SymbolValue, Self::Error> {
        self.lookup_with_op(name, span, context, &mut ())
    }

    fn resolve_memory_reference(
        &mut self,
        memref: &MemoryReference,
        _span: Span,
        _op: &mut Self::Operation<'_>,
    ) -> Result<Address, Self::Error> {
        match self.block_origins.get(&memref.block_number) {
            Some(block_origin) => match offset_from_origin(block_origin, memref.block_offset) {
                Ok(addr) => Ok(addr),
                Err(e) => {
                    panic!("failed to compute block offset {memref:?}: {e}");
                }
            },
            None => {
                panic!(
                    "failed to resolve reference to unknown memory block {}",
                    memref.block_number
                );
            }
        }
    }
}

fn finalise_symbol(
    symbol_name: &SymbolName,
    span: &Span,
    context: &SymbolContext,
    t: &mut SymbolTable,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let mut op = FinalLookupOperation::default();
    match t.lookup_with_op(symbol_name, *span, context, &mut op) {
        Ok(value) => match value {
            SymbolValue::Final(value) => Ok(value),
        },
        Err(e) => Err(e),
    }
}

pub(super) enum SymbolTableFinalisationError {
    DefaultValueAssignment(DefaultValueAssignmentError),
    SymbolLookup(SymbolLookupFailure),
}

pub(super) fn finalise_symbol_table<'a, I>(
    mut t: SymbolTable,
    symbol_refs_in_program_order: I,
) -> Result<FinalSymbolTable, SymbolTableFinalisationError>
where
    I: Iterator<Item = &'a (SymbolName, Span, SymbolContext)>,
{
    let mut finalized_entries: HashMap<SymbolName, Unsigned36Bit> = HashMap::new();
    for (symbol_name, span, context) in symbol_refs_in_program_order {
        let val: Unsigned36Bit = finalise_symbol(symbol_name, span, context, &mut t)
            .map_err(SymbolTableFinalisationError::SymbolLookup)?;
        finalized_entries.insert(symbol_name.clone(), val);
    }
    let mut origins: BTreeMap<usize, Address> = BTreeMap::new();
    let blocks: Vec<(usize, BlockPosition)> =
        t.blocks.iter().map(|(i, bl)| (*i, bl.clone())).collect();
    for (block_number, block) in blocks {
        let address = if let Some(address) = block.block_address {
            address
        } else {
            let mut op = FinalLookupOperation::default();
            match t.finalise_origin(block_number, block.span, Some(&mut op)) {
                Ok(address) => address,
                Err(e) => {
                    return Err(SymbolTableFinalisationError::DefaultValueAssignment(e));
                }
            }
        };
        origins.insert(block_number, address);
    }

    Ok(FinalSymbolTable {
        entries: finalized_entries,
        block_origins: origins,
    })
}

#[derive(Debug, Clone)]
pub(super) struct BlockPosition {
    // span is either the span of the origin specification if there is
    // one, or otherwise the span of the first thing in the block.
    span: Span,
    origin: Option<Origin>,
    block_address: Option<Address>,
    block_size: usize,
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
pub(super) struct SymbolTable {
    definitions: BTreeMap<SymbolName, InternalSymbolDef>,
    blocks: BTreeMap<usize, BlockPosition>,
    // TODO: put rc_block in here?
    index_registers_used: Unsigned6Bit,
}

#[derive(Debug, Default)]
pub(crate) struct FinalLookupOperation {
    depends_on: HashSet<SymbolName>,
    deps_in_order: Vec<SymbolName>,
}

impl Display for SymbolLookupFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let desc = self.target.to_string();
        match self.kind() {
            SymbolLookupFailureKind::MissingDefault => {
                write!(f, "{desc} is not defined and no default value was applied")
            }
            SymbolLookupFailureKind::Inconsistent(msg) => f.write_str(msg.as_str()),
            SymbolLookupFailureKind::Loop { deps_in_order } => {
                let names: Vec<String> = deps_in_order.iter().map(|dep| dep.to_string()).collect();
                write!(
                    f,
                    "definition of {desc} has a dependency loop ({})",
                    names.join("->")
                )
            }
            SymbolLookupFailureKind::MachineLimitExceeded(fail) => {
                write!(f, "machine limit exceeded: {fail}")
            }
        }
    }
}

impl SymbolTable {
    pub(crate) fn new<I>(block_sizes: I) -> SymbolTable
    where
        I: IntoIterator<Item = (Span, Option<Origin>, usize)>,
    {
        let blocks = block_sizes
            .into_iter()
            .enumerate()
            .map(|(i, (span, maybe_origin, block_size))| {
                (
                    i,
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

    //pub(crate) fn define_if_undefined(
    //    &mut self,
    //    name: SymbolName,
    //    value: Unsigned36Bit,
    //    context: &SymbolContext,
    //) {
    //    self.definitions
    //        .entry(name)
    //        .and_modify(|def| {
    //            if let SymbolDefinition::Undefined(_) = def.def {
    //                def.def = SymbolDefinition::DefaultAssigned(value, context.clone());
    //            }
    //        })
    //        .or_insert(InternalSymbolDef {
    //            def: SymbolDefinition::DefaultAssigned(value, context.clone()),
    //            used: todo!(),
    //        })
    //}

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

    fn final_lookup_helper(
        &mut self,
        name: &SymbolName,
        span: Span,
        _context: &SymbolContext,
        op: &mut FinalLookupOperation,
    ) -> Result<SymbolValue, SymbolLookupFailure> {
        fn body(
            t: &mut SymbolTable,
            name: &SymbolName,
            span: Span,
            op: &mut FinalLookupOperation,
        ) -> Result<SymbolValue, SymbolLookupFailure> {
            if let Some(def) = t.get_clone(name) {
                match def {
                    SymbolDefinition::DefaultAssigned(value, _) => Ok(SymbolValue::Final(value)),
                    SymbolDefinition::Tag {
                        block_number,
                        block_offset,
                        span: _,
                    } => match t.finalise_origin(block_number, span, Some(op)) {
                        Ok(address) => Ok(SymbolValue::Final(
                            offset_from_origin(&address, block_offset)
                                .expect("program is too long")
                                .into(),
                        )),
                        Err(e) => {
                            panic!("failed to finalise origin of block {block_number}: {e}");
                        }
                    },
                    SymbolDefinition::Equality(expression) => {
                        expression.evaluate(t, op).map(SymbolValue::Final)
                    }
                    SymbolDefinition::Undefined(context_union) => {
                        match t.get_default_value(name, &span, &context_union) {
                            Ok(value) => Ok(SymbolValue::Final(value)),
                            Err(e) => Err(e),
                        }
                    }
                }
            } else {
                panic!("final symbol lookup of symbol '{name}' happened in an evaluation context which was not previously returned by SourceFile::global_symbol_references(): {op:?}");
            }
        }

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
        let result = body(self, name, span, op);
        op.deps_in_order.pop();
        op.depends_on.remove(name);
        result
    }

    pub(crate) fn finalise_origin(
        &mut self,
        block_number: usize,
        block_span: Span,
        maybe_op: Option<&mut FinalLookupOperation>,
    ) -> Result<Address, DefaultValueAssignmentError> {
        let mut newdef: Option<(SymbolName, SymbolDefinition, Span)> = None;
        match self
            .blocks
            .get(&block_number)
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
                let mut new_op = FinalLookupOperation::default();
                let op: &mut FinalLookupOperation = maybe_op.unwrap_or(&mut new_op);
                self.assign_default_for_block(block_number, op)
            }
            BlockPosition {
                origin: Some(Origin::Symbolic(span, symbol_name)),
                block_address: None,
                ..
            } => {
                // The block hasn't yet been assigned an address, but it has a symbolic name.
                // If the name has a definition, that's the address to use.  Otherwise, we
                // assign an address and then update the symbol table.
                match self.get_clone(&symbol_name) {
                    Some(SymbolDefinition::Equality(rhs)) => {
                        let mut new_op = FinalLookupOperation::default();
                        let op: &mut FinalLookupOperation = maybe_op.unwrap_or(&mut new_op);
                        match rhs.evaluate(self, op) {
                            Ok(value) => Ok(Address::from(subword::right_half(value))),
                            Err(e) => {
                                panic!("no code to handle symbol lookup failure in finalise_origin: {e}"); // TODO
                            }
                        }
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
                        panic!("origin of block {block_number} is defined as {symbol_name} but this is a tag, and that is not allowed");
                    }
                    Some(SymbolDefinition::DefaultAssigned(value, _)) => {
                        Ok(Address::from(subword::right_half(value)))
                    }
                    None => {
                        let context = SymbolContext::origin(block_number, span);
                        let mut new_op = FinalLookupOperation::default();
                        let op: &mut FinalLookupOperation = maybe_op.unwrap_or(&mut new_op);
                        let addr = self.assign_default_for_block(block_number, op)?;
                        newdef = Some((symbol_name.clone(), SymbolDefinition::DefaultAssigned(addr.into(), context), span));
                        Ok(addr)
                    }
                    Some(SymbolDefinition::Undefined(context)) => {
                        let mut new_op = FinalLookupOperation::default();
                        let op: &mut FinalLookupOperation = maybe_op.unwrap_or(&mut new_op);
                        let addr = self.assign_default_for_block(block_number, op)?;
                        newdef = Some((symbol_name.clone(), SymbolDefinition::DefaultAssigned(addr.into(), context), block_span));
                        Ok(addr)
                    }
                }
            }
        }.and_then(|addr| {
            match self.blocks.get_mut(&block_number) {
                Some(block_pos) => {
                    block_pos.block_address = Some(addr);
                    Ok(addr)
                }
                None => Err(DefaultValueAssignmentError::Inconsistency(
                    format!("request to finalise origin of block {block_number} but there is no such block"))),
            }
        }).map(|a| {
            if let Some((symbol_name, def, span)) = newdef {
                self.definitions.insert(symbol_name, InternalSymbolDef {
                    span,
                    def,
                });
            }
            a
        })
    }

    fn assign_default_for_block(
        &mut self,
        block_number: usize,
        op: &mut FinalLookupOperation,
    ) -> Result<Address, DefaultValueAssignmentError> {
        let address = match block_number.checked_sub(1) {
            None => {
                // This is the first block.
                Ok(Origin::default_address())
            }
            Some(previous_block_number) => match self.blocks.get(&previous_block_number).cloned() {
                Some(previous) => {
                    let previous_block_origin =
                        self.finalise_origin(previous_block_number, previous.span, Some(op))?;
                    match offset_from_origin(&previous_block_origin, previous.block_size) {
                        Ok(addr) => Ok(addr),
                        Err(_) => Err(DefaultValueAssignmentError::MachineLimitExceeded(
                            MachineLimitExceededFailure::BlockTooLarge {
                                block_number: previous_block_number,
                                block_origin: previous_block_origin,
                                offset: previous.block_size,
                            },
                        )),
                    }
                }
                None => {
                    panic!("block {previous_block_number} is missing from the block layout");
                }
            },
        }?;
        if let Some(pos) = self.blocks.get_mut(&block_number) {
            pos.block_address = Some(address);
        } else {
            panic!("block {block_number} is missing from the block layout");
        }
        Ok(address)
    }

    /// Assign a default value for a symbol, using the rules from
    /// section 6-2.2 of the Users Handbook ("SYMEX DEFINITON - TAGS -
    /// EQUALITIES - AUTOMATIC ASSIGNMENT").
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
                todo!("assign the next word in the RC block")
            }
        }
    }
}

impl SymbolLookup for SymbolTable {
    type Error = SymbolLookupFailure;
    type Operation<'a> = FinalLookupOperation;

    fn lookup_with_op(
        &mut self,
        name: &SymbolName,
        span: Span,
        context: &SymbolContext,
        op: &mut Self::Operation<'_>,
    ) -> Result<SymbolValue, SymbolLookupFailure> {
        self.final_lookup_helper(name, span, context, op)
    }

    fn lookup(
        &mut self,
        name: &SymbolName,
        span: Span,
        context: &SymbolContext,
    ) -> Result<SymbolValue, SymbolLookupFailure> {
        let mut op = FinalLookupOperation::default();
        self.lookup_with_op(name, span, context, &mut op)
    }

    fn resolve_memory_reference(
        &mut self,
        memref: &MemoryReference,
        span: Span,
        op: &mut Self::Operation<'_>,
    ) -> Result<Address, SymbolLookupFailure> {
        let limit_exceeded = |mle: MachineLimitExceededFailure| -> SymbolLookupFailure {
            SymbolLookupFailure {
                target: LookupTarget::MemRef(*memref, span),
                kind: SymbolLookupFailureKind::MachineLimitExceeded(mle),
            }
        };

        match self.finalise_origin(memref.block_number, span, Some(op)) {
            Ok(block_origin) => match offset_from_origin(&block_origin, memref.block_offset) {
                Ok(addr) => Ok(addr),
                Err(_) => Err(limit_exceeded(MachineLimitExceededFailure::BlockTooLarge {
                    block_number: memref.block_number,
                    block_origin,
                    offset: memref.block_offset,
                })),
            },
            Err(value_assign_error) => match value_assign_error {
                DefaultValueAssignmentError::Inconsistency(msg) => Err(SymbolLookupFailure {
                    target: LookupTarget::MemRef(*memref, span),
                    kind: SymbolLookupFailureKind::Inconsistent(msg),
                }),
                DefaultValueAssignmentError::MachineLimitExceeded(mle) => Err(limit_exceeded(mle)),
            },
        }
    }
}
