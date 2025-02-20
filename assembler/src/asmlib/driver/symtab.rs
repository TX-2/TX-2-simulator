use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::prelude::*;
use base::subword;

use super::super::ast::Origin;
use super::super::eval::{
    BadSymbolDefinition, Evaluate, HereValue, LookupTarget, SymbolContext, SymbolDefinition,
    SymbolLookup, SymbolLookupFailure, SymbolLookupFailureKind, SymbolValue,
};
use super::super::symbol::SymbolName;
use super::super::types::{offset_from_origin, MachineLimitExceededFailure, Span};

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
    blocks: BTreeMap<usize, BlockPosition>,
    // TODO: put rc_block in here?
    index_registers_used: Unsigned6Bit,
}

#[derive(Debug, Default)]
pub(crate) struct LookupOperation {
    depends_on: HashSet<SymbolName>,
    deps_in_order: Vec<SymbolName>,
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

    #[cfg(test)]
    pub(crate) fn has_definitions(&self) -> bool {
        !self.definitions.is_empty()
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

    fn final_lookup_helper(
        &mut self,
        name: &SymbolName,
        span: Span,
        target_address: &HereValue,
        _context: &SymbolContext,
        op: &mut LookupOperation,
    ) -> Result<SymbolValue, SymbolLookupFailure> {
        fn body(
            t: &mut SymbolTable,
            name: &SymbolName,
            span: Span,
            target_address: &HereValue,
            op: &mut LookupOperation,
        ) -> Result<SymbolValue, SymbolLookupFailure> {
            if let Some(def) = t.get_clone(name) {
                match def {
                    SymbolDefinition::DefaultAssigned(value, _) => Ok(SymbolValue::Final(value)),
                    SymbolDefinition::Origin(addr) => Ok(SymbolValue::Final(addr.into())),
                    SymbolDefinition::Tag {
                        block_number,
                        block_offset,
                        span: _,
                    } => match t.finalise_origin(block_number, Some(op)) {
                        Ok(address) => {
                            let computed_address: Address = address.index_by(block_offset);
                            Ok(SymbolValue::Final(computed_address.into()))
                        }
                        Err(e) => {
                            panic!("failed to finalise origin of block {block_number}: {e}");
                        }
                    },
                    SymbolDefinition::Equality(expression) => {
                        // The target address does not matter below
                        // since assignments are not allowed to use
                        // '#' on the right-hand-side of the
                        // assignment.
                        expression
                            .evaluate(target_address, t, op)
                            .map(SymbolValue::Final)
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
        let result = body(self, name, span, target_address, op);
        op.deps_in_order.pop();
        op.depends_on.remove(name);
        result
    }

    pub(crate) fn finalise_origin(
        &mut self,
        block_number: usize,
        maybe_op: Option<&mut LookupOperation>,
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
                let mut new_op = LookupOperation::default();
                let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                self.assign_default_for_block(block_number, op)
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
                        match rhs.evaluate(&HereValue::NotAllowed, self, op) {
                            Ok(value) => Ok(Address::from(subword::right_half(value))),
                            Err(e) => {
                                panic!("no code to handle symbol lookup failure in finalise_origin: {e}"); // TODO
                            }
                        }
                    }
                    Some(SymbolDefinition::Origin(addr)) => Ok(addr),
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
                        let mut new_op = LookupOperation::default();
                        let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
                        let addr = self.assign_default_for_block(block_number, op)?;
                        newdef = Some((symbol_name.clone(), SymbolDefinition::DefaultAssigned(addr.into(), context), span));
                        Ok(addr)
                    }
                    Some(SymbolDefinition::Undefined(context)) => {
                        let mut new_op = LookupOperation::default();
                        let op: &mut LookupOperation = maybe_op.unwrap_or(&mut new_op);
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
        }).inspect(|_a| {
            if let Some((symbol_name, def, span)) = newdef {
                self.definitions.insert(symbol_name, InternalSymbolDef {
                    span,
                    def,
                });
            }
        })
    }

    fn assign_default_for_block(
        &mut self,
        block_number: usize,
        op: &mut LookupOperation,
    ) -> Result<Address, DefaultValueAssignmentError> {
        let address = match block_number.checked_sub(1) {
            None => {
                // This is the first block.
                Ok(Origin::default_address())
            }
            Some(previous_block_number) => match self.blocks.get(&previous_block_number).cloned() {
                Some(previous) => {
                    let previous_block_origin =
                        self.finalise_origin(previous_block_number, Some(op))?;
                    match offset_from_origin(&previous_block_origin, previous.block_size) {
                        Ok(addr) => Ok(addr),
                        Err(_) => Err(DefaultValueAssignmentError::MachineLimitExceeded(
                            MachineLimitExceededFailure::BlockTooLarge {
                                block_number: previous_block_number,
                                block_origin: previous_block_origin,
                                offset: previous.block_size.into(),
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
    type Operation<'a> = LookupOperation;

    fn lookup_with_op(
        &mut self,
        name: &SymbolName,
        span: Span,
        target_address: &HereValue,
        context: &SymbolContext,
        op: &mut Self::Operation<'_>,
    ) -> Result<SymbolValue, SymbolLookupFailure> {
        self.final_lookup_helper(name, span, target_address, context, op)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FinalSymbolType {
    Tag,
    Equality,
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

    pub(crate) fn check_all_defined(&self, symtab: &SymbolTable) {
        for (name, definition) in symtab.definitions.iter() {
            if !self.definitions.contains_key(name) {
                panic!("symbol {name} appears in symbol table with definition {definition:?} but was not finalised in the final symbol table");
            }
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
        show(f, FinalSymbolType::Equality, "Equalities")
    }
}
