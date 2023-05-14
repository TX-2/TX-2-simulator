use std::collections::HashMap;
use std::ops::Shl;

use base::prelude::*;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::{
    charset::Script,
    prelude::{Address, Unsigned36Bit},
};

use super::super::ast::Expression;
use super::super::eval::{BadSymbolDefinition, SymbolContext, SymbolDefinition, SymbolLookup};
use super::super::symbol::SymbolName;
use super::super::types::Span;
use super::super::types::{offset_from_origin, MachineLimitExceededFailure};
use super::{SymbolLookupFailure, SymbolLookupFailureKind};

/// Instances of Infallible cannot be created as it has no variants.
/// When the never type (`!`) is stabilised, we should use that
/// instead.
#[derive(Debug)]
pub(crate) enum Infallible {}

struct DefaultValueAssigner<'a> {
    program_words: Unsigned18Bit,
    rc_block: &'a mut Vec<Unsigned36Bit>,
    index_registers_used: &'a mut Unsigned6Bit,
}

impl<'a> DefaultValueAssigner<'a> {
    /// Assign a default value for a symbol, using the rules from
    /// section 6-2.2 of the Users Handbook ("SYMEX DEFINITON - TAGS -
    /// EQUALITIES - AUTOMATIC ASSIGNMENT").
    pub(crate) fn get_default_symbol_value(
        &mut self,
        name: &SymbolName,
        contexts_used: SymbolContext,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        event!(
            Level::DEBUG,
            "assigning default value for {name} used in contexts {contexts_used:?}"
        );
        match contexts_used.bits() {
            [false, false, _, true] => {
                // origin only or address and origin
                // TODO: this really isn't correct, since assigning an
                // origin for this block should extend
                // self.program_words by the size of the block we just
                // chose a location for.
                Ok(self.program_words.into())
            }
            [true, _, _, true] | [_, true, _, true] => {
                // origin and either config or index
                Err(SymbolLookupFailure::from((
                    name.clone(),
                    SymbolLookupFailureKind::Inconsistent(format!(
                        "symbol '{name}' was used in both origin and other contexts"
                    )),
                )))
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
                        *self.index_registers_used = n;
                        Ok(n.into())
                    }
                    None => Err(SymbolLookupFailure::from((
                        name.clone(),
                        SymbolLookupFailureKind::MachineLimitExceeded(
                            MachineLimitExceededFailure::RanOutOfIndexRegisters(name.clone()),
                        ),
                    ))),
                }
            }
            [false, false, true, false] => {
                // address only, assign the next RC word.
                Unsigned18Bit::try_from(self.rc_block.len())
                    .ok()
                    .and_then(|len| self.program_words.checked_add(len))
                    .map(|rc_word_addr| {
                        self.rc_block.push(Unsigned36Bit::ZERO);
                        Ok(rc_word_addr.into())
                    })
                    .unwrap_or(Err(SymbolLookupFailure::from((
                        name.clone(),
                        SymbolLookupFailureKind::MachineLimitExceeded(
                            MachineLimitExceededFailure::RcBlockTooLarge,
                        ),
                    ))))
            }
        }
    }
}

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

    fn lookup(
        &mut self,
        name: &SymbolName,
        _: &SymbolContext,
    ) -> Result<Unsigned36Bit, Self::Error> {
        match self.entries.get(name) {
            Some(value) => Ok(*value),
            None => {
                panic!("no value was found in the final symbol table for symbol {name}");
            }
        }
    }
}

fn resolve(
    symbol_name: &SymbolName,
    span: &Span,
    t: &mut SymbolTable,
    assigner: &mut DefaultValueAssigner,
    finalized_entries: &mut HashMap<SymbolName, Unsigned36Bit>,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    if let Some(value) = finalized_entries.get(symbol_name) {
        return Ok(*value);
    }

    let result = match t.get(symbol_name).cloned() {
        Some(SymbolDefinition::DefaultAssigned(value)) => Ok(value),
        Some(SymbolDefinition::Equality(Expression::Literal(value))) => Ok(value.value()),
        Some(SymbolDefinition::Equality(Expression::Symbol(_span, script, fwd_symbol_name))) => {
            // TODO: this logic should probably be delegated to
            // Expression::value, not done here.
            let value = resolve(&fwd_symbol_name, span, t, assigner, finalized_entries)?;
            Ok(value.shl(script.shift()))
        }
        Some(SymbolDefinition::Tag {
            block,
            offset: block_offset,
        }) => match t.block_origins.get(&block) {
            Some(block_address) => {
                let block_too_large = || -> SymbolLookupFailure {
                    SymbolLookupFailure::from((
                        symbol_name.clone(),
                        SymbolLookupFailureKind::MachineLimitExceeded(
                            MachineLimitExceededFailure::BlockTooLarge {
                                block_number: block,
                                block_origin: *block_address,
                                offset: block_offset,
                            },
                        ),
                    ))
                };
                // TODO: factor this out.
                let (physical_block_start, _) = block_address.split();

                match Unsigned18Bit::try_from(block_offset) {
                    Ok(offset) => match physical_block_start.checked_add(offset) {
                        Some(physical) => Ok(physical.into()),
                        None => Err(block_too_large()),
                    },
                    Err(_) => Err(block_too_large()),
                }
            }
            None => {
                panic!("symbol name {symbol_name:?} refers to offset {block_offset} in block {block} but there is no block {block}.");
            }
        },
        Some(SymbolDefinition::Undefined(use_contexts)) => {
            // Not already defined, so we need to assign a default.
            assigner.get_default_symbol_value(symbol_name, use_contexts)
        }
        None => {
            unreachable!()
        }
    };
    match result {
        Ok(value) => match finalized_entries.insert(symbol_name.clone(), value) {
            None => {
                t.define_if_undefined(symbol_name.clone(), value);
                Ok(value)
            }
            Some(_previous) => {
                panic!("symbol {symbol_name} occurs twice in symbols_in_program_order");
            }
        },
        Err(e) => Err(e),
    }
}

pub(super) fn finalise_symbol_table<'a, I>(
    mut t: SymbolTable,
    symbols_in_program_order: I,
    program_words: Unsigned18Bit,
    rc_block: &mut Vec<Unsigned36Bit>,
    mut index_registers_used: Unsigned6Bit,
) -> Result<FinalSymbolTable, SymbolLookupFailure>
where
    I: Iterator<Item = &'a (SymbolName, Span)>,
{
    let mut expected_but_misssing: HashSet<SymbolName> = t.definitions.keys().cloned().collect();
    let mut assigner = DefaultValueAssigner {
        program_words,
        rc_block,
        index_registers_used: &mut index_registers_used,
    };
    let mut finalized_entries: HashMap<SymbolName, Unsigned36Bit> = HashMap::new();
    for (symbol_name, span) in symbols_in_program_order {
        expected_but_misssing.remove(symbol_name);
        resolve(
            symbol_name,
            span,
            &mut t,
            &mut assigner,
            &mut finalized_entries,
        )?;
    }
    if !expected_but_misssing.is_empty() {
        panic!("final symbol table lacks entries for known symbols {expected_but_misssing:?}");
    }
    Ok(FinalSymbolTable {
        entries: finalized_entries,
        block_origins: t.block_origins.clone(),
    })
}

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug, Default)]
pub(super) struct SymbolTable {
    definitions: BTreeMap<SymbolName, SymbolDefinition>,
    block_origins: BTreeMap<usize, Address>,
}

#[derive(Debug)]
struct FinalLookupOperation {
    target: SymbolName,
    context: SymbolContext,
    depends_on: HashSet<SymbolName>,
    deps_in_order: Vec<SymbolName>,
}

impl FinalLookupOperation {
    fn new(target: SymbolName, context: SymbolContext) -> FinalLookupOperation {
        FinalLookupOperation {
            target,
            context,
            depends_on: Default::default(),
            deps_in_order: Default::default(),
        }
    }
}

impl Display for SymbolLookupFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let name = self.symbol_name();
        match self.kind() {
            SymbolLookupFailureKind::MissingDefault => {
                write!(
                    f,
                    "symbol {name} is not defined and no default value was applied"
                )
            }
            SymbolLookupFailureKind::Inconsistent(msg) => f.write_str(msg.as_str()),
            SymbolLookupFailureKind::Loop { deps_in_order } => {
                let names: Vec<String> = deps_in_order.iter().map(|dep| dep.to_string()).collect();
                write!(
                    f,
                    "definition of symbol {name} has a dependency loop ({})",
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
    pub(crate) fn get(&self, name: &SymbolName) -> Option<&SymbolDefinition> {
        self.definitions.get(name)
    }

    pub(crate) fn define(
        &mut self,
        name: SymbolName,
        new_definition: SymbolDefinition,
    ) -> Result<(), BadSymbolDefinition> {
        if let Some(existing) = self.definitions.get_mut(&name) {
            if matches!(&new_definition, SymbolDefinition::Undefined(_)) {
                event!(Level::DEBUG, "skipping redefinition of symbol {name} with undefined value because it already has a definition, {existing}");
                Ok(())
            } else {
                existing.override_with(new_definition)
            }
        } else {
            self.definitions.insert(name, new_definition);
            Ok(())
        }
    }

    pub(crate) fn define_if_undefined(&mut self, name: SymbolName, value: Unsigned36Bit) {
        self.definitions
            .entry(name)
            .and_modify(|def| {
                if let SymbolDefinition::Undefined(_) = def {
                    *def = SymbolDefinition::DefaultAssigned(value);
                }
            })
            .or_insert(SymbolDefinition::DefaultAssigned(value));
    }

    pub(crate) fn record_block_origin(&mut self, block_number: usize, address: Address) {
        self.block_origins.insert(block_number, address);
    }

    pub(crate) fn record_usage_context(
        &mut self,
        name: SymbolName,
        _span: Span,
        context: SymbolContext,
    ) {
        // TODO: record the span.
        self.definitions
            .entry(name)
            .and_modify(|def| {
                def.merge_context(context);
            })
            .or_insert(SymbolDefinition::Undefined(context));
    }

    fn final_lookup_helper(
        &self,
        name: &SymbolName,
        op: &mut FinalLookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        op.deps_in_order.push(name.clone());
        if !op.depends_on.insert(name.clone()) {
            // `name` was already in `depends_on`; in other words,
            // we have a loop.
            return Err(SymbolLookupFailure::from((
                name.clone(),
                SymbolLookupFailureKind::Loop {
                    deps_in_order: op.deps_in_order.to_vec(),
                },
            )));
        }
        let should_have_seen = |op: &FinalLookupOperation| {
            panic!("final symbol lookup of symbol '{}' happened in an evaluation context which was not previously returned by SourceFile::global_symbol_references(): {:?}", op.target, op);
        };
        match self.definitions.get(name) {
            Some(def) => match def {
                SymbolDefinition::DefaultAssigned(value) => Ok(*value),
                SymbolDefinition::Tag { block, offset } => match self.block_origins.get(block) {
                    Some(address) => Ok(offset_from_origin(address, *offset)
                        .expect("program is too long")
                        .into()),
                    None => {
                        panic!("definition of tag {name} references block {block} but there is no such block");
                    }
                },
                SymbolDefinition::Equality(expression) => match expression {
                    Expression::Literal(literal) => Ok(literal.value()),
                    Expression::Symbol(_span, elevation, symbol_name) => {
                        // We re-use the existing op object (1) to
                        // detect cycles.  I'm not yet clear on how
                        // precisely to make use of the elevation.
                        //
                        // For example, imagine B=² and we are
                        // assembling this program:
                        //
                        //  X-> B TSD ...
                        //  Y->  ᴮTSD ...
                        //
                        // What configuration value is to be used?
                        // For the first insruction (at X), the
                        // configuration value is clearly 2.  But for
                        // the second (at Y), the value of B is
                        // (2<<30), which is out of range for a
                        // configuration value.
                        //
                        // Similarly, what if B is defined B=(4ᴰ) and D=1?
                        //
                        // Related questions arise around how we
                        // establish what contexts a symbol has been
                        // used in.
                        //
                        // TODO: figure out how this should be interpreted.
                        if elevation != &Script::Normal {
                            event!(
                                Level::WARN,
                                "superscript/subscript inside assignment value may not be correctly handled"
                            );
                        }
                        self.final_lookup_helper(symbol_name, op)
                    }
                },
                SymbolDefinition::Undefined(context_union) => {
                    if context_union.includes(&op.context) {
                        Err(SymbolLookupFailure::from((
                            name.clone(),
                            SymbolLookupFailureKind::MissingDefault,
                        )))
                    } else {
                        should_have_seen(op)
                    }
                }
            },
            None => should_have_seen(op),
        }
    }

    pub(crate) fn lookup_final(
        &self,
        name: &SymbolName,
        context: &SymbolContext,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let mut op = FinalLookupOperation::new(name.clone(), *context);
        self.final_lookup_helper(name, &mut op)
    }
}

impl SymbolLookup for SymbolTable {
    type Error = SymbolLookupFailure;

    fn lookup(
        &mut self,
        name: &SymbolName,
        context: &SymbolContext,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let mut op = FinalLookupOperation::new(name.clone(), *context);
        self.final_lookup_helper(name, &mut op)
    }
}
