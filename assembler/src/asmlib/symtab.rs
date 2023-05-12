use std::collections::HashMap;

use base::prelude::*;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use tracing::{event, Level};

use base::{
    charset::Script,
    prelude::{Address, Unsigned36Bit},
};

use super::ast::Expression;
use super::symbol::SymbolName;
use super::types::offset_from_origin;

#[derive(Debug, PartialEq, Eq)]
pub enum SymbolLookupFailure {
    Undefined(SymbolName),
    Inconsistent {
        symbol: SymbolName,
        msg: String,
    },
    Loop {
        target: SymbolName,
        deps_in_order: Vec<SymbolName>,
    },
    RanOutOfIndexRegisters(SymbolName),
    RcBlockTooLarge,
    BlockTooLarge {
        block_number: usize,
        block_origin: Address,
        offset: usize,
    },
}

impl SymbolLookupFailure {
    pub(crate) fn symbol_name(&self) -> &SymbolName {
        match self {
            SymbolLookupFailure::Undefined(n) => n,
            SymbolLookupFailure::Inconsistent { symbol, msg: _ } => symbol,
            SymbolLookupFailure::Loop {
                target,
                deps_in_order: _,
            } => target,
            SymbolLookupFailure::RanOutOfIndexRegisters(n) => n,
            SymbolLookupFailure::RcBlockTooLarge => todo!(),
            SymbolLookupFailure::BlockTooLarge { .. } => todo!(),
        }
    }
}

impl std::error::Error for SymbolLookupFailure {}

/// Instances of Infallible cannot be created as it has no variants.
/// When the never type (`!`) is stabilised, we should use that
/// instead.
pub(crate) enum Infallible {}

pub(crate) trait SymbolLookup {
    type Error;
    fn lookup(
        &mut self,
        name: &SymbolName,
        context: &SymbolContext,
    ) -> Result<Unsigned36Bit, Self::Error>;
}

//#[derive(Debug, PartialEq, Eq, Hash)]
//pub(crate) enum SymexContext {
//    Configuration = 1,
//    Index = 2,
//    Address = 4,
//    Origin = 8,
//    Tag = 16,
//}
//
//impl From<Script> for SymexContext {
//    fn from(script: Script) -> SymexContext {
//        match script {
//            Script::Super => SymexContext::Configuration,
//            Script::Sub => SymexContext::Index,
//            Script::Normal => SymexContext::Address,
//        }
//    }
//}
//
//#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
//struct SymexContexts(u8);
//
//impl SymexContexts {
//    fn bitmask(c: SymexContext) -> u8 {
//        c as u8
//    }
//
//    fn add(&mut self, c: SymexContext) {
//        self.0 |= SymexContexts::bitmask(c)
//    }
//
//    fn contains(&self, c: SymexContext) -> bool {
//        if self.0 & SymexContexts::bitmask(c) == 0 {
//            false
//        } else {
//            true
//        }
//    }
//
//    fn contains_only(&self, c: SymexContext) -> bool {
//        let mask = SymexContexts::bitmask(c);
//        (self.0 & mask) == mask
//    }
//}
//
//impl From<SymexContext> for SymexContexts {
//    fn from(c: SymexContext) -> SymexContexts {
//        SymexContexts(c as u8)
//    }
//}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolUse {
    Reference(SymbolContext),
    Definition(SymbolDefinition),
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum SymbolContextMergeError {
    ConflictingOrigin(usize, usize),
}

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
pub(crate) struct SymbolContext {
    // The "All members are false" context is the one in which we list
    // the values of symbols in the program listing.
    configuration: bool,
    index: bool,
    address: bool,
    origin_of_block: Option<usize>,
}

impl SymbolContext {
    fn bits(&self) -> [bool; 4] {
        [
            self.configuration,
            self.index,
            self.address,
            self.origin_of_block.is_some(),
        ]
    }

    pub(crate) fn is_origin(&self) -> bool {
        self.origin_of_block.is_some()
    }

    pub(crate) fn is_origin_only(&self) -> bool {
        self.is_origin() && !(self.configuration || self.index || self.address)
    }

    fn includes(&self, other: &SymbolContext) -> bool {
        other
            .bits()
            .into_iter()
            .zip(self.bits().into_iter())
            .all(|(otherbit, selfbit)| selfbit || !otherbit)
    }

    fn merge(&mut self, other: SymbolContext) -> Result<SymbolContext, SymbolContextMergeError> {
        let previous = self.clone();
        let origin = match (self.origin_of_block, other.origin_of_block) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x),
            (Some(x), Some(y)) => {
                if x == y {
                    Some(x)
                } else {
                    return Err(SymbolContextMergeError::ConflictingOrigin(x, y));
                }
            }
        };
        let result = SymbolContext {
            configuration: self.configuration || other.configuration,
            index: self.index || other.index,
            address: self.address || other.address,
            origin_of_block: origin,
        };
        println!("merged {previous:?} with {other:?} yielding {result:?}");
        *self = result;
        Ok(result)
    }
}

/// Assign a default value for a symbol, using the rules from
/// section 6-2.2 of the Users Handbook ("SYMEX DEFINITON - TAGS -
/// EQUALITIES - AUTOMATIC ASSIGNMENT").
fn get_default_symbol_value(
    name: &SymbolName,
    contexts_used: SymbolContext,
    program_words: Unsigned18Bit,
    rc_block: &mut Vec<Unsigned36Bit>,
    index_registers_used: &mut Unsigned6Bit,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    if contexts_used.origin_of_block.is_some() {
        if contexts_used.is_origin_only() {
            Ok(program_words.into())
        } else {
            Err(SymbolLookupFailure::Inconsistent {
                symbol: name.clone(),
                msg: format!(
                    "symbol '{}' was used in both origin and also other contexts",
                    name
                ),
            })
        }
    } else {
        match (
            contexts_used.configuration,
            contexts_used.index,
            contexts_used.address,
        ) {
            (false, false, false) => unreachable!(),
            (true, _, _) => Ok(Unsigned36Bit::ZERO), // configuration (perhaps in combo with others)
            (false, true, _) => {
                // Index but not also configuration. Assign the next
                // index register.  This count start at 0, but we
                // Can't assign X0, so we increment first (as X0 is
                // always 0 and we can't assign it).
                match index_registers_used.checked_add(u6!(1)) {
                    Some(n) => {
                        *index_registers_used = n;
                        return Ok(n.into());
                    }
                    None => {
                        return Err(SymbolLookupFailure::RanOutOfIndexRegisters(name.clone()));
                    }
                }
            }
            (false, false, true) => {
                // address only, assign the next RC word.
                Unsigned18Bit::try_from(rc_block.len())
                    .ok()
                    .map(|len| program_words.checked_add(len))
                    .flatten()
                    .map(|rc_word_addr| {
                        rc_block.push(Unsigned36Bit::ZERO);
                        Ok(rc_word_addr.into())
                    })
                    .unwrap_or(Err(SymbolLookupFailure::RcBlockTooLarge))
            }
        }
    }
}

impl From<&Script> for SymbolContext {
    fn from(elevation: &Script) -> SymbolContext {
        let (configuration, index, address) = match elevation {
            Script::Super => (true, false, false),
            Script::Sub => (false, true, false),
            Script::Normal => (false, false, true),
        };
        SymbolContext {
            configuration,
            index,
            address,
            origin_of_block: None,
        }
    }
}

impl From<Script> for SymbolContext {
    fn from(elevation: Script) -> SymbolContext {
        SymbolContext::from(&elevation)
    }
}

#[derive(PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Tag { block: usize, offset: usize },
    Equality(Expression),
    Undefined(SymbolContext),
}

impl Debug for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Tag { block, offset } => {
                write!(f, "Tag {{block:{block}, offset:{offset}}}")
            }
            SymbolDefinition::Equality(expr) => f.debug_tuple("Equality").field(expr).finish(),
            SymbolDefinition::Undefined(context) => {
                f.debug_tuple("Undefined").field(context).finish()
            }
        }
    }
}

impl Display for SymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolDefinition::Tag { block, offset } => {
                write!(f, "tag at offset {offset} in block {block}")
            }
            SymbolDefinition::Equality(expression) => {
                write!(f, "assignment with value {expression}")
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
    fn merge_context(&mut self, context: SymbolContext) {
        if let SymbolDefinition::Undefined(current) = self {
            match current.merge(context) {
                Ok(_) => (),
                Err(e) => {
                    panic!("cannot have an origin block number conflict if one of the merge sides has no block number: {e:?}")
                }
            }
        }
    }

    fn override_with(&mut self, update: SymbolDefinition) -> Result<(), BadSymbolDefinition> {
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
                    dbg!(&current);
                    dbg!(&new);
                    Err(BadSymbolDefinition::Incompatible(current.clone(), new))
                }
            }
        }
    }
}

/// FinalSymbolTable has final values for all identifiers.
#[derive(Debug, Default)]
pub(crate) struct FinalSymbolTable {
    entries: HashMap<SymbolName, Unsigned36Bit>,
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
}

impl SymbolLookup for FinalSymbolTable {
    type Error = Infallible;

    fn lookup(
        &mut self,
        name: &SymbolName,
        _: &SymbolContext,
    ) -> Result<Unsigned36Bit, Self::Error> {
        Ok(self.entries[name])
    }
}

pub(crate) fn finalise_symbol_table<'a, I>(
    t: SymbolTable,
    symbols_in_program_order: I,
    program_words: Unsigned18Bit,
    rc_block: &mut Vec<Unsigned36Bit>,
    index_registers_used: &mut Unsigned6Bit,
) -> Result<FinalSymbolTable, SymbolLookupFailure>
where
    I: Iterator<Item = &'a SymbolName>,
{
    let mut finalized_entries: HashMap<SymbolName, Unsigned36Bit> = HashMap::new();
    for symbol_name in symbols_in_program_order {
        if finalized_entries.contains_key(symbol_name) {
            panic!("symbol {symbol_name} occurs twice in symbols_in_program_order");
        }
        match t.get(symbol_name) {
            Some(SymbolDefinition::Equality(Expression::Literal(value))) => {
                finalized_entries.insert(symbol_name.clone(), value.value());
            }
            Some(SymbolDefinition::Equality(expression)) => {
                unimplemented!("need to evaluate expression {expression:?}")
            }
            Some(SymbolDefinition::Tag {
                block,
                offset: block_offset,
            }) => match t.block_origins.get(&*block) {
                Some(block_address) => {
                    // TODO: factor this out.
                    let (physical_block_start, _) = block_address.split();
                    match Unsigned18Bit::try_from(*block_offset) {
                        Ok(offset) => match physical_block_start.checked_add(offset) {
                            Some(physical) => {
                                finalized_entries.insert(symbol_name.clone(), physical.into());
                            }
                            None => {
                                return Err(SymbolLookupFailure::BlockTooLarge {
                                    block_number: *block,
                                    block_origin: *block_address,
                                    offset: *block_offset,
                                });
                            }
                        },
                        Err(_) => {
                            return Err(SymbolLookupFailure::BlockTooLarge {
                                block_number: *block,
                                block_origin: *block_address,
                                offset: *block_offset,
                            });
                        }
                    }
                }
                None => {
                    panic!("symbol name {symbol_name:?} refers to offset {block_offset} in block {block} but there is no block {block}.");
                }
            },
            Some(SymbolDefinition::Undefined(use_contexts)) => {
                // Not already defined, so we need to assign a default.
                match get_default_symbol_value(
                    symbol_name,
                    *use_contexts,
                    program_words,
                    rc_block,
                    index_registers_used,
                ) {
                    Ok(assigned) => {
                        finalized_entries.insert(symbol_name.clone(), assigned);
                    }
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
            None => {
                unreachable!()
            }
        }
    }
    Ok(FinalSymbolTable {
        entries: finalized_entries,
    })
}

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug, Default)]
pub(crate) struct SymbolTable {
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
        match self {
            SymbolLookupFailure::Undefined(name) => {
                write!(f, "symbol {name} is not defined")
            }
            SymbolLookupFailure::RanOutOfIndexRegisters(name) => {
                write!(f, "there are not enough index registers to assign one as the default for the symbol {name}")
            }
            SymbolLookupFailure::RcBlockTooLarge => f.write_str("RC block is too large"),
            SymbolLookupFailure::BlockTooLarge {
                block_number,
                block_origin,
                offset,
            } => {
                write!(f, "program block {block_number} is too large; offset {offset} from block start {block_origin} does not fit in physical memory")
            }
            SymbolLookupFailure::Inconsistent { symbol: _, msg } => f.write_str(msg.as_str()),
            SymbolLookupFailure::Loop {
                target,
                deps_in_order,
            } => {
                let names: Vec<String> = deps_in_order.iter().map(|dep| dep.to_string()).collect();
                write!(
                    f,
                    "definition of symbol {} has a dependency loop ({})",
                    target,
                    names.join("->")
                )
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
            existing.override_with(new_definition)
        } else {
            self.definitions.insert(name, new_definition);
            Ok(())
        }
    }

    pub(crate) fn record_block_origin(&mut self, block_number: usize, address: Address) {
        self.block_origins.insert(block_number, address);
    }

    pub(crate) fn record_usage_context(&mut self, name: SymbolName, context: SymbolContext) {
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
            return Err(SymbolLookupFailure::Loop {
                target: op.target.clone(),
                deps_in_order: op.deps_in_order.to_vec(),
            });
        }
        let should_have_seen = |op: &FinalLookupOperation| {
            panic!("final symbol lookup of symbol '{}' happened in an evaluation context which was not previously returned by SourceFile::global_symbol_references(): {:?}", op.target, op);
        };
        match self.definitions.get(name) {
            Some(def) => match def {
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
                    Expression::Symbol(elevation, symbol_name) => {
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
                        panic!("SymbolTable::final_lookup_helper: final value for symbol {name} should have been assigned");
                    } else {
                        should_have_seen(&op)
                    }
                }
            },
            None => should_have_seen(&op),
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
