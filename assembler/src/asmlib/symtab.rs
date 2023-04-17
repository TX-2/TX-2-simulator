use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};

use super::ast::{Expression, SymbolName};
use base::prelude::{Address, Unsigned36Bit};

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
pub(crate) struct SymbolContext {
    // The "All members are false" context is the one in which we list
    // the values of symbols in the program listing.
    configuration: bool,
    index: bool,
    address: bool,
    origin: bool,
}

impl SymbolContext {
    fn configuration() -> SymbolContext {
        SymbolContext {
            configuration: true,
            ..SymbolContext::default()
        }
    }

    fn bits(&self) -> [bool; 4] {
        [self.configuration, self.index, self.address, self.origin]
    }

    fn includes(&self, other: &SymbolContext) -> bool {
        other
            .bits()
            .into_iter()
            .zip(self.bits().into_iter())
            .all(|(otherbit, selfbit)| selfbit || !otherbit)
    }

    fn merge(&mut self, other: SymbolContext) -> SymbolContext {
        SymbolContext {
            configuration: self.configuration || other.configuration,
            index: self.index || other.index,
            address: self.address || other.address,
            origin: self.origin || other.origin,
        }
    }

    /// Assign a default value for a symbol, using the rules from
    /// section 6-2.2 of the Users Handbook ("SYMEX DEFINITON - TAGS -
    /// EQUALITIES - AUTOMATIC ASSIGNMENT").
    fn default_value(&self) -> Unsigned36Bit {
        if self.origin {
            unreachable!("block origins should already have been assigned")
        }
        match (self.configuration, self.index, self.address) {
            (true, _, _) => Unsigned36Bit::ZERO,
            (false, true, _) => {
                // Should allocate the lowest unused X-register, but this is not yet implemented.
                unimplemented!("should assign an index register here")
            }
            (false, false, true) => {
                // Should assign an RC-word.
                unimplemented!("should assign an RC-word here")
            }
            (false, false, false) => {
                unreachable!(
                    "request for default value of symbol for which we have seen no references"
                )
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolDefinition {
    Tag { block: usize, offset: usize },
    Origin(Address),
    Equality(Expression),
    Undefined(SymbolContext),
}

impl SymbolDefinition {
    fn merge_context(&mut self, context: SymbolContext) {
        if let SymbolDefinition::Undefined(current) = self {
            current.merge(context);
        }
    }
}

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug, Default)]
pub(crate) struct SymbolTable {
    definitions: BTreeMap<SymbolName, SymbolDefinition>,
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

#[derive(Debug)]
pub(crate) enum SymbolLookupFailure {
    Loop {
        target: SymbolName,
        deps_in_order: Vec<SymbolName>,
    },
}

impl std::error::Error for SymbolLookupFailure {}

impl Display for SymbolLookupFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
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
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        true
    }

    pub(crate) fn define(&mut self, name: SymbolName, definition: SymbolDefinition) {
        self.definitions.insert(name, definition);
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
        let should_have_seen = |name: &SymbolName| {
            panic!("final symbol lookup of symbol '{name}' happened in an evaluation context which was not previously returned by SourceFile::global_symbol_references()");
        };
        match self.definitions.get(name) {
            Some(def) => match def {
                SymbolDefinition::Tag {
                    block: _,
                    offset: _,
                } => todo!(),
                SymbolDefinition::Origin(address) => {
                    let (physical, mark) = address.split();
                    if mark {
                        panic!("origin addresses should not be indirect, this should have been rejected");
                    }
                    Ok(physical.into())
                }
                SymbolDefinition::Equality(expression) => match expression {
                    Expression::Literal(literal) => Ok(literal.value()),
                },
                SymbolDefinition::Undefined(context_union) => {
                    if context_union.includes(&op.context) {
                        Ok(context_union.default_value())
                    } else {
                        should_have_seen(&op.target)
                    }
                }
            },
            None => should_have_seen(&op.target),
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

    pub(crate) fn list(&self) -> Result<Vec<(SymbolName, Unsigned36Bit)>, SymbolLookupFailure> {
        let result: Vec<(SymbolName, Unsigned36Bit)> = self
            .definitions
            .iter()
            .filter_map(|(name, def)| match def {
                SymbolDefinition::Equality(Expression::Literal(literal)) => {
                    Some((name.clone(), literal.value()))
                }
                _ => None, // only equalities are listed.
            })
            .collect();
        Ok(result)
    }
}
