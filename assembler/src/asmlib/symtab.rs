use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt::{self, Debug, Display, Formatter};

use base::prelude::*;

use super::ast::{EqualityValue, Origin};
use super::collections::OneOrMore;
use super::eval::SymbolLookupFailure;
use super::memorymap::{RcAllocator, RcWordAllocationFailure, RcWordSource};
use super::source::Source;
use super::span::*;
use super::symbol::{InconsistentSymbolUse, SymbolContext, SymbolName};
use super::types::{AssemblerFailure, BlockIdentifier, ProgramError};

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

/// The rules for how symbols which have references but no explicit
/// definition are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct ImplicitSymbolTable {
    definitions: BTreeMap<SymbolName, ImplicitDefinition>,
}

impl ImplicitSymbolTable {
    pub(super) fn symbols(&self) -> impl Iterator<Item = &SymbolName> {
        self.definitions.keys()
    }

    pub(crate) fn get(&self, name: &SymbolName) -> Option<&ImplicitDefinition> {
        self.definitions.get(name)
    }

    pub(super) fn get_mut(&mut self, name: &SymbolName) -> Option<&mut ImplicitDefinition> {
        self.definitions.get_mut(name)
    }

    pub(crate) fn remove(&mut self, name: &SymbolName) -> Option<ImplicitDefinition> {
        self.definitions.remove(name)
    }

    pub(crate) fn record_usage_context(
        &mut self,
        name: SymbolName,
        context: SymbolContext,
    ) -> Result<(), InconsistentSymbolUse> {
        self.definitions
            .entry(name.clone())
            .or_insert_with(|| ImplicitDefinition::Undefined(context.clone()))
            .merge_context(&name, context.clone())
    }

    pub(super) fn record_deduced_origin_value(
        &mut self,
        name: SymbolName,
        value: Address,
        block_id: BlockIdentifier,
        span: Span,
    ) -> Result<(), InconsistentSymbolUse> {
        let context = SymbolContext::origin(block_id, Origin::Deduced(span, name.clone(), value));
        self.definitions
            .entry(name.clone())
            .or_insert_with(|| ImplicitDefinition::DefaultAssigned(value.into(), context.clone()))
            .merge_context(&name, context)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct ExplicitSymbolTable {
    definitions: BTreeMap<SymbolName, ExplicitDefinition>,
}

#[derive(Debug, Default)]
pub(crate) struct LookupOperation {
    pub(super) depends_on: HashSet<SymbolName>,
    pub(super) deps_in_order: Vec<SymbolName>,
}

// TODO: check whether we still need this at all.
impl Spanned for (&Span, &SymbolName, &ExplicitDefinition) {
    fn span(&self) -> Span {
        let r1: &Span = self.0;
        let r2: Span = self.2.span();
        assert_eq!(r1, &r2);
        r2
    }
}

impl ExplicitSymbolTable {
    pub(crate) fn new() -> ExplicitSymbolTable {
        ExplicitSymbolTable {
            definitions: Default::default(),
        }
    }

    pub(crate) fn get(&self, name: &SymbolName) -> Option<&ExplicitDefinition> {
        self.definitions.get(name)
    }

    pub(crate) fn is_defined(&self, name: &SymbolName) -> bool {
        self.definitions.contains_key(name)
    }

    pub(crate) fn define(
        &mut self,
        name: SymbolName,
        new_definition: ExplicitDefinition,
    ) -> Result<(), BadSymbolDefinition> {
        if let Some(existing) = self.definitions.get_mut(&name) {
            existing.override_with(name, new_definition)
        } else {
            self.definitions.insert(name, new_definition);
            Ok(())
        }
    }
    pub(crate) fn merge(
        &mut self,
        other: ExplicitSymbolTable,
    ) -> Result<(), OneOrMore<BadSymbolDefinition>> {
        let mut errors: Vec<BadSymbolDefinition> = Vec::new();
        for (name, def) in other.definitions.into_iter() {
            if let Err(e) = self.define(name, def) {
                errors.push(e);
            }
        }
        match OneOrMore::try_from_vec(errors) {
            Ok(errors) => Err(errors),
            Err(_) => Ok(()), // errors was empty
        }
    }
}

// TODO: do we still need this?
impl Spanned for (&Span, &SymbolName, &ImplicitDefinition) {
    fn span(&self) -> Span {
        *self.0
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

impl Spanned for TagDefinition {
    fn span(&self) -> Span {
        match self {
            TagDefinition::Unresolved { span, .. } | TagDefinition::Resolved { span, .. } => *span,
        }
    }
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

impl Spanned for ExplicitDefinition {
    fn span(&self) -> Span {
        match self {
            ExplicitDefinition::Tag(tag_definition) => tag_definition.span(),
            ExplicitDefinition::Equality(equality_value) => equality_value.span(),
            ExplicitDefinition::Origin(origin, _block_identifier) => origin.span(),
        }
    }
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

impl ExplicitDefinition {
    pub(crate) fn override_with(
        &mut self,
        name: SymbolName,
        update: ExplicitDefinition,
    ) -> Result<(), BadSymbolDefinition> {
        match (self, update) {
            (current @ ExplicitDefinition::Equality(_), new @ ExplicitDefinition::Equality(_)) => {
                // This is always OK.
                *current = new;
                Ok(())
            }
            (current, new) => {
                if current == &new {
                    Ok(()) // nothing to do.
                } else {
                    Err(BadSymbolDefinition {
                        symbol_name: name,
                        span: new.span(),
                        existing: Box::new(current.clone()),
                        proposed: Box::new(new),
                    })
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum ImplicitDefinition {
    Undefined(SymbolContext),
    DefaultAssigned(Unsigned36Bit, SymbolContext),
}

impl ImplicitDefinition {
    pub(crate) fn context(&self) -> &SymbolContext {
        match self {
            ImplicitDefinition::Undefined(context)
            | ImplicitDefinition::DefaultAssigned(_, context) => context,
        }
    }
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
pub(crate) struct BadSymbolDefinition {
    /// Signals that an origin has been inconsistently defined, or a
    /// tag has been defined in more than once place.
    pub(crate) symbol_name: SymbolName,
    pub(crate) span: Span,
    // We box the two definitions here to reduce the (direct) size
    // of the BadSymbolDefinition object itself.  Otherwise, this
    // will give rise to large disparities between the Ok() and
    // Err() variants of results that directly or indirectly
    // include BadSymbolDefinition instances.
    pub(crate) existing: Box<ExplicitDefinition>,
    pub(crate) proposed: Box<ExplicitDefinition>,
}

impl Spanned for BadSymbolDefinition {
    fn span(&self) -> Span {
        self.span
    }
}

impl Display for BadSymbolDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match (&*self.existing, &*self.proposed) {
            (ExplicitDefinition::Tag(td1), ExplicitDefinition::Tag(td2)) => {
                write!(
                    f,
                    "{0} is defined more than once, but this is not allowed for tags (tag defitions are {1} and {2})",
                    &self.symbol_name, td1, td2

                )
            }
            _ => {
                write!(f, "it is not allowed to override the symbol definition of {0} as {1} with a new definition {2}",
                       &self.symbol_name, &self.existing, &self.proposed)
            }
        }
    }
}

impl std::error::Error for BadSymbolDefinition {}

impl ImplicitDefinition {
    pub(crate) fn merge_context(
        &mut self,
        name: &SymbolName,
        context: SymbolContext,
    ) -> Result<(), InconsistentSymbolUse> {
        match self {
            ImplicitDefinition::Undefined(current) => current.merge(name, context),
            ImplicitDefinition::DefaultAssigned(value, existing_context) => {
                if &context != existing_context {
                    panic!("attempting to change the recorded usage context for {name} after a default value {value:?} has been assigned; previous context was {existing_context:?}, new context is {context:?}");
                } else {
                    Ok(())
                }
            }
        }
    }
}

pub(super) fn assign_default_rc_word_tags<R: RcAllocator>(
    implicit_symtab: &mut ImplicitSymbolTable,
    rcblock: &mut R,
    final_symbols: &mut FinalSymbolTable,
) -> Result<(), RcWordAllocationFailure> {
    for (name, def) in implicit_symtab.definitions.iter_mut() {
        if let ImplicitDefinition::Undefined(context) = def {
            if context.requires_rc_word_allocation() {
                let span: Span = *context.any_span();
                let value = Unsigned36Bit::ZERO;
                let addr =
                    rcblock.allocate(RcWordSource::DefaultAssignment(span, name.clone()), value)?;
                final_symbols.define(
                    name.clone(),
                    FinalSymbolType::Equality,
                    value.to_string(),
                    FinalSymbolDefinition::PositionIndependent(value),
                );
                *def = ImplicitDefinition::DefaultAssigned(addr.into(), context.clone());
            }
        }
    }
    Ok(())
}

pub(super) fn record_undefined_symbol_or_return_failure<'s>(
    source_file_body: &Source<'s>,
    e: SymbolLookupFailure,
    undefined_symbols: &mut BTreeMap<SymbolName, ProgramError>,
) -> Result<(), AssemblerFailure> {
    use SymbolLookupFailure::*;
    match e {
        Loop {
            span,
            deps_in_order,
            ..
        } => {
            undefined_symbols
                .entry(deps_in_order.first().clone())
                .or_insert_with(|| ProgramError::SymbolDefinitionLoop {
                    symbol_names: deps_in_order,
                    span,
                });
            Ok(())
        }
        other => Err(other
            .into_program_error()
            .into_assembler_failure(source_file_body)),
    }
}
