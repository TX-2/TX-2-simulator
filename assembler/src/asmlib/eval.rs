use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Shl;

use tracing::{event, Level};

use base::{
    charset::Script,
    prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit},
    subword,
};

use super::ast::*;
use super::collections::OneOrMore;
use super::listing::{Listing, ListingLine};
use super::span::*;
use super::symbol::{ConfigUse, IndexUse, OriginUse, SymbolName};

use super::types::{
    offset_from_origin, AssemblerFailure, BlockIdentifier, MachineLimitExceededFailure,
    ProgramError, RcWordSource,
};
use crate::symbol::SymbolContext;
use crate::symtab::{
    BlockPosition, ExplicitDefinition, ExplicitSymbolTable, FinalSymbolDefinition,
    FinalSymbolTable, FinalSymbolType, ImplicitDefinition, ImplicitSymbolTable,
    IndexRegisterAssigner, LookupOperation, MemoryMap,
};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum LookupTarget {
    Symbol(SymbolName, Span),
    MemRef(MemoryReference),
}

impl From<(SymbolName, Span)> for LookupTarget {
    fn from((sym, span): (SymbolName, Span)) -> LookupTarget {
        LookupTarget::Symbol(sym, span)
    }
}

impl From<MemoryReference> for LookupTarget {
    fn from(r: MemoryReference) -> LookupTarget {
        LookupTarget::MemRef(r)
    }
}

impl Spanned for LookupTarget {
    fn span(&self) -> Span {
        match self {
            LookupTarget::MemRef(r) => r.span(),
            LookupTarget::Symbol(_, span) => *span,
        }
    }
}

impl Display for LookupTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            LookupTarget::Symbol(name, _) => {
                write!(f, "symbol {name}")
            }
            LookupTarget::MemRef(MemoryReference {
                block_id,
                block_offset: _,
                span: _,
            }) => {
                write!(f, "{block_id}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct MemoryReference {
    pub(crate) block_id: BlockIdentifier,
    pub(crate) block_offset: usize,
    pub(crate) span: Span,
}

impl Spanned for MemoryReference {
    fn span(&self) -> Span {
        self.span
    }
}

// SymbolValue is the result of a symbol table lookup.
//
// TODO: in some places we want to do further processing of the
// looked-up result in ways that require us to specify a span.  The
// span of interest will usually be the span at which the symbol was
// actually defined, so we should also return that in SymbolValue.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolValue {
    Final(Unsigned36Bit),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SymbolLookupFailure {
    Loop {
        span: Span,
        deps_in_order: OneOrMore<SymbolName>,
    },
    BlockTooLarge(Span, MachineLimitExceededFailure),
    FailedToAssignIndexRegister(Span, SymbolName),
    HereIsNotAllowedHere(Span),
}

impl Spanned for SymbolLookupFailure {
    fn span(&self) -> Span {
        match self {
            SymbolLookupFailure::HereIsNotAllowedHere(span)
            | SymbolLookupFailure::FailedToAssignIndexRegister(span, _)
            | SymbolLookupFailure::Loop { span, .. }
            | SymbolLookupFailure::BlockTooLarge(span, _) => *span,
        }
    }
}

impl Display for SymbolLookupFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use SymbolLookupFailure::*;
        match self {
            Loop {
                deps_in_order,
                span: _,
            } => {
                let names: Vec<String> = deps_in_order.iter().map(|dep| dep.to_string()).collect();
                write!(
                    f,
                    "definition of {} has a dependency loop ({})",
                    deps_in_order.first(),
                    names.join("->")
                )
            }
            FailedToAssignIndexRegister(_, name) => {
                write!(f, "unable to assign index register as the default value for symbol {name} because there are not enough index registers")
            }
            BlockTooLarge(_span, mle) => {
                write!(f, "program block too large: {mle}")
            }
            HereIsNotAllowedHere(_) => {
                f.write_str("'#' (representing the current address) is not allowed here")
            }
        }
    }
}

impl SymbolLookupFailure {
    pub(crate) fn into_program_error(self) -> ProgramError {
        match self {
            SymbolLookupFailure::FailedToAssignIndexRegister(span, name) => {
                ProgramError::FailedToAssignIndexRegister(span, name)
            }
            SymbolLookupFailure::BlockTooLarge(span, mle) => ProgramError::BlockTooLong(span, mle),
            SymbolLookupFailure::Loop {
                deps_in_order,
                span,
            } => ProgramError::SymbolDefinitionLoop {
                symbol_names: deps_in_order,
                span,
            },
            SymbolLookupFailure::HereIsNotAllowedHere(span) => ProgramError::SyntaxError {
                span,
                msg: "# is not allowed in this context".to_string(),
            },
        }
    }
}

impl std::error::Error for SymbolLookupFailure {}

/// HereValue specifies the value used for '#'
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum HereValue {
    /// '#' refers to an address
    Address(Address),
    /// NotAllowed is for when '#' is not allowed (this is used
    /// when evaluating an origin).
    NotAllowed,
}

impl HereValue {
    pub(crate) fn get_address(&self, span: &Span) -> Result<Address, SymbolLookupFailure> {
        match self {
            HereValue::Address(addr) => Ok(*addr),
            HereValue::NotAllowed => Err(SymbolLookupFailure::HereIsNotAllowedHere(*span)),
        }
    }
}

/// Assign a default value for a symbol, using the rules from
/// section 6-2.2 of the Users Handbook ("SYMEX DEFINITON - TAGS -
/// EQUALITIES - AUTOMATIC ASSIGNMENT").
fn assign_default_value(
    index_register_assigner: &mut IndexRegisterAssigner,
    name: &SymbolName,
    contexts_used: &SymbolContext,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    event!(
        Level::DEBUG,
        "assigning default value for {name} used in contexts {contexts_used:?}"
    );
    let span: Span = *contexts_used.any_span();
    use ConfigUse::*;
    use IndexUse::*;
    match &contexts_used.origin {
        OriginUse::IncludesOrigin(_block, _origin) => {
            unreachable!("assign_default_value should not be called for origin speicifations; attempted to assign default value for {name} (used in contexts: {contexts_used:?}")
        }
        OriginUse::NotOrigin { config, index } => match (config, index) {
            (NotConfig, NotIndex) => {
                if contexts_used.is_address() {
                    // Values which refer to addresses (and which
                    // therefore should point to a zero-initialised
                    // RC-word) should already have a default value
                    // assigned.
                    unreachable!("default assignments for address-context symexes should be assigned before evaluation starts")
                } else {
                    unreachable!("attempted to assign a default value for a symbol {name} which appears not to be used in any context at all")
                }
            }
            (IncludesConfig, _) => Ok(Unsigned36Bit::ZERO),
            (NotConfig, IncludesIndex) => {
                // Index but not also configuration. Assign the next
                // index register.
                match index_register_assigner.assign_index_register() {
                    Some(n) => Ok(n.into()),
                    None => Err(SymbolLookupFailure::FailedToAssignIndexRegister(
                        span,
                        name.clone(),
                    )),
                }
            }
        },
    }
}

/// The word-value evaluation process does not modify the memory map
/// or the symbol table (so those structs are shared references).  But
/// it does modify the "implicit symbol table" which records
/// default-assignments for symbols that don't have an explicit
/// definition.  It can also update RC-words in-place.
#[derive(Debug)]
pub(crate) struct EvaluationContext<'s, R: RcUpdater> {
    pub(crate) here: HereValue,
    pub(crate) explicit_symtab: &'s ExplicitSymbolTable,
    pub(crate) implicit_symtab: &'s mut ImplicitSymbolTable,
    pub(crate) index_register_assigner: &'s mut IndexRegisterAssigner,
    pub(crate) memory_map: &'s MemoryMap,
    pub(crate) rc_updater: &'s mut R,
    pub(crate) lookup_operation: LookupOperation,
}

impl<R: RcUpdater> EvaluationContext<'_, R> {
    pub(super) fn fetch_or_assign_default(
        &mut self,
        name: &SymbolName,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let existing_def: &mut ImplicitDefinition = match self.implicit_symtab.get_mut(name) {
            Some(def) => def,
            None => {
                // In order to assign a default value for a symbol, we
                // need to know the contexts in which it is used (see
                // assign_default_value()) and so not having recorded
                // that information is an internal error.
                panic!("attempted to assign a default value for an entirely unknown symbol {name}");
            }
        };

        match existing_def {
            ImplicitDefinition::DefaultAssigned(value, _) => Ok(*value),
            ImplicitDefinition::Undefined(_) => {
                let context: SymbolContext = existing_def.context().clone();
                let span: Span = *context.any_span();

                // Special case assigning origin addresses, because
                // the rest of the work is carried out with
                // index_register_assigner only.
                if let Some((block_identifier, _origin)) = context.get_origin() {
                    if let Some(block_position) = self.memory_map.get(block_identifier).cloned() {
                        // If we simply try to pass block_position to
                        // evaluate() we will loop and diagnose this
                        // as an undefined symbol.  While the symbol
                        // has no definition via assignment, we can
                        // determine the position of the block by
                        // appending it to the previous block.  So we
                        // evaluate the block's position as if it had
                        // no origin specification.
                        let pos_with_unspecified_origin: BlockPosition = BlockPosition {
                            origin: None,
                            ..block_position
                        };
                        let what: (&BlockIdentifier, &BlockPosition) =
                            (block_identifier, &pos_with_unspecified_origin);
                        match what.evaluate(self) {
                            Ok(value) => {
                                let address: Address = subword::right_half(value).into();
                                match self.implicit_symtab.record_deduced_origin_value(
                                    name.clone(),
                                    address,
                                    *block_identifier,
                                    span,
                                ) {
                                    Ok(()) => Ok(value),
                                    Err(e) => {
                                        panic!("got a bad symbol definition error ({e}) on a previously undefined origin symbol");
                                    }
                                }
                            }
                            Err(e) => Err(e),
                        }
                    } else {
                        unreachable!("symbol {name} was used as an origin for block {block_identifier} but this is not a known block");
                    }
                } else {
                    match assign_default_value(self.index_register_assigner, name, &context) {
                        Ok(value) => {
                            *existing_def = ImplicitDefinition::DefaultAssigned(value, context);
                            Ok(value)
                        }
                        Err(e) => {
                            // TODO: this should be an error at the time
                            // the usage was recorded.
                            Err(e)
                        }
                    }
                }
            }
        }
    }
}

impl<R: RcUpdater> EvaluationContext<'_, R> {
    pub(super) fn for_target_address<F, T>(&mut self, new_here: HereValue, mut closure: F) -> T
    where
        F: FnMut(&mut EvaluationContext<'_, R>) -> T,
    {
        let old_here = self.here;
        self.here = new_here;
        let output = closure(self);
        self.here = old_here;
        output
    }
}

pub(super) trait Evaluate: Spanned {
    // By separating the RcUpdater and RcAllocator traits we ensure
    // that evaluation cannot allocate more RC words.
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure>;
}

#[derive(Debug, Default, Clone)]
pub(crate) struct RcBlock {
    pub(crate) address: Address,
    pub(crate) words: Vec<(RcWordSource, Unsigned36Bit)>,
}

impl RcBlock {
    fn end(&self) -> Option<Address> {
        match Unsigned18Bit::try_from(self.words.len()) {
            Ok(offset) => Some(self.address.index_by(offset)),
            Err(_) => None,
        }
    }
}

impl RcAllocator for RcBlock {
    fn allocate(
        &mut self,
        source: RcWordSource,
        value: Unsigned36Bit,
    ) -> Result<Address, RcWordAllocationFailure> {
        if let Some(addr) = self.end() {
            self.words.push((source, value));
            Ok(addr)
        } else {
            Err(RcWordAllocationFailure::RcBlockTooBig {
                source,
                rc_block_len: self.words.len(),
            })
        }
    }
}

impl RcUpdater for RcBlock {
    fn update(&mut self, address: Address, value: Unsigned36Bit) {
        if address < self.address {
            panic!(
                "out of range access to address {address} of RC-block starting at {}",
                self.address
            );
        }
        match Unsigned18Bit::from(address).checked_sub(Unsigned18Bit::from(self.address)) {
            Some(offset) => match self.words.get_mut(usize::from(offset)) {
                Some((_source, spot)) => {
                    *spot = value;
                }
                None => {
                    panic!(
                        "out of range access to offset {offset} of RC-block having length {}",
                        self.words.len()
                    );
                }
            },
            None => {
                // The checks above should ensure that address >= self.address.
                panic!(
                    "inconsistent checks; {address:o} should be greater than {:o}",
                    self.address
                );
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn make_empty_rc_block_for_test(location: Address) -> RcBlock {
    RcBlock {
        address: location,
        words: Vec::new(),
    }
}

fn final_lookup_helper_body<R: RcUpdater>(
    ctx: &mut EvaluationContext<R>,
    name: &SymbolName,
    span: Span,
) -> Result<SymbolValue, SymbolLookupFailure> {
    if let Some(def) = ctx.explicit_symtab.get(name) {
        let what: (&Span, &SymbolName, &ExplicitDefinition) = (&span, name, def);
        what.evaluate(ctx).map(SymbolValue::Final)
    } else {
        Ok(SymbolValue::Final(ctx.fetch_or_assign_default(name)?))
    }
}

pub(super) fn lookup_with_op<R: RcUpdater>(
    ctx: &mut EvaluationContext<R>,
    name: &SymbolName,
    span: Span,
) -> Result<SymbolValue, SymbolLookupFailure> {
    ctx.lookup_operation.deps_in_order.push(name.clone());
    if !ctx.lookup_operation.depends_on.insert(name.clone()) {
        // `name` was already in `depends_on`; in other words,
        // we have a loop.
        match OneOrMore::try_from_vec(ctx.lookup_operation.deps_in_order.clone()) {
            Ok(deps_in_order) => {
                return Err(SymbolLookupFailure::Loop {
                    span,
                    deps_in_order,
                });
            }
            Err(_) => {
                panic!("we know deps_in_order is non-empty because we just appended an item to it");
            }
        }
    }
    let result = final_lookup_helper_body(ctx, name, span);
    ctx.lookup_operation.deps_in_order.pop();
    ctx.lookup_operation.depends_on.remove(name);
    result
}

pub(crate) fn symbol_name_lookup<R: RcUpdater>(
    name: &SymbolName,
    elevation: Script,
    span: Span,
    ctx: &mut EvaluationContext<R>,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    match lookup_with_op(ctx, name, span) {
        Ok(SymbolValue::Final(value)) => Ok(value),
        Err(e) => Err(e),
    }
    .map(|value| value.shl(elevation.shift()))
}

fn record_undefined_symbol_or_return_failure(
    source_file_body: &str,
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

#[allow(clippy::too_many_arguments)]
pub(super) fn extract_final_equalities<R: RcUpdater>(
    equalities: &[Equality],
    body: &str,
    explicit_symbols: &ExplicitSymbolTable,
    implicit_symbols: &mut ImplicitSymbolTable,
    memory_map: &MemoryMap,
    index_register_assigner: &mut IndexRegisterAssigner,
    rc_allocator: &mut R,
    final_symbols: &mut FinalSymbolTable,
    bad_symbol_definitions: &mut BTreeMap<SymbolName, ProgramError>,
) -> Result<(), AssemblerFailure> {
    for eq in equalities {
        let mut ctx = EvaluationContext {
            explicit_symtab: explicit_symbols,
            implicit_symtab: implicit_symbols,
            memory_map,
            here: HereValue::NotAllowed,
            index_register_assigner,
            rc_updater: rc_allocator,
            lookup_operation: Default::default(),
        };

        match eq.value.evaluate(&mut ctx) {
            Ok(value) => {
                final_symbols.define(
                    eq.name.clone(),
                    FinalSymbolType::Equality,
                    extract_span(body, &eq.span).trim().to_string(),
                    FinalSymbolDefinition::PositionIndependent(value),
                );
            }
            Err(SymbolLookupFailure::HereIsNotAllowedHere(_)) => {
                // The value of this equality would depend on the
                // address at which it is evaluated, so it has no
                // single final value.  This is OK.
                final_symbols.define(
                    eq.name.clone(),
                    FinalSymbolType::Equality,
                    extract_span(body, &eq.span).trim().to_string(),
                    FinalSymbolDefinition::PositionDependent,
                );
            }
            Err(e) => {
                record_undefined_symbol_or_return_failure(body, e, bad_symbol_definitions)?;
            }
        }
    }
    Ok(())
}

impl LocatedBlock {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_binary_block<R: RcUpdater>(
        &self,
        location: Address,
        explicit_symtab: &ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        memory_map: &MemoryMap,
        index_register_assigner: &mut IndexRegisterAssigner,
        rc_allocator: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &str,
        listing: &mut Listing,
        undefined_symbols: &mut BTreeMap<SymbolName, ProgramError>,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let word_count: usize = self
            .sequences
            .iter()
            .map(|seq| usize::from(seq.emitted_word_count()))
            .sum();
        let mut result: Vec<Unsigned36Bit> = Vec::with_capacity(word_count);
        for seq in self.sequences.iter() {
            let current_block_len: Unsigned18Bit = result
                .len()
                .try_into()
                .expect("assembled code block should fit within physical memory");
            let mut words: Vec<Unsigned36Bit> = seq.build_binary_block(
                location,
                current_block_len,
                explicit_symtab,
                implicit_symtab,
                memory_map,
                index_register_assigner,
                rc_allocator,
                final_symbols,
                body,
                listing,
                undefined_symbols,
            )?;
            result.append(&mut words);
        }
        Ok(result)
    }
}

impl InstructionSequence {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_binary_block<R: RcUpdater>(
        &self,
        location: Address,
        start_offset: Unsigned18Bit,
        explicit_symtab: &ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        memory_map: &MemoryMap,
        index_register_assigner: &mut IndexRegisterAssigner,
        rc_allocator: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &str,
        listing: &mut Listing,
        bad_symbol_definitions: &mut BTreeMap<SymbolName, ProgramError>,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let mut words: Vec<Unsigned36Bit> = Vec::with_capacity(self.emitted_word_count().into());
        for (offset, instruction) in self.iter().enumerate() {
            let offset: Unsigned18Bit = Unsigned18Bit::try_from(offset)
                .ok()
                .and_then(|offset| offset.checked_add(start_offset))
                .expect("assembled code block should fit within physical memory");
            let address: Address = location.index_by(offset);
            for tag in instruction.tags.iter() {
                final_symbols.define(
                    tag.name.clone(),
                    FinalSymbolType::Tag,
                    extract_span(body, &tag.span).trim().to_string(),
                    FinalSymbolDefinition::PositionIndependent(address.into()),
                );
            }

            if self.local_symbols.is_some() {
                panic!("InstructionSequence::build_binary_block: evaluation with local symbol tables is not yet implemented");
            }
            let mut ctx = EvaluationContext {
                explicit_symtab,
                implicit_symtab,
                memory_map,
                here: HereValue::Address(address),
                index_register_assigner,
                rc_updater: rc_allocator,
                lookup_operation: Default::default(),
            };
            match instruction.evaluate(&mut ctx) {
                Ok(word) => {
                    listing.push_line(ListingLine {
                        span: Some(instruction.span),
                        rc_source: None,
                        content: Some((address, word)),
                    });
                    words.push(word);
                }
                Err(e) => {
                    record_undefined_symbol_or_return_failure(body, e, bad_symbol_definitions)?;
                }
            }
        }
        Ok(words)
    }
}

impl Spanned for (&BlockIdentifier, &BlockPosition) {
    fn span(&self) -> Span {
        self.1.span
    }
}

impl Evaluate for (&BlockIdentifier, &BlockPosition) {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        fn address_from_lower_half(x: Unsigned36Bit) -> Address {
            subword::right_half(x).into()
        }
        let (block_id, block_position) = self;
        let addr: Address = match block_position {
            BlockPosition {
                block_address: Some(address),
                ..
            } => Ok(*address),
            BlockPosition {
                block_address: None,
                origin: Some(origin),
                ..
            } => origin.evaluate(ctx).map(address_from_lower_half),
            BlockPosition {
                block_address: None,
                origin: None,
                span: block_span,
                ..
            } => {
                match block_id.previous_block() {
                    None => {
                        // This is the first block.
                        Ok(Origin::default_address())
                    }
                    Some(previous_block_id) => {
                        match ctx.memory_map.get(&previous_block_id).cloned() {
                            Some(previous_block) => {
                                let prev_addr_w: Unsigned36Bit =
                                    (&previous_block_id, &previous_block).evaluate(ctx)?;
                                let prev_addr: Address =
                                    Address::from(subword::right_half(prev_addr_w));
                                match offset_from_origin(&prev_addr, previous_block.block_size) {
                                    Ok(addr) => Ok(addr),
                                    Err(_) => Err(SymbolLookupFailure::BlockTooLarge(
                                        *block_span,
                                        MachineLimitExceededFailure::BlockTooLarge {
                                            span: *block_span,
                                            block_id: previous_block_id,
                                            offset: previous_block.block_size.into(),
                                        },
                                    )),
                                }
                            }
                            None => {
                                panic!("{previous_block_id} is missing from the block layout");
                            }
                        }
                    }
                }
            }
        }?;
        Ok(Unsigned36Bit::from(addr))
    }
}
