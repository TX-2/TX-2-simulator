use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Shl;

use tracing::{Level, event};

use base::{
    charset::Script,
    prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit},
    subword,
};
#[cfg(test)]
use base::{u18, u36};

use super::ast::*;
use super::collections::OneOrMore;
use super::memorymap::{
    BlockPosition, MemoryMap, RcAllocator, RcWordAllocationFailure, RcWordSource,
};
use super::source::Source;
use super::span::*;
#[cfg(test)]
use super::symbol::AddressUse;
use super::symbol::{ConfigUse, IndexUse, OriginUse, SymbolName};

use super::types::{AssemblerFailure, BlockIdentifier, MachineLimitExceededFailure, ProgramError};
use crate::symbol::SymbolContext;
use crate::symtab::{
    ExplicitDefinition, ExplicitSymbolTable, FinalSymbolDefinition, FinalSymbolTable,
    FinalSymbolType, ImplicitDefinition, ImplicitSymbolTable, IndexRegisterAssigner,
    LookupOperation, TagDefinition, record_undefined_symbol_or_return_failure,
};

/// We ran out of index registers when trying to perform default
/// assignment of a symbol name.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub(crate) struct ExhaustedIndexRegisters {
    span: Span,
    name: SymbolName,
}

/// We failed while evaluating the value of a word (typically, the
/// value of a word in the final assembled output).
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum EvaluationFailure {
    /// Evaluation failed because there was a loop in the definition
    /// of a symbol (i.e. in one of the equaities we needed to
    /// evaluate to determine the final result).
    SymbolDefinitionLoop {
        span: Span,
        deps_in_order: OneOrMore<SymbolName>,
    },
    /// A block of the program is too large.
    BlockTooLarge(Span, MachineLimitExceededFailure),
    /// More index values needed to be default-assigned than there are
    /// index registers in the TX-2 architecture.
    FailedToAssignIndexRegister(ExhaustedIndexRegisters),

    /// We could not evaluate something because `#` was used in a
    /// context in which it was not allowed (an origin value).
    HereIsNotAllowedHere(Span),
}

impl Spanned for EvaluationFailure {
    fn span(&self) -> Span {
        match self {
            EvaluationFailure::HereIsNotAllowedHere(span)
            | EvaluationFailure::FailedToAssignIndexRegister(ExhaustedIndexRegisters {
                span,
                ..
            })
            | EvaluationFailure::SymbolDefinitionLoop { span, .. }
            | EvaluationFailure::BlockTooLarge(span, _) => *span,
        }
    }
}

impl Display for EvaluationFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use EvaluationFailure::*;
        match self {
            SymbolDefinitionLoop {
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
            FailedToAssignIndexRegister(ExhaustedIndexRegisters { name, .. }) => {
                write!(
                    f,
                    "unable to assign index register as the default value for symbol {name} because there are not enough index registers"
                )
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

impl EvaluationFailure {
    /// Convert an instance of `EvaluationFailure` (which describes
    /// why an evaluation failed) into an instance of [`ProgramError`]
    /// (which describes why the user's program cannot be assembled).
    pub(crate) fn into_program_error(self) -> ProgramError {
        match self {
            EvaluationFailure::FailedToAssignIndexRegister(ExhaustedIndexRegisters {
                span,
                name,
            }) => ProgramError::FailedToAssignIndexRegister(span, name),
            EvaluationFailure::BlockTooLarge(span, mle) => ProgramError::BlockTooLong(span, mle),
            EvaluationFailure::SymbolDefinitionLoop {
                deps_in_order,
                span,
            } => ProgramError::SymbolDefinitionLoop {
                symbol_names: deps_in_order,
                span,
            },
            EvaluationFailure::HereIsNotAllowedHere(span) => ProgramError::SyntaxError {
                span,
                msg: "# is not allowed in this context".to_string(),
            },
        }
    }
}

impl std::error::Error for EvaluationFailure {}

/// HereValue specifies the value used for `#`.  A `#` always
/// signifies the address of the word we are trying to assemble.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum HereValue {
    /// '#' refers to an address
    Address(Address),
    /// NotAllowed is for when '#' is not allowed (this is used
    /// when evaluating an origin).
    NotAllowed,
}

impl HereValue {
    pub(crate) fn get_address(&self, span: &Span) -> Result<Address, EvaluationFailure> {
        match self {
            HereValue::Address(addr) => Ok(*addr),
            HereValue::NotAllowed => Err(EvaluationFailure::HereIsNotAllowedHere(*span)),
        }
    }
}

/// Assign a default value for a symbol, using the rules from
/// [section 6-2.2 of the Users Handbook, "SYMEX DEFINITON - TAGS - EQUALITIES - AUTOMATIC ASSIGNMENT"](https://archive.org/details/tx-2-users-handbook-nov-63/page/n157/mode/1up).
fn assign_default_value(
    index_register_assigner: &mut IndexRegisterAssigner,
    name: &SymbolName,
    contexts_used: &SymbolContext,
) -> Result<Unsigned36Bit, ExhaustedIndexRegisters> {
    event!(
        Level::DEBUG,
        "assigning default value for {name} used in contexts {contexts_used:?}"
    );
    let span: Span = *contexts_used.any_span();
    use ConfigUse::*;
    use IndexUse::*;
    match &contexts_used.origin {
        OriginUse::IncludesOrigin(_block, _origin) => {
            unreachable!(
                "assign_default_value should not be called for origin specifications; attempted to assign default value for {name} (used in contexts: {contexts_used:?}"
            )
        }
        OriginUse::NotOrigin { config, index } => match (config, index) {
            (NotConfig, NotIndex) => {
                if contexts_used.is_address() {
                    // Values which refer to addresses (and which
                    // therefore should point to a zero-initialised
                    // RC-word) should already have a default value
                    // assigned.
                    unreachable!(
                        "default assignments for address-context symexes should be assigned before evaluation starts"
                    )
                } else {
                    unreachable!(
                        "attempted to assign a default value for a symbol {name} which appears not to be used in any context at all"
                    )
                }
            }
            (IncludesConfig, _) => Ok(Unsigned36Bit::ZERO),
            (NotConfig, IncludesIndex) => {
                // Index but not also configuration. Assign the next
                // index register.
                match index_register_assigner.assign_index_register() {
                    Some(n) => Ok(n.into()),
                    None => Err(ExhaustedIndexRegisters {
                        span,
                        name: name.clone(),
                    }),
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
    /// Defines how to evaluate `#`.
    pub(crate) here: HereValue,
    /// Definitions of tags, origins and equalities.
    pub(crate) explicit_symtab: &'s ExplicitSymbolTable,
    /// Implicit symbol definitions and information about how these
    /// symbols have been used.
    pub(crate) implicit_symtab: &'s mut ImplicitSymbolTable,
    /// Assigns default values to symbols used in an index context.
    pub(crate) index_register_assigner: &'s mut IndexRegisterAssigner,
    /// Memory locations of the program's blocks.
    pub(crate) memory_map: &'s MemoryMap,
    /// Performs in-place updates of the values of RC-words.
    pub(crate) rc_updater: &'s mut R,
    /// The current lookup operation; this is used to detect loops.
    pub(crate) lookup_operation: LookupOperation,
}

impl<R: RcUpdater> EvaluationContext<'_, R> {
    /// For a symbol lacking an explicit definition, look up the
    /// default value we assigned to it, or if we didn't assign a
    /// value yet, assign a default value now and record it.
    pub(super) fn fetch_or_assign_default(
        &mut self,
        name: &SymbolName,
    ) -> Result<Unsigned36Bit, EvaluationFailure> {
        let existing_def: &mut ImplicitDefinition = match self.implicit_symtab.get_mut(name) {
            Some(def) => def,
            None => {
                // In order to assign a default value for a symbol, we
                // need to know the contexts in which it is used (see
                // [`assign_default_value()`]) and so not having
                // recorded that information is an internal error.
                panic!("attempted to assign a default value for an entirely unknown symbol {name}");
            }
        };

        match existing_def {
            ImplicitDefinition::DefaultAssigned(value, _) => Ok(*value),
            ImplicitDefinition::Undefined(_) => {
                let saved_def = existing_def.clone();
                let context: SymbolContext = existing_def.context().clone();
                let span: Span = *context.any_span();

                // Special case assigning origin addresses, because
                // the rest of the work is carried out with
                // index_register_assigner only.
                if let Some((block_identifier, _origin)) = context.get_origin() {
                    if let Some(block_position) = self.memory_map.get(block_identifier).cloned() {
                        // If we simply try to pass the block's origin
                        // to evaluate() we will loop and diagnose
                        // this as an undefined symbol.  While the
                        // symbol has no definition via assignment, we
                        // can determine the position of the block by
                        // appending it to the previous block.  So we
                        // evaluate the block's position as if it had
                        // no origin specification.
                        let position_without_origin = BlockPosition {
                            origin: None,
                            ..block_position
                        };
                        match position_without_origin.evaluate(self, ScopeIdentifier::global()) {
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
                                        dbg!(saved_def);
                                        panic!(
                                            "got a bad symbol definition error ({e:?}) on a previously undefined origin symbol {name}"
                                        );
                                    }
                                }
                            }
                            Err(e) => Err(e),
                        }
                    } else {
                        unreachable!(
                            "symbol {name} was used as an origin for block {block_identifier} but this is not a known block"
                        );
                    }
                } else {
                    match assign_default_value(self.index_register_assigner, name, &context) {
                        Ok(value) => {
                            *existing_def = ImplicitDefinition::DefaultAssigned(value, context);
                            Ok(value)
                        }
                        Err(e) => Err(EvaluationFailure::FailedToAssignIndexRegister(e)),
                    }
                }
            }
        }
    }
}

#[test]
fn can_deduce_address_of_origin_with_previous_forward_reference() {
    // GIVEN a program containing two blocks, in whicht the second block has a
    // symbolic origin and where there is a forward reference within the first
    // block to the address of the second block
    let origin_name = SymbolName::from("INPUT");
    let origin_def = Origin::Symbolic(span(2455..2461), origin_name.clone());
    const BLOCK0_SIZE: Unsigned18Bit = u18!(4);
    const BLOCK1_SIZE: Unsigned18Bit = u18!(3);
    let block0_pos = BlockPosition {
        block_identifier: BlockIdentifier::from(0),
        // The first reference to block 1 is inside block 1, so the
        // span of block1 includes the location of the first reference
        // to origin_name.  This is not a necessary setup for our test
        // scenario, but it is realistic.
        span: span(0..2400),
        origin: None,
        block_address: None,
        block_size: BLOCK0_SIZE,
    };
    let block1_pos = BlockPosition {
        block_identifier: BlockIdentifier::from(1),
        span: span(2455..2800),
        origin: None,
        block_address: None,
        block_size: BLOCK1_SIZE,
    };

    let mut implicit_symtab = ImplicitSymbolTable::default();
    implicit_symtab.load_test_definitions([(
        origin_name.clone(),
        ImplicitDefinition::Undefined(SymbolContext {
            address: AddressUse::IncludesAddress,
            origin: OriginUse::IncludesOrigin(block1_pos.block_identifier, origin_def.clone()),
            uses: [
                // The first reference is inside block 0.
                OrderableSpan(span(1188..1193)),
                // The second reference is in the origin definition of
                // block 1 (which is the thing we're trying to assign
                // a default value to).
                OrderableSpan(span(block1_pos.span.start..(block1_pos.span.start + 6))),
                // There is a third reference (but this is just from
                // our motivating example, it is not necessary to the
                // test).
                OrderableSpan(span(3059..3064)),
            ]
            .into_iter()
            .collect(),
        }),
    )]);

    let explicit_symtab = ExplicitSymbolTable::default();
    let mut register_assigner = IndexRegisterAssigner::default();
    let mut memory_map = MemoryMap::new([
        (span(0..10), None, BLOCK0_SIZE),
        (
            span(2455..2461),
            Some(Origin::Symbolic(span(2455..2461), origin_name.clone())),
            BLOCK1_SIZE,
        ),
    ]);
    let mut rc_block = RcBlock::default();
    let mut context = EvaluationContext {
        here: HereValue::Address(Address::from(u18!(0o100))),
        explicit_symtab: &explicit_symtab,
        implicit_symtab: &mut implicit_symtab,
        index_register_assigner: &mut register_assigner,
        memory_map: &memory_map,
        rc_updater: &mut rc_block,
        lookup_operation: LookupOperation::default(),
    };
    let scope = ScopeIdentifier::global();

    // Assign an address for block 0 as part of the scenario setup.
    let block0_addr = block0_pos
        .evaluate(&mut context, scope)
        .expect("should be able to assign an address to the first block");
    drop(context); // no longer want an immutable borrow on memory_map.
    memory_map.set_block_position(
        block0_pos.block_identifier,
        subword::right_half(block0_addr).into(),
    );

    // WHEN we try to assign an address to the second block (block 1).
    let mut context = EvaluationContext {
        here: HereValue::Address(Address::from(u18!(0o100))),
        explicit_symtab: &explicit_symtab,
        implicit_symtab: &mut implicit_symtab,
        index_register_assigner: &mut register_assigner,
        memory_map: &memory_map,
        rc_updater: &mut rc_block,
        lookup_operation: LookupOperation::default(),
    };
    let eval_result = context.fetch_or_assign_default(&origin_name);

    // THEN we should assign an address without failing.
    match eval_result {
        Err(e) => {
            panic!("should not fail to assign a start address to a block: {e}");
        }
        Ok(default_value) => {
            let expected: Unsigned36Bit =
                u36!(0o200000).wrapping_add(Unsigned36Bit::from(BLOCK0_SIZE));
            assert_eq!(default_value, expected);
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

/// Identifies a scope in which a tag name can be looked up.  Macro
/// bodies can contain "local" tags and so in general a tag's
/// definition will be local to the scope in which the definition is
/// made.  However, this is not yet implemented and so for the moment,
/// `ScopeIdentifier` just contains a unit value.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Ord, PartialOrd, Copy)]
pub(super) struct ScopeIdentifier(());

impl ScopeIdentifier {
    pub(super) fn global() -> ScopeIdentifier {
        ScopeIdentifier(())
    }
}

/// The `Evaluate` trait is implemented by any element of the program
/// that can evaluate to a 36-bit word value.
///
/// This includes octal constants, full instructions and also parts of
/// instructions (e.g. the index value, configuration value,
/// instruction opcodes, `#`, RC-word references and so forth.
pub(super) trait Evaluate: Spanned {
    // By separating the RcUpdater and RcAllocator traits we ensure
    // that evaluation cannot allocate more RC words.
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, EvaluationFailure>;
}

// Represents the RC-block; see [section 6-2.6 of the Users
// Handbook](https://archive.org/details/tx-2-users-handbook-nov-63/page/n161/mode/1up).
#[derive(Debug, Default, Clone)]
pub(crate) struct RcBlock {
    /// The address of the RC-block.
    pub(crate) address: Address,
    /// The contents of the RC-block, along with information about why
    /// each of the RC-words was allocated.
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

fn evaluate_normal_symbol<R: RcUpdater>(
    name: &SymbolName,
    span: Span,
    ctx: &mut EvaluationContext<R>,
    scope: ScopeIdentifier,
) -> Result<Unsigned36Bit, EvaluationFailure> {
    ctx.lookup_operation.deps_in_order.push(name.clone());
    if !ctx.lookup_operation.depends_on.insert(name.clone()) {
        // `name` was already in `depends_on`; in other words,
        // we have a loop.
        match OneOrMore::try_from_vec(ctx.lookup_operation.deps_in_order.clone()) {
            Ok(deps_in_order) => {
                return Err(EvaluationFailure::SymbolDefinitionLoop {
                    span,
                    deps_in_order,
                });
            }
            Err(_) => {
                panic!("we know deps_in_order is non-empty because we just appended an item to it");
            }
        }
    }

    let result = if let Some(def) = ctx.explicit_symtab.get(name) {
        let what: (&Span, &SymbolName, &ExplicitDefinition) = (&span, name, def);
        what.evaluate(ctx, scope)
    } else {
        ctx.fetch_or_assign_default(name)
    };

    ctx.lookup_operation.deps_in_order.pop();
    ctx.lookup_operation.depends_on.remove(name);
    result
}

/// Evaluate a named symbol.  This factors out behaviour common to the
/// evaluation of both symbolic origins and general symbols.
pub(crate) fn evaluate_symbol<R: RcUpdater>(
    name: &SymbolName,
    elevation: Script,
    span: Span,
    ctx: &mut EvaluationContext<R>,
    scope: ScopeIdentifier,
) -> Result<Unsigned36Bit, EvaluationFailure> {
    evaluate_normal_symbol(name, span, ctx, scope).map(|value| value.shl(elevation.shift()))
}

/// Determine the numerical value of all equalities, where they have
/// one.  We do this in order to identify problems with symbol
/// definitons and to generate information that we may need to emit
/// into the ouptut listing.
///
/// This function isn't actually needed to generate the output binary.
#[allow(clippy::too_many_arguments)]
pub(super) fn extract_final_equalities<R: RcUpdater>(
    equalities: &[Equality],
    body: &Source,
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
        let scope = ScopeIdentifier::global();

        match eq.value.evaluate(&mut ctx, scope) {
            Ok(value) => {
                final_symbols.define(
                    eq.name.clone(),
                    FinalSymbolType::Equality,
                    body.extract(eq.span.start..eq.span.end).to_string(),
                    FinalSymbolDefinition::PositionIndependent(value),
                );
            }
            Err(EvaluationFailure::HereIsNotAllowedHere(_)) => {
                // The value of this equality would depend on the
                // address at which it is evaluated, so it has no
                // single final value.  This is OK.
                final_symbols.define(
                    eq.name.clone(),
                    FinalSymbolType::Equality,
                    body.extract(eq.span.start..eq.span.end).to_string(),
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

impl Spanned for (&BlockIdentifier, &Option<Origin>, &Span) {
    fn span(&self) -> Span {
        *self.2
    }
}

#[derive(Debug)]
struct AddressOverflow(pub(crate) Address, pub(crate) Unsigned18Bit);

impl std::error::Error for AddressOverflow {}

impl Display for AddressOverflow {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "Adding {:o} to {:o} would generate a result which doesn't fit into an 18-bit address",
            self.0, self.1
        )
    }
}

fn offset_from_origin(origin: &Address, offset: Unsigned18Bit) -> Result<Address, AddressOverflow> {
    let (physical, _mark) = origin.split();
    match physical.checked_add(offset) {
        Some(total) => Ok(Address::from(total)),
        None => Err(AddressOverflow(*origin, offset)),
    }
}

impl Evaluate for BlockPosition {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, EvaluationFailure> {
        // Resolve the address of this block by evaluating its origin
        // specification if it has one.
        if let Some(origin) = self.origin.as_ref() {
            return origin.evaluate(ctx, scope);
        }

        // If it has no origin specification, we can deduce the
        // address of this block by placing it immediately after the
        // previous block, or (for the first block) using the default
        // block address.
        let previous_block_id: BlockIdentifier = match self.block_identifier.previous_block() {
            None => {
                // This is the first block.
                return Ok(Origin::default_address().into());
            }
            Some(id) => id,
        };

        // Get the location of the previous block and place this block after it.
        let (prev_addr, prev_size, prev_span): (Address, Unsigned18Bit, Span) =
            if let Some(previous_block) = ctx.memory_map.get(&previous_block_id).cloned() {
                // The previous block should have already been
                // assigned an address, because we assign them
                // in block-number order, ascending.
                let address_of_previous_block: Address = previous_block
                    .block_address
                    .expect("blocks should be assigned addresses in ascending block order");
                (
                    address_of_previous_block,
                    previous_block.block_size,
                    previous_block.span,
                )
            } else {
                unreachable!("unknown block {previous_block_id}")
            };

        // Add the size of the previous block to its address, yielding
        // the address of the location following it; this is the
        // address at which we will locate the current block.
        match offset_from_origin(&prev_addr, prev_size) {
            Ok(addr) => Ok(addr.into()),
            Err(_) => {
                // The address of this block would be outside
                // physical memory, so it is the combination
                // of the address of the previous block and
                // the size of the previous block which is the
                // problem.
                Err(EvaluationFailure::BlockTooLarge(
                    prev_span,
                    MachineLimitExceededFailure::BlockTooLarge {
                        span: prev_span,
                        block_id: previous_block_id,
                        offset: prev_size.into(),
                    },
                ))
            }
        }
    }
}

impl Evaluate for (&Span, &SymbolName, &ExplicitDefinition) {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, EvaluationFailure> {
        let (_span, name, def): (&Span, &SymbolName, &ExplicitDefinition) = *self;
        match def {
            ExplicitDefinition::Origin(Origin::Symbolic(_span, name), _block_id) => {
                unreachable!("symbolic origin {name} should already have been deduced")
            }
            ExplicitDefinition::Origin(Origin::Deduced(_span, _name, address), _block_id) => {
                Ok((*address).into())
            }
            ExplicitDefinition::Origin(Origin::Literal(_span, address), _block_id) => {
                Ok((*address).into())
            }
            ExplicitDefinition::Tag(TagDefinition::Resolved { span: _, address }) => {
                Ok(address.into())
            }
            ExplicitDefinition::Tag(TagDefinition::Unresolved {
                block_id,
                block_offset,
                span,
            }) => {
                if let Some(block_position) = ctx.memory_map.get(block_id).cloned() {
                    let block_origin: Address =
                        subword::right_half(block_position.evaluate(ctx, scope)?).into();
                    match offset_from_origin(&block_origin, *block_offset) {
                        Ok(computed_address) => Ok(computed_address.into()),
                        Err(_overflow_error) => Err(EvaluationFailure::BlockTooLarge(
                            *span,
                            MachineLimitExceededFailure::BlockTooLarge {
                                span: *span,
                                block_id: *block_id,
                                offset: (*block_offset).into(),
                            },
                        )),
                    }
                } else {
                    panic!(
                        "Tag named {name} at {span:?} refers to unknown block {block_id}: {def:?}"
                    );
                }
            }
            ExplicitDefinition::Equality(expression) => expression.evaluate(ctx, scope),
        }
    }
}
