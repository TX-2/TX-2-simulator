#[cfg(test)]
mod comma_tests;

use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{Shl, Shr};

use tracing::{event, Level};

use base::{
    charset::Script,
    prelude::{Address, IndexBy, Signed36Bit, Unsigned18Bit, Unsigned36Bit, DEFER_BIT},
    subword, u36,
};

use super::ast::*;
use super::collections::OneOrMore;
use super::listing::{Listing, ListingLine};
use super::span::*;
use super::symbol::{AddressUse, ConfigUse, IndexUse, OriginUse, SymbolName};

use super::types::{
    offset_from_origin, AssemblerFailure, BlockIdentifier, InconsistentOrigin,
    MachineLimitExceededFailure, ProgramError, RcWordSource,
};
use crate::symbol::SymbolContext;
use crate::symtab::{
    BlockPosition, ExplicitDefinition, ExplicitSymbolTable, FinalSymbolDefinition,
    FinalSymbolTable, FinalSymbolType, ImplicitDefinition, ImplicitSymbolTable,
    IndexRegisterAssigner, LookupOperation, MemoryMap, TagDefinition,
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
    InconsistentOrigins(InconsistentOrigin),
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
            SymbolLookupFailure::InconsistentOrigins(inconsistent_origin) => {
                inconsistent_origin.span()
            }
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
            InconsistentOrigins(e) => write!(f, "{e}"),
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
            SymbolLookupFailure::InconsistentOrigins(e) => {
                ProgramError::InconsistentOriginDefinitions(e)
            }
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
///
/// Values which refer to addresses (and which therefore should
/// point to a zero-initialised RC-word) should already have a
/// default value assigned.
fn assign_default_value(
    index_register_assigner: &mut IndexRegisterAssigner,
    name: &SymbolName,
    contexts_used: &SymbolContext,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    // TODO: maybe make this a method of EvaluationContext instead.
    event!(
        Level::DEBUG,
        "assigning default value for {name} used in contexts {contexts_used:?}"
    );
    let span: Span = *contexts_used.any_span();
    use AddressUse::*;
    use ConfigUse::*;
    use IndexUse::*;
    use OriginUse::*;
    match contexts_used.parts() {
        (NotConfig, NotIndex, _, IncludesOrigin) => {
            // origin only or address and origin
            unreachable!("get_default_value should not be called for origin speicifations; attempted to assign default value for {name} (used in contexts: {contexts_used:?}")
        }
        (IncludesConfig, _, _, IncludesOrigin) | (_, IncludesIndex, _, IncludesOrigin) => {
            // origin and either config or index
            //
            // TODO: make this an error at the time the contexts are recorded.
            Err(SymbolLookupFailure::InconsistentOrigins(
                InconsistentOrigin {
                    origin_name: name.clone(),
                    span,
                    msg: format!("symbol {name} was used in both origin and other contexts"),
                },
            ))
        }
        (NotConfig, NotIndex, NotAddress, NotOrigin) => unreachable!(), // apparently no usage at all
        (IncludesConfig, _, _, NotOrigin) => Ok(Unsigned36Bit::ZERO), // configuration (perhaps in combo with others)
        (NotConfig, IncludesIndex, _, NotOrigin) => {
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
        (NotConfig, NotIndex, IncludesAddress, NotOrigin) => {
            unreachable!("default assignments for address-context symexes should be assigned before evaluation starts")
        }
    }
}

#[derive(Debug)]
pub(crate) struct EvaluationContext<'s, R: RcUpdater> {
    pub(crate) here: HereValue,
    pub(crate) explicit_symtab: &'s mut ExplicitSymbolTable,
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
                // the resto of the work is carried out with
                // index_register_assigner only.
                if let SymbolContext {
                    origin_of_block: Some(block_identifier),
                    ..
                } = &context
                {
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
                                match self.implicit_symtab.record_computed_origin_value(
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
                            eprintln!("recording default value {value} for {name}");
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

pub(crate) fn evaluate_and_combine_values<'a, R, E, I>(
    mut items: I,
    ctx: &mut EvaluationContext<R>,
) -> Result<Unsigned36Bit, SymbolLookupFailure>
where
    R: RcUpdater,
    E: Evaluate + 'a,
    I: Iterator<Item = &'a E>,
{
    items.try_fold(Unsigned36Bit::ZERO, |acc, item| {
        item.evaluate(ctx)
            .map(|value| combine_fragment_values(acc, value))
    })
}

impl Evaluate for EqualityValue {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.inner.evaluate(ctx)
    }
}

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // Comma delimited values are evaluated left-to-right, as stated in item
        // (b) in section 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of
        // the Users Handbook.  The initial value is zero (as
        // specified in item (a) in the same place).
        evaluate_and_combine_values(self.fragments.iter(), ctx)
    }
}

/// The Users Handbook implies that instruction fragments are added
/// together, and I am not sure whether they mean this literally (as
/// in, addition) or figuratively (as in a logica-or operation).  This
/// function exists to be a single place to encode this assumption.
pub(crate) fn combine_fragment_values(left: Unsigned36Bit, right: Unsigned36Bit) -> Unsigned36Bit {
    left | right
}

impl Evaluate for TaggedProgramInstruction {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction.evaluate(ctx)
    }
}

impl Evaluate for LiteralValue {
    fn evaluate<R: RcUpdater>(
        &self,
        _ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        Ok(self.value())
    }
}

fn fold_step<R: RcUpdater>(
    acc: Unsigned36Bit,
    (binop, right): &(Operator, SignedAtom),
    ctx: &mut EvaluationContext<R>,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let right: Unsigned36Bit = right.evaluate(ctx)?;
    Ok(ArithmeticExpression::eval_binop(acc, binop, right))
}

impl Evaluate for ArithmeticExpression {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let first: Unsigned36Bit = self.first.evaluate(ctx)?;
        let result: Result<Unsigned36Bit, SymbolLookupFailure> = self
            .tail
            .iter()
            .try_fold(first, |acc, curr| fold_step(acc, curr, ctx));
        result
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            InstructionFragment::Null(_) => Ok(Unsigned36Bit::ZERO),
            InstructionFragment::Arithmetic(expr) => expr.evaluate(ctx),
            InstructionFragment::DeferredAddressing(_) => Ok(DEFER_BIT),
            InstructionFragment::Config(value) => value.evaluate(ctx),
            InstructionFragment::PipeConstruct {
                index: p,
                rc_word_span: _,
                rc_word_value,
            } => {
                // The pipe construct is described in section 6-2.8
                // "SPECIAL SYMBOLS" of the Users Handbook.
                //
                //
                // "ADXₚ|ₜQ" should be equivalent to "ADXₚ{Qₜ}*".
                // (Note that in the real pipe construct the "|" is
                // itself in subscript).  During parsing, the values
                // of Q and ₜ were combined into the two parts of the
                // rc_word_value tuple.  We evaluate Qₜ as
                // rc_word_val.
                let p_value: Unsigned36Bit = p.item.evaluate(ctx)?;
                let rc_word_addr: Unsigned36Bit = rc_word_value.evaluate(ctx)?;
                Ok(combine_fragment_values(
                    combine_fragment_values(p_value, rc_word_addr),
                    DEFER_BIT,
                ))
            }
        }
    }
}

impl Evaluate for ConfigValue {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // The `expr` member was either originally in superscript (in
        // which case the `evaluate` value will already have been
        // shifted into the correct position in the word, or in normal
        // script (in which case we need to shift it ourselves).
        let shift = if self.already_superscript { 0 } else { 30u32 };
        self.expr.evaluate(ctx).map(|value| value.shl(shift))
    }
}

fn final_lookup_helper_body<R: RcUpdater>(
    ctx: &mut EvaluationContext<R>,
    name: &SymbolName,
    span: Span,
) -> Result<SymbolValue, SymbolLookupFailure> {
    if let Some(def) = ctx.explicit_symtab.get_clone(name) {
        let what: (&Span, &SymbolName, &ExplicitDefinition) = (&span, name, &def);
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

fn symbol_name_lookup<R: RcUpdater>(
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

impl Evaluate for Atom {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Atom::SymbolOrLiteral(value) => value.evaluate(ctx),
            Atom::Parens(_span, _script, expr) => expr.evaluate(ctx),
            Atom::RcRef(_span, registers_containing) => registers_containing.evaluate(ctx),
        }
    }
}

impl Evaluate for SignedAtom {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.magnitude.evaluate(ctx).map(|magnitude| {
            if self.negated {
                let s36 = magnitude.reinterpret_as_signed();
                let signed_result = Signed36Bit::ZERO.wrapping_sub(s36);
                signed_result.reinterpret_as_unsigned()
            } else {
                magnitude
            }
        })
    }
}

impl Evaluate for SymbolOrLiteral {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            SymbolOrLiteral::Symbol(script, symbol_name, span) => {
                symbol_name_lookup(symbol_name, *script, *span, ctx)
            }
            SymbolOrLiteral::Literal(literal_value) => literal_value.evaluate(ctx),
            SymbolOrLiteral::Here(script, span) => ctx
                .here
                .get_address(span)
                .map(|addr: Address| Unsigned36Bit::from(addr))
                .map(|addr_value: Unsigned36Bit| addr_value.shl(script.shift())),
        }
    }
}

/// Implement the value transformation rules described in the table
/// "COMMA CHART" in section 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS"
/// of the Users Handbook.
///
/// It's likely that the TX-2's original implementation of this in the
/// M4 assembler used the system configuration feature to perform the
/// word-quarter masking and mapping.  While we could do that it would
/// introduce a dependency between the assembler and the siimulator's
/// implementation of the exchange unit.  Generating the correct
/// system configuration value would be more or less as complex as
/// just implementing the logic here, so we just implement it here in
/// order to avoid the dependency.
fn comma_transformation(
    leading_commas: &Option<Commas>,
    value: Unsigned36Bit,
    trailing_commas: &Option<Commas>,
) -> Unsigned36Bit {
    match (leading_commas, trailing_commas) {
        (None, None) => value,
        (None, Some(Commas::One(_))) => value.and(0o777).shl(27),
        (None, Some(Commas::Two(_))) => value.and(0o777777).shl(18),
        (None, Some(Commas::Three(_))) => value.and(0o777777777).shl(9),

        (Some(Commas::One(_)), None) => value.and(0o777),
        (Some(Commas::One(_)), Some(Commas::One(_))) => value.and(0o777_777).shl(9),
        (Some(Commas::One(_)), Some(Commas::Two(_))) => value.and(0o777).shl(18),
        (Some(Commas::One(_)), Some(Commas::Three(_))) => value.and(0o777_777_777_000),

        (Some(Commas::Two(_)), None) => value.and(0o777_777),
        (Some(Commas::Two(_)), Some(Commas::One(_))) => value.and(0o777).shl(9),
        (Some(Commas::Two(_)), Some(Commas::Two(_))) => {
            let hi = value.and(0o000_000_777_777).shl(18);
            let lo = value.and(0o777_777_000_000).shr(18);
            hi | lo
        }
        (Some(Commas::Two(_)), Some(Commas::Three(_))) => value.and(0o777_777_000_000).shr(18),

        (Some(Commas::Three(_)), None) => value.and(0o777),
        (Some(Commas::Three(_)), Some(Commas::One(_))) => value.and(0o777_000_000_000).shr(27),
        (Some(Commas::Three(_)), Some(Commas::Two(_))) => value.and(0o777_000_000_000).shr(9),
        (Some(Commas::Three(_)), Some(Commas::Three(_))) => value.and(0o777_777_000_000).shr(18),
    }
}

impl Evaluate for CommaDelimitedFragment {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.fragment
            .evaluate(ctx)
            .map(|word| {
                // TODO: issue a diagnostic if there are inconsistent
                //  values for the hold bit.  We will need to decide
                // whether something like ",h" sets the hold bit (i.e. whether
                // the hold bit is supposed to be subject to the same
                // comma rules that other values are).
                const HELD_MASK: Unsigned36Bit = u36!(1 << 35);

                match self.holdbit {
                    HoldBit::Hold => word | HELD_MASK,
                    HoldBit::NotHold => word & !HELD_MASK,
                    HoldBit::Unspecified => word,
                }
            })
            .map(|value| comma_transformation(&self.leading_commas, value, &self.trailing_commas))
    }
}

fn record_undefined_symbol_or_return_failure(
    source_file_body: &str,
    e: SymbolLookupFailure,
    undefined_symbols: &mut BTreeMap<SymbolName, (Span, ProgramError)>,
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
                .or_insert_with(|| {
                    (
                        span,
                        ProgramError::SymbolDefinitionLoop {
                            symbol_names: deps_in_order,
                            span,
                        },
                    )
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
    explicit_symbols: &mut ExplicitSymbolTable,
    implicit_symbols: &mut ImplicitSymbolTable,
    memory_map: &MemoryMap,
    index_register_assigner: &mut IndexRegisterAssigner,
    rc_allocator: &mut R,
    final_symbols: &mut FinalSymbolTable,
    bad_symbol_definitions: &mut BTreeMap<SymbolName, (Span, ProgramError)>,
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
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        memory_map: &MemoryMap,
        index_register_assigner: &mut IndexRegisterAssigner,
        rc_allocator: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &str,
        listing: &mut Listing,
        undefined_symbols: &mut BTreeMap<SymbolName, (Span, ProgramError)>,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let word_count: Unsigned18Bit = self
            .sequences
            .iter()
            .map(|seq| seq.emitted_word_count())
            .sum();
        let mut result: Vec<Unsigned36Bit> = Vec::with_capacity(word_count.into());
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
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        memory_map: &MemoryMap,
        index_register_assigner: &mut IndexRegisterAssigner,
        rc_allocator: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &str,
        listing: &mut Listing,
        bad_symbol_definitions: &mut BTreeMap<SymbolName, (Span, ProgramError)>,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let mut words: Vec<Unsigned36Bit> = Vec::with_capacity(self.emitted_word_count().into());
        for (offset, instruction) in self.iter().enumerate() {
            let offset: Unsigned18Bit = Unsigned18Bit::try_from(offset)
                .ok()
                .and_then(|off| off.checked_add(start_offset))
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

impl Evaluate for RegistersContaining {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let mut first_addr: Option<Unsigned36Bit> = None;
        for rc_word in self.words() {
            // Evaluation of the RegisterContaining value will compute
            // a correct here-value, we don't need to pass it in.  But
            // we can't pass None, and so instead we pass NotAllowed
            // so that if a bug is introduced we will see a failure
            // rather than an incorrect result.
            let address: Unsigned36Bit =
                ctx.for_target_address(HereValue::NotAllowed, |newctx| rc_word.evaluate(newctx))?;
            if first_addr.is_none() {
                first_addr = Some(address);
            }
        }
        match first_addr {
            Some(addr) => Ok(addr),
            None => {
                unreachable!("RC-references should not occupy zero words of storage");
            }
        }
    }
}

impl Evaluate for RegisterContaining {
    fn evaluate<R: RcUpdater>(
        &self,
        // We must not use the passed-in target address (in ctx.here) since inside
        // an RC-word, `#` refers to the adddress of the RC-word, not
        // the address of the instruction which refers to it.
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            RegisterContaining::Unallocated(_) => {
                unreachable!(
                    "evaluate() called on RegisterContaining instance {self:?} before it was allocated"
                );
            }
            RegisterContaining::Allocated(rc_word_addr, inst) => {
                // Tags defined in RC-words may not be used for M4's
                // editing instuctions, but nevertheless they are not
                // locally-scoped.  This is demonstrated by the
                // example in section 6-4.7 of the User's Handbook,
                // which looks like this:
                //
                // ```
                // ☛☛DEF TBS|α
                //  α
                //  α
                //  α
                //  α
                //  α
                // ☛☛EMD
                // 100|
                // USE->     LDA {TS->TBS|0}  ** 5 BLANK RC WORDS
                //           LDA TOMM
                //           STA TS+3
                // ```
                //
                // You will see above that the definition of the tag
                // `TS` is inside an RC-word, but _not_ inside a macro
                // body.
                //
                // The example explains that the above code snippet expands to:
                //
                // ```
                // 100|
                // USE ->    LDA {TS-> TBS| 0}              |002400 000103|000100
                //           LDA TOMM                       |002400 000110|   101
                //           STA TS+3                       |003400 000106|   102
                // TS ->     TBS 0
                //           0                              |000000 000000|   103
                //           0                              |000000 000000|   104
                //           0                              |000000 000000|   105
                //           0                              |000000 000000|   106
                //           0                              |000000 000000|   107
                // TOMM ->   0                              |000000 000000|000110
                // ```
                //
                // Within the RC-word, # ("here") resolves to the
                // address of the RC-word itself.  So before we
                // evaluate the value to be placed in the RC-word, we
                // need to know the value that # will take during the
                // evaluation process.
                let rc_word_value: Unsigned36Bit = ctx
                    .for_target_address(HereValue::Address(*rc_word_addr), |newctx| {
                        inst.evaluate(newctx)
                    })?;
                ctx.rc_updater.update(*rc_word_addr, rc_word_value);
                Ok(Unsigned36Bit::from(rc_word_addr))
            }
        }
    }
}

impl Evaluate for Origin {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Origin::Literal(_span, address) => Ok(address.into()),
            Origin::Symbolic(span, symbol_name) => {
                symbol_name_lookup(symbol_name, Script::Normal, *span, ctx)
            }
        }
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

impl LocatedBlock {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        for seq in self.sequences.iter_mut() {
            seq.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
        }
        Ok(())
    }
}

impl TaggedProgramInstruction {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.instruction
            .assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
    }
}

impl UntaggedProgramInstruction {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        for inst in self.fragments.iter_mut() {
            inst.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
        }
        Ok(())
    }
}

impl CommaDelimitedFragment {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.fragment
            .assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
    }
}

impl InstructionFragment {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        use InstructionFragment::*;
        match self {
            Null(_) | DeferredAddressing(_) => Ok(()),
            Arithmetic(expr) => {
                expr.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
            }
            Config(cfg) => cfg.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator),
            PipeConstruct {
                index: _,
                rc_word_span,
                rc_word_value,
            } => {
                let span: Span = *rc_word_span;
                let w = rc_word_value.clone();
                *rc_word_value = w.assign_rc_word(
                    RcWordSource::PipeConstruct(span),
                    explicit_symtab,
                    implicit_symtab,
                    rc_allocator,
                )?;
                Ok(())
            }
        }
    }
}

impl RegisterContaining {
    pub(crate) fn assign_rc_word<R: RcAllocator>(
        self,
        source: RcWordSource,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<RegisterContaining, RcWordAllocationFailure> {
        match self {
            RegisterContaining::Unallocated(mut tpibox) => {
                let address: Address = rc_allocator.allocate(source, Unsigned36Bit::ZERO)?;
                for tag in tpibox.tags.iter() {
                    eprintln!(
                        "assigning RC-word at address {address} serves as defnition of tag {}",
                        &tag.name
                    );
                    implicit_symtab.remove(&tag.name);
                    if let Err(e) = explicit_symtab.define(
                        tag.name.clone(),
                        ExplicitDefinition::Tag(TagDefinition::Resolved {
                            span: tag.span,
                            address,
                        }),
                    ) {
                        return Err(RcWordAllocationFailure::InconsistentTag(e));
                    }
                }
                tpibox.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
                let tpi: Box<TaggedProgramInstruction> = tpibox;
                Ok(RegisterContaining::Allocated(address, tpi))
            }
            other => Ok(other),
        }
    }
}

impl RegistersContaining {
    pub(crate) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        span: Span,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        let source = RcWordSource::Braces(span);
        for rc in self.words_mut() {
            *rc = rc.clone().assign_rc_word(
                source.clone(),
                explicit_symtab,
                implicit_symtab,
                rc_allocator,
            )?;
        }
        Ok(())
    }
}

impl ArithmeticExpression {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.first
            .assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
        for (_op, atom) in self.tail.iter_mut() {
            atom.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
        }
        Ok(())
    }
}

impl ConfigValue {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.expr
            .assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
    }
}

impl SignedAtom {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.magnitude
            .assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
    }
}

impl Atom {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        match self {
            Atom::SymbolOrLiteral(thing) => {
                thing.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
            }
            Atom::Parens(_, _, expr) => {
                expr.assign_rc_words(explicit_symtab, implicit_symtab, rc_allocator)
            }
            Atom::RcRef(span, rc) => {
                rc.assign_rc_words(*span, explicit_symtab, implicit_symtab, rc_allocator)
            }
        }
    }
}

impl SymbolOrLiteral {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        _explicit_symtab: &mut ExplicitSymbolTable,
        _implicit_symtab: &mut ImplicitSymbolTable,
        _rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        Ok(())
    }
}
