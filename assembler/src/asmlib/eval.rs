use std::fmt::{self, Debug, Display, Formatter, Write};
use std::ops::{Shl, Shr};

use base::{
    charset::Script,
    prelude::{Address, IndexBy, Unsigned18Bit, Unsigned36Bit, DEFER_BIT},
    u36,
};

use crate::symtab::{LookupOperation, SymbolTable};

use super::ast::{
    ArithmeticExpression, Atom, CommaDelimitedInstruction, Commas, ConfigValue, EqualityValue,
    HoldBit, InstructionFragment, LiteralValue, Operator, RcAllocator, SymbolOrLiteral,
    TaggedProgramInstruction, UntaggedProgramInstruction,
};
use super::span::*;
use super::symbol::{SymbolContext, SymbolName, SymbolOrHere};
use super::types::{BlockIdentifier, MachineLimitExceededFailure};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum LookupTarget {
    Symbol(SymbolName, Span),
    MemRef(MemoryReference, Span),
    /// Attempt to look up "here", that is, '#'.
    Hash(Span),
}

impl From<(SymbolName, Span)> for LookupTarget {
    fn from((sym, span): (SymbolName, Span)) -> LookupTarget {
        LookupTarget::Symbol(sym, span)
    }
}

impl From<(MemoryReference, Span)> for LookupTarget {
    fn from((r, span): (MemoryReference, Span)) -> LookupTarget {
        LookupTarget::MemRef(r, span)
    }
}

impl Display for LookupTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            LookupTarget::Hash(_) => f.write_char('#'),
            LookupTarget::Symbol(name, _) => {
                write!(f, "symbol {name}")
            }
            LookupTarget::MemRef(
                MemoryReference {
                    block_id,
                    block_offset: _,
                },
                _,
            ) => {
                write!(f, "{block_id}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct MemoryReference {
    pub(crate) block_id: BlockIdentifier,
    pub(crate) block_offset: usize,
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
pub(crate) enum SymbolLookupFailureKind {
    Inconsistent(String),
    Loop { deps_in_order: Vec<SymbolName> },
    MachineLimitExceeded(MachineLimitExceededFailure),
    HereIsNotAllowedHere,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SymbolLookupFailure {
    pub(crate) target: LookupTarget,
    pub(crate) kind: SymbolLookupFailureKind,
}

impl Display for SymbolLookupFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let desc = self.target.to_string();
        match self.kind() {
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
            SymbolLookupFailureKind::HereIsNotAllowedHere => {
                f.write_str("'#' (representing the current address) is not allowed here")
            }
        }
    }
}

impl From<(SymbolName, Span, SymbolLookupFailureKind)> for SymbolLookupFailure {
    fn from(
        (symbol_name, span, kind): (SymbolName, Span, SymbolLookupFailureKind),
    ) -> SymbolLookupFailure {
        SymbolLookupFailure {
            target: LookupTarget::Symbol(symbol_name, span),
            kind,
        }
    }
}

impl SymbolLookupFailure {
    pub(crate) fn kind(&self) -> &SymbolLookupFailureKind {
        &self.kind
    }
}

impl std::error::Error for SymbolLookupFailure {}

pub(crate) trait SymbolLookup {
    type Operation<'a>;

    fn lookup_with_op<R: RcAllocator>(
        &mut self,
        name: &SymbolName,
        span: Span, // TODO: use &Span?
        target_address: &HereValue,
        rc_allocator: &mut R,
        context: &SymbolContext,
        op: &mut Self::Operation<'_>,
    ) -> Result<SymbolValue, SymbolLookupFailure>;
}

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
            HereValue::NotAllowed => Err(SymbolLookupFailure {
                target: LookupTarget::Hash(*span),
                kind: SymbolLookupFailureKind::HereIsNotAllowedHere,
            }),
        }
    }
}

pub(crate) trait Evaluate {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure>;
}

#[derive(Debug, Default)]
pub(crate) struct RcBlock {
    pub(crate) address: Address,
    pub(crate) words: Vec<(Span, Unsigned36Bit)>,
}

impl RcAllocator for RcBlock {
    fn allocate(&mut self, span: Span, value: Unsigned36Bit) -> Address {
        match Unsigned18Bit::try_from(self.words.len()) {
            Ok(offset) => {
                let addr = self.address.index_by(offset);
                self.words.push((span, value));
                addr
            }
            Err(_) => {
                panic!("program is too large"); // TODO: fixme: use Result
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

pub(crate) fn evaluate_and_combine_values<R, E>(
    items: &[E],
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure>
where
    R: RcAllocator,
    E: Evaluate,
{
    items.iter().try_fold(Unsigned36Bit::ZERO, |acc, item| {
        item.evaluate(target_address, symtab, rc_allocator, op)
            .map(|value| combine_fragment_values(acc, value))
    })
}

impl Evaluate for EqualityValue {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // Comma delimited values are evaluated left-to-right, as stated in item
        // (b) in section 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of
        // the Users Handbook.  The initial value is zero (as
        // specified in item (a) in the same place).
        evaluate_and_combine_values(self.items(), target_address, symtab, rc_allocator, op)
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
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        if self.instructions.is_empty() {
            panic!("invariant broken: TaggedProgramInstruction contains zero instructions");
        }
        evaluate_and_combine_values(&self.instructions, target_address, symtab, rc_allocator, op)
    }
}

impl Evaluate for LiteralValue {
    fn evaluate<R: RcAllocator>(
        &self,
        _target_address: &HereValue,
        _symtab: &mut SymbolTable,
        _rc_allocator: &mut R,
        _op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        Ok(self.value())
    }
}

fn fold_step<R: RcAllocator>(
    acc: Unsigned36Bit,
    (binop, right): &(Operator, Atom),
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let right: Unsigned36Bit = right.evaluate(target_address, symtab, rc_allocator, op)?;
    Ok(ArithmeticExpression::eval_binop(acc, binop, right))
}

impl Evaluate for ArithmeticExpression {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let first: Unsigned36Bit = self
            .first
            .evaluate(target_address, symtab, rc_allocator, op)?;
        let result: Result<Unsigned36Bit, SymbolLookupFailure> =
            self.tail.iter().try_fold(first, |acc, curr| {
                fold_step(acc, curr, target_address, symtab, rc_allocator, op)
            });
        result
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        fn index_value_of(unshifted: Unsigned36Bit) -> Unsigned36Bit {
            unshifted.shl(Script::Sub.shift())
        }

        match self {
            InstructionFragment::Arithmetic(expr) => {
                expr.evaluate(target_address, symtab, rc_allocator, op)
            }
            InstructionFragment::DeferredAddressing => Ok(DEFER_BIT),
            InstructionFragment::Config(value) => {
                value.evaluate(target_address, symtab, rc_allocator, op)
            }
            InstructionFragment::PipeConstruct {
                index: p,
                rc_word_span,
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
                let (base, index) = rc_word_value.as_ref();
                let base_value = base.evaluate(target_address, symtab, rc_allocator, op)?;
                let index_value = index.evaluate(target_address, symtab, rc_allocator, op)?;
                let rc_word_val: Unsigned36Bit = combine_fragment_values(base_value, index_value);
                let p_value: Unsigned36Bit =
                    index_value_of(p.evaluate(target_address, symtab, rc_allocator, op)?);
                let addr: Address = rc_allocator.allocate(*rc_word_span, rc_word_val);
                Ok(combine_fragment_values(
                    combine_fragment_values(Unsigned36Bit::from(addr), p_value),
                    DEFER_BIT,
                ))
            }
        }
    }
}

impl Evaluate for ConfigValue {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            ConfigValue::Literal(_span, value) => Ok(*value),
            ConfigValue::Symbol(span, SymbolOrHere::Here) => {
                Ok(Unsigned36Bit::from(target_address.get_address(span)?))
            }
            ConfigValue::Symbol(span, SymbolOrHere::Named(name)) => {
                let context = SymbolContext::configuration();
                match symtab.lookup_with_op(name, *span, target_address, rc_allocator, &context, op)
                {
                    Ok(SymbolValue::Final(value)) => Ok(value),
                    Err(e) => Err(e),
                }
            }
        }
        .map(|value| value.shl(30u32))
    }
}

fn symbol_name_lookup<R: RcAllocator>(
    name: &SymbolName,
    elevation: Script,
    span: Span,
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let context = SymbolContext::from((elevation, span));
    match symtab.lookup_with_op(name, span, target_address, rc_allocator, &context, op) {
        Ok(SymbolValue::Final(value)) => Ok(value),
        Err(e) => Err(e),
    }
    .map(|value| value.shl(elevation.shift()))
}

impl Evaluate for Atom {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Atom::Symbol(span, elevation, SymbolOrHere::Here) => {
                let value: Unsigned36Bit = target_address.get_address(span)?.into();
                Ok(value.shl(elevation.shift()))
            }
            Atom::Literal(literal) => Ok(literal.value()),
            Atom::Symbol(span, elevation, SymbolOrHere::Named(name)) => symbol_name_lookup(
                name,
                *elevation,
                *span,
                target_address,
                symtab,
                rc_allocator,
                op,
            ),
            Atom::Parens(_script, expr) => expr.evaluate(target_address, symtab, rc_allocator, op),
            Atom::RcRef(span, tagged_program_instructions) => {
                let value: Unsigned36Bit = evaluate_and_combine_values(
                    tagged_program_instructions,
                    target_address,
                    symtab,
                    rc_allocator,
                    op,
                )?;
                let addr: Address = rc_allocator.allocate(*span, value);
                Ok(addr.into())
            }
        }
    }
}

impl Evaluate for SymbolOrLiteral {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            SymbolOrLiteral::Symbol(script, symbol_name, span) => symbol_name_lookup(
                symbol_name,
                *script,
                *span,
                target_address,
                symtab,
                rc_allocator,
                op,
            ),
            SymbolOrLiteral::Literal(literal_value) => {
                literal_value.evaluate(target_address, symtab, rc_allocator, op)
            }
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

impl Evaluate for CommaDelimitedInstruction {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction
            .evaluate(target_address, symtab, rc_allocator, op)
            .map(|value| comma_transformation(&self.leading_commas, value, &self.trailing_commas))
    }
}

#[cfg(test)]
mod comma_tests {
    use super::super::ast::*;
    use super::super::span::span;
    use super::comma_transformation;
    use base::u36;

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_0() {
        assert_eq!(
            comma_transformation(&None, u36!(0o444_333_222_111), &None),
            u36!(0o444_333_222_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &None,
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16)))
            ),
            u36!(0o111_000_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &None,
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17)))
            ),
            u36!(0o222_111_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &None,
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18)))
            ),
            u36!(0o333_222_111_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_0() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &None,
            ),
            u36!(0o000_000_000_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16))),
            ),
            u36!(0o000_222_111_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17))),
            ),
            u36!(0o000_111_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18))),
            ),
            u36!(0o444_333_222_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_0() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &None,
            ),
            u36!(0o000_000_222_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16))),
            ),
            u36!(0o000_000_111_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17))),
            ),
            u36!(0o222_111_444_333)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18))),
            ),
            u36!(0o000_000_444_333)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_0() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &None,
            ),
            u36!(0o000_000_000_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16))),
            ),
            u36!(0o000_000_000_444)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17))),
            ),
            u36!(0o000_444_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18))),
            ),
            u36!(0o000_000_444_333)
        );
    }
}

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // TODO: issue a diagnostic if a TaggedProgramInstruction
        // contains inconsistent values for the hold bit.  We will need to decide
        // whether something like ",h" sets the hold bit (i.e. whether
        // the hold bit is supposed to be subject to the same
        // comma rules that other values are).
        const HELD_MASK: Unsigned36Bit = u36!(1 << 35);
        self.inst
            .evaluate(target_address, symtab, rc_allocator, op)
            .map(|word| match self.holdbit {
                HoldBit::Hold => word | HELD_MASK,
                HoldBit::NotHold => word & !HELD_MASK,
                HoldBit::Unspecified => word,
            })
    }
}
