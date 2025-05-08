use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::ops::{Shl, Shr};

use base::{
    charset::Script,
    prelude::{Address, IndexBy, Signed36Bit, Unsigned18Bit, Unsigned36Bit, DEFER_BIT},
    u36,
};

use super::ast::*;
use super::listing::{Listing, ListingLine};
use super::span::*;
use super::symbol::SymbolName;
use super::types::{
    AssemblerFailure, BlockIdentifier, MachineLimitExceededFailure, ProgramError, RcWordSource,
};
use crate::symbol::SymbolContext;
use crate::symtab::{
    FinalSymbolDefinition, FinalSymbolTable, FinalSymbolType, LookupOperation, SymbolTable,
};

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
    InconsistentOrigins {
        name: SymbolName,
        span: Span,
        msg: String,
    },
    Missing {
        uses: SymbolContext,
    },
    Loop {
        deps_in_order: Vec<SymbolName>,
    },
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
            SymbolLookupFailureKind::Missing { .. } => f.write_str("no definition found"),
            SymbolLookupFailureKind::InconsistentOrigins { name, span: _, msg } => {
                write!(f, "inconsistent definitions for origin {name}: {msg}")
            }
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

    fn lookup_with_op<R: RcUpdater>(
        &mut self,
        name: &SymbolName,
        span: Span, // TODO: use &Span?
        target_address: &HereValue,
        rc_updater: &mut R,
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

pub(super) trait Evaluate: Spanned {
    // By separating the RcUpdater and RcAllocator traits we ensure
    // that evaluation cannot allocate more RC words.
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
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
            Err(RcWordAllocationFailure {
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

pub(crate) fn evaluate_and_combine_values<R, E>(
    items: &[E],
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_updater: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure>
where
    R: RcUpdater,
    E: Evaluate,
{
    items.iter().try_fold(Unsigned36Bit::ZERO, |acc, item| {
        item.evaluate(target_address, symtab, rc_updater, op)
            .map(|value| combine_fragment_values(acc, value))
    })
}

impl Evaluate for EqualityValue {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.inner.evaluate(target_address, symtab, rc_updater, op)
    }
}

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // Comma delimited values are evaluated left-to-right, as stated in item
        // (b) in section 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of
        // the Users Handbook.  The initial value is zero (as
        // specified in item (a) in the same place).
        evaluate_and_combine_values(
            self.fragments.as_slice(),
            target_address,
            symtab,
            rc_updater,
            op,
        )
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
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction
            .evaluate(target_address, symtab, rc_updater, op)
    }
}

impl Evaluate for LiteralValue {
    fn evaluate<R: RcUpdater>(
        &self,
        _target_address: &HereValue,
        _symtab: &mut SymbolTable,
        _rc_updater: &mut R,
        _op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        Ok(self.value())
    }
}

fn fold_step<R: RcUpdater>(
    acc: Unsigned36Bit,
    (binop, right): &(Operator, SignedAtom),
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_updater: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let right: Unsigned36Bit = right.evaluate(target_address, symtab, rc_updater, op)?;
    Ok(ArithmeticExpression::eval_binop(acc, binop, right))
}

impl Evaluate for ArithmeticExpression {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let first: Unsigned36Bit = self
            .first
            .evaluate(target_address, symtab, rc_updater, op)?;
        let result: Result<Unsigned36Bit, SymbolLookupFailure> =
            self.tail.iter().try_fold(first, |acc, curr| {
                fold_step(acc, curr, target_address, symtab, rc_updater, op)
            });
        result
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            InstructionFragment::Null(_) => Ok(Unsigned36Bit::ZERO),
            InstructionFragment::Arithmetic(expr) => {
                expr.evaluate(target_address, symtab, rc_updater, op)
            }
            InstructionFragment::DeferredAddressing(_) => Ok(DEFER_BIT),
            InstructionFragment::Config(value) => {
                value.evaluate(target_address, symtab, rc_updater, op)
            }
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
                let p_value: Unsigned36Bit =
                    p.item.evaluate(target_address, symtab, rc_updater, op)?;
                let rc_word_addr: Unsigned36Bit =
                    rc_word_value.evaluate(target_address, symtab, rc_updater, op)?;
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
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // The `expr` member was either originally in superscript (in
        // which case the `evaluate` value will already have been
        // shifted into the correct position in the word, or in normal
        // script (in which case we need to shift it ourselves).
        let shift = if self.already_superscript { 0 } else { 30u32 };
        self.expr
            .evaluate(target_address, symtab, rc_updater, op)
            .map(|value| value.shl(shift))
    }
}

fn symbol_name_lookup<R: RcUpdater>(
    name: &SymbolName,
    elevation: Script,
    span: Span,
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_updater: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    match symtab.lookup_with_op(name, span, target_address, rc_updater, op) {
        Ok(SymbolValue::Final(value)) => Ok(value),
        Err(e) => Err(e),
    }
    .map(|value| value.shl(elevation.shift()))
}

impl Evaluate for Atom {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Atom::SymbolOrLiteral(value) => value.evaluate(target_address, symtab, rc_updater, op),
            Atom::Parens(_span, _script, expr) => {
                expr.evaluate(target_address, symtab, rc_updater, op)
            }
            Atom::RcRef(_span, registers_containing) => {
                registers_containing.evaluate(target_address, symtab, rc_updater, op)
            }
        }
    }
}

impl Evaluate for SignedAtom {
    fn evaluate<R: RcUpdater>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.magnitude
            .evaluate(target_address, symtab, rc_updater, op)
            .map(|magnitude| {
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
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            SymbolOrLiteral::Symbol(script, symbol_name, span) => symbol_name_lookup(
                symbol_name,
                *script,
                *span,
                target_address,
                symtab,
                rc_updater,
                op,
            ),
            SymbolOrLiteral::Literal(literal_value) => {
                literal_value.evaluate(target_address, symtab, rc_updater, op)
            }
            SymbolOrLiteral::Here(script, span) => target_address
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
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.fragment
            .evaluate(target_address, symtab, rc_updater, op)
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

fn translate_symbol_lookup_failure(
    source_file_body: &str,
    here: &HereValue,
    e: SymbolLookupFailure,
    undefined_symbols: &mut Vec<(Span, SymbolName)>,
) -> Result<(), AssemblerFailure> {
    use SymbolLookupFailureKind::*;
    match &e.target {
        LookupTarget::Symbol(name, span) => {
            undefined_symbols.push((*span, name.clone()));
        }
        _ => {
            unreachable!("unexpected error {e:?} for translate_symbol_lookup_failure");
        }
    }
    match e.kind {
        Missing { .. } | Loop { .. } => Ok(()),
        HereIsNotAllowedHere => {
            unreachable!("should be able to use # where target_address={here:?}");
        }
        InconsistentOrigins { name, span, msg } => Err(AssemblerFailure::BadProgram(vec![(
            source_file_body,
            ProgramError::InconsistentOriginDefinitions {
                origin_name: name,
                span,
                msg,
            },
        )
            .into()])),
        MachineLimitExceeded(e) => Err(AssemblerFailure::MachineLimitExceeded(e)),
    }
}

pub(super) fn extract_final_equalities<R: RcUpdater>(
    equalities: &[Equality],
    body: &str,
    symtab: &mut SymbolTable,
    rc_updater: &mut R,
    final_symbols: &mut FinalSymbolTable,
) -> Result<(), AssemblerFailure> {
    let mut undefined_symbols: Vec<(Span, SymbolName)> = Vec::new();
    for eq in equalities {
        let mut op = Default::default();
        match eq
            .value
            .evaluate(&HereValue::NotAllowed, symtab, rc_updater, &mut op)
        {
            Ok(value) => {
                final_symbols.define(
                    eq.name.clone(),
                    FinalSymbolType::Equality,
                    extract_span(body, &eq.span).trim().to_string(),
                    FinalSymbolDefinition::PositionIndependent(value),
                );
            }
            Err(SymbolLookupFailure {
                target: _,
                kind: SymbolLookupFailureKind::HereIsNotAllowedHere,
            }) => {
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
                translate_symbol_lookup_failure(
                    body,
                    &HereValue::NotAllowed,
                    e,
                    &mut undefined_symbols,
                )?;
            }
        }
    }
    Ok(())
}

impl LocatedBlock {
    pub(super) fn build_binary_block<R: RcUpdater>(
        &self,
        location: Address,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &str,
        listing: &mut Listing,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        self.statements.build_binary_block(
            location,
            symtab,
            rc_updater,
            final_symbols,
            body,
            listing,
        )
    }
}

impl InstructionSequence {
    pub(super) fn build_binary_block<R: RcUpdater>(
        &self,
        location: Address,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        final_symbols: &mut FinalSymbolTable,
        body: &str,
        listing: &mut Listing,
    ) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
        let mut undefined_symbols: Vec<(Span, SymbolName)> = Vec::new();
        let mut words: Vec<Unsigned36Bit> = Vec::with_capacity(self.emitted_word_count().into());
        for (offset, instruction) in self.iter().enumerate() {
            let offset: Unsigned18Bit = Unsigned18Bit::try_from(offset)
                .expect("assembled code block should fit within physical memory");
            let address: Address = location.index_by(offset);
            let here = HereValue::Address(address);
            for tag in instruction.tags.iter() {
                final_symbols.define(
                    tag.name.clone(),
                    FinalSymbolType::Tag,
                    extract_span(body, &tag.span).trim().to_string(),
                    FinalSymbolDefinition::PositionIndependent(address.into()),
                );
            }
            let mut op = Default::default();
            match instruction.evaluate(&here, symtab, rc_updater, &mut op) {
                Ok(word) => {
                    listing.push_line(ListingLine {
                        origin: None,
                        span: Some(instruction.span),
                        rc_source: None,
                        content: Some((address, word)),
                    });
                    words.push(word);
                }
                Err(e) => {
                    translate_symbol_lookup_failure(body, &here, e, &mut undefined_symbols)?;
                }
            }
        }
        if !undefined_symbols.is_empty() {
            return Err(AssemblerFailure::BadProgram(
                undefined_symbols
                    .into_iter()
                    .map(|(span, name)| {
                        let e = ProgramError::UnexpectedlyUndefinedSymbol { name, span };
                        (body, e).into()
                    })
                    .collect(),
            ));
        }
        Ok(words)
    }
}

impl Evaluate for RegistersContaining {
    fn evaluate<R: RcUpdater>(
        &self,
        _target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let mut first_addr: Option<Unsigned36Bit> = None;
        for rc_word in self.words() {
            // Evaluation of the RegisterContaining value will compute
            // a correct here-value, we don't need to pass it in.  But
            // we can't pass None, and so instead we pass NotAllowed
            // so that if a bug is introduced we will see a failure
            // rather than an incorrect result.
            let must_recompute_here_address = HereValue::NotAllowed;
            let addr: Unsigned36Bit =
                rc_word.evaluate(&must_recompute_here_address, symtab, rc_updater, op)?;
            if first_addr.is_none() {
                first_addr = Some(addr);
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
        _target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_updater: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            RegisterContaining::Unallocated(_) => {
                unreachable!(
                    "evaluate() called on RegisterContaining instance {self:?} before it was allocated"
                );
            }
            RegisterContaining::Allocated(rc_word_addr, inst) => {
                // Within the RC-word, # ("here") resolves to the
                // address of the RC-word itself.  So before we
                // evaluate the value to be placed in the RC-word,
                // we need to know the value that # will take
                // during the evaluation process.
                let here = HereValue::Address(*rc_word_addr);

                // If inst has a tag, we temporarily override any
                // global value for that tag with the address of
                // this instruction.
                let tag_overrides: BTreeMap<&Tag, Address> =
                    inst.tags.iter().map(|t| (t, *rc_word_addr)).collect();
                let value: Unsigned36Bit = symtab.evaluate_with_temporary_tag_overrides(
                    tag_overrides,
                    inst.as_ref(),
                    &here,
                    rc_updater,
                    op,
                )?;
                rc_updater.update(*rc_word_addr, value);
                Ok(Unsigned36Bit::from(rc_word_addr))
            }
        }
    }
}

impl LocatedBlock {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.statements.assign_rc_words(symtab, rc_allocator)
    }
}

impl TaggedProgramInstruction {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.instruction.assign_rc_words(symtab, rc_allocator)
    }
}

impl UntaggedProgramInstruction {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        for inst in self.fragments.iter_mut() {
            inst.assign_rc_words(symtab, rc_allocator)?;
        }
        Ok(())
    }
}

impl CommaDelimitedFragment {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.fragment.assign_rc_words(symtab, rc_allocator)
    }
}

impl InstructionFragment {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        use InstructionFragment::*;
        match self {
            Null(_) | DeferredAddressing(_) => Ok(()),
            Arithmetic(expr) => expr.assign_rc_words(symtab, rc_allocator),
            Config(cfg) => cfg.assign_rc_words(symtab, rc_allocator),
            PipeConstruct {
                index: _,
                rc_word_span,
                rc_word_value,
            } => {
                let span: Span = *rc_word_span;
                let w = rc_word_value.clone();
                *rc_word_value =
                    w.assign_rc_word(RcWordSource::PipeConstruct(span), symtab, rc_allocator)?;
                Ok(())
            }
        }
    }
}

impl RegisterContaining {
    pub(crate) fn assign_rc_word<R: RcAllocator>(
        self,
        source: RcWordSource,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<RegisterContaining, RcWordAllocationFailure> {
        match self {
            RegisterContaining::Unallocated(mut tpibox) => {
                let addr: Address = rc_allocator.allocate(source, Unsigned36Bit::ZERO)?;
                tpibox.assign_rc_words(symtab, rc_allocator)?;
                let tpi: Box<TaggedProgramInstruction> = tpibox;
                Ok(RegisterContaining::Allocated(addr, tpi))
            }
            other => Ok(other),
        }
    }
}

impl RegistersContaining {
    pub(crate) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        span: Span,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        let source = RcWordSource::Braces(span);
        for rc in self.words_mut() {
            *rc = rc
                .clone()
                .assign_rc_word(source.clone(), symtab, rc_allocator)?;
        }
        Ok(())
    }
}

impl ArithmeticExpression {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.first.assign_rc_words(symtab, rc_allocator)?;
        for (_op, atom) in self.tail.iter_mut() {
            atom.assign_rc_words(symtab, rc_allocator)?;
        }
        Ok(())
    }
}

impl ConfigValue {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.expr.assign_rc_words(symtab, rc_allocator)
    }
}

impl SignedAtom {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        self.magnitude.assign_rc_words(symtab, rc_allocator)
    }
}

impl Atom {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        match self {
            Atom::SymbolOrLiteral(thing) => thing.assign_rc_words(symtab, rc_allocator),
            Atom::Parens(_, _, expr) => expr.assign_rc_words(symtab, rc_allocator),
            Atom::RcRef(span, rc) => rc.assign_rc_words(*span, symtab, rc_allocator),
        }
    }
}

impl SymbolOrLiteral {
    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        _symtab: &mut SymbolTable,
        _rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        Ok(())
    }
}
