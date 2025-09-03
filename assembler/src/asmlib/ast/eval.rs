use super::super::eval::{Evaluate, ScopeIdentifier};
use super::*;

impl Evaluate for LiteralValue {
    fn evaluate<R: RcUpdater>(
        &self,
        _ctx: &mut EvaluationContext<R>,
        _scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        Ok(self.value())
    }
}

impl Evaluate for SignedAtom {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.magnitude.evaluate(ctx, scope).map(|magnitude| {
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

impl Evaluate for ArithmeticExpression {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let first: Unsigned36Bit = self.first.evaluate(ctx, scope)?;
        let result: Result<Unsigned36Bit, SymbolLookupFailure> = self
            .tail
            .iter()
            .try_fold(first, |acc, curr| fold_step(acc, curr, ctx, scope));
        result
    }
}

impl Evaluate for ConfigValue {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // The `expr` member was either originally in superscript (in
        // which case the `evaluate` value will already have been
        // shifted into the correct position in the word, or in normal
        // script (in which case we need to shift it ourselves).
        let shift = if self.already_superscript { 0 } else { 30u32 };
        self.expr.evaluate(ctx, scope).map(|value| value.shl(shift))
    }
}

impl Evaluate for RegistersContaining {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let mut first_addr: Option<Unsigned36Bit> = None;
        for rc_word in self.words() {
            // Evaluation of the RegisterContaining value will compute
            // a correct here-value, we don't need to pass it in.  But
            // we can't pass None, and so instead we pass NotAllowed
            // so that if a bug is introduced we will see a failure
            // rather than an incorrect result.
            let address: Unsigned36Bit = ctx
                .for_target_address(HereValue::NotAllowed, |newctx| {
                    rc_word.evaluate(newctx, scope)
                })?;
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
        scope: ScopeIdentifier,
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
                        inst.evaluate(newctx, scope)
                    })?;
                ctx.rc_updater.update(*rc_word_addr, rc_word_value);
                Ok(Unsigned36Bit::from(rc_word_addr))
            }
        }
    }
}

impl Evaluate for Atom {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Atom::SymbolOrLiteral(value) => value.evaluate(ctx, scope),
            Atom::Parens(_span, _script, expr) => expr.evaluate(ctx, scope),
            Atom::RcRef(_span, registers_containing) => registers_containing.evaluate(ctx, scope),
        }
    }
}

impl Evaluate for SymbolOrLiteral {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            SymbolOrLiteral::Symbol(script, symbol_name, span) => {
                symbol_name_lookup(symbol_name, *script, *span, ctx, scope)
            }
            SymbolOrLiteral::Literal(literal_value) => literal_value.evaluate(ctx, scope),
            SymbolOrLiteral::Here(script, span) => ctx
                .here
                .get_address(span)
                .map(|addr: Address| Unsigned36Bit::from(addr))
                .map(|addr_value: Unsigned36Bit| addr_value.shl(script.shift())),
        }
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            InstructionFragment::Null(_) => Ok(Unsigned36Bit::ZERO),
            InstructionFragment::Arithmetic(expr) => expr.evaluate(ctx, scope),
            InstructionFragment::DeferredAddressing(_) => Ok(DEFER_BIT),
            InstructionFragment::Config(value) => value.evaluate(ctx, scope),
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
                let p_value: Unsigned36Bit = p.item.evaluate(ctx, scope)?;
                let rc_word_addr: Unsigned36Bit = rc_word_value.evaluate(ctx, scope)?;
                Ok(combine_fragment_values(
                    combine_fragment_values(p_value, rc_word_addr),
                    DEFER_BIT,
                ))
            }
        }
    }
}

impl Evaluate for Origin {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Origin::Deduced(_span, _, address) | Origin::Literal(_span, address) => {
                Ok(address.into())
            }
            Origin::Symbolic(span, symbol_name) => {
                symbol_name_lookup(symbol_name, Script::Normal, *span, ctx, scope)
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

impl Evaluate for CommaDelimitedFragment {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.fragment
            .evaluate(ctx, scope)
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

/// The Users Handbook implies that instruction fragments are added
/// together, and I am not sure whether they mean this literally (as
/// in, addition) or figuratively (as in a logica-or operation).  This
/// function exists to be a single place to encode this assumption.
fn combine_fragment_values(left: Unsigned36Bit, right: Unsigned36Bit) -> Unsigned36Bit {
    left | right
}

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        fn evaluate_and_combine_values<'a, R, E, I>(
            mut items: I,
            ctx: &mut EvaluationContext<R>,
            scope: ScopeIdentifier,
        ) -> Result<Unsigned36Bit, SymbolLookupFailure>
        where
            R: RcUpdater,
            E: Evaluate + 'a,
            I: Iterator<Item = &'a E>,
        {
            items.try_fold(Unsigned36Bit::ZERO, |acc, item| {
                item.evaluate(ctx, scope)
                    .map(|value| combine_fragment_values(acc, value))
            })
        }

        // Comma delimited values are evaluated left-to-right, as stated in item
        // (b) in section 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of
        // the Users Handbook.  The initial value is zero (as
        // specified in item (a) in the same place).
        evaluate_and_combine_values(self.fragments.iter(), ctx, scope)
    }
}

impl Evaluate for EqualityValue {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.inner.evaluate(ctx, scope)
    }
}

impl Evaluate for TaggedProgramInstruction {
    fn evaluate<R: RcUpdater>(
        &self,
        ctx: &mut EvaluationContext<R>,
        scope: ScopeIdentifier,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction.evaluate(ctx, scope)
    }
}

#[cfg(test)]
mod comma_tests {
    use super::comma_transformation;
    use super::*;
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
