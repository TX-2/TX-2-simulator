#![allow(dead_code)]
// TODO: once we've resolved all the test compilation errors, resinstate the dead_code warning.

/// terminal contains all the terminals of the grammar; that is, the
/// lowest-level symbols not defined in terms of anything else in the
/// grammar.
use chumsky::input::ValueInput;
use chumsky::prelude::*;

use super::super::ast::Operator;
use super::{Extra, Span, Tok};
use base::charset::Script;

pub(super) fn end_of_input<'a, I>() -> impl Parser<'a, I, (), Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + Clone,
{
    chumsky::prelude::end().labelled("end-of-input")
}

pub(super) fn operator<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, Operator, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        // Solidus ("/") is used for divide.  See section 6-2.7
        // "Word Assembly" for details.
        // TODO: support subscript/superscript for '/'
        Tok::Solidus if script_required == Script::Normal => Operator::Divide,
        Tok::Plus(Script::Normal) => Operator::Add,
        // TODO: support subscript/superscript for times
        Tok::Times if script_required == Script::Normal => Operator::Multiply,
        Tok::LogicalOr(got) if got == script_required => Operator::LogicalOr,
        Tok::LogicalAnd(got) if got == script_required => Operator::LogicalAnd,
        Tok::Minus(got) if script_required == got => Operator::Subtract,
        Tok::Plus(got) if script_required == got => Operator::Add,
    }
    .labelled("arithmetic operator")
}
