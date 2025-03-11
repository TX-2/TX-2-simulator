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
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a> + Clone,
{
    match script_required {
        Script::Normal => select! {
            Tok::LogicalOr => Operator::LogicalOr,
            Tok::LogicalAnd => Operator::LogicalAnd,
            Tok::Plus => Operator::Add,
            Tok::Minus => Operator::Subtract,
            Tok::Times => Operator::Multiply,
            // Solidus ("/") is used for divide.  See section 6-2.7
            // "Word Assembly" for details.
            Tok::Solidus => Operator::Divide,
        },
        _ => unimplemented!("binary operators in superscript or subscript"),
    }
    .labelled("arithmetic operator")
}
