// Code derived from an example by Eyal Kalderon;
// copied from https://github.com/ebkalderon/example-fault-tolerant-parser/commit/5f64f73055527c389c22d9fff30ee1adc72e6dbc#diff-42cb6807ad74b3e201c5a7ca98b911c5fa08380e942be6e4ac5807f8377f87fc
// Code is "unlicense" licensed code.

use std::cell::RefCell;
use std::ops::Range;

use nom::branch::alt;
use nom::bytes::complete::take;
use nom::character::complete::anychar;
use nom::combinator::{all_consuming, map, not, rest};
use nom::sequence::{preceded, terminated};

use crate::parser::{program_instruction, ErrorLocation, ProgramInstruction};

pub type LocatedSpan<'a> = nom_locate::LocatedSpan<&'a str, State<'a>>;
pub type IResult<'a, T> = nom::IResult<LocatedSpan<'a>, T>;

pub trait ToRange {
    fn to_range(&self) -> Range<usize>;
}

impl<'a> ToRange for LocatedSpan<'a> {
    fn to_range(&self) -> Range<usize> {
        let start = self.location_offset();
        let end = start + self.fragment().len();
        start..end
    }
}

#[derive(Debug)]
pub struct Error(pub ErrorLocation, pub String);

#[derive(Clone, Debug)]
pub struct State<'a>(&'a RefCell<Vec<Error>>);

impl<'a> State<'a> {
    pub fn report_error(&self, error: Error) {
        self.0.borrow_mut().push(error);
    }
}

fn expect<'a, F, E, T>(parser: F, error_msg: E) -> impl Fn(LocatedSpan<'a>) -> IResult<Option<T>>
where
    F: Fn(LocatedSpan<'a>) -> IResult<T>,
    E: ToString,
{
    move |input| match parser(input) {
        Ok((remaining, out)) => Ok((remaining, Some(out))),
        Err(nom::Err::Error((input, _))) | Err(nom::Err::Failure((input, _))) => {
            let err = Error(ErrorLocation::from(&input), error_msg.to_string());
            input.extra.report_error(err);
            Ok((input, None))
        }
        Err(err) => Err(err),
    }
}

fn source_line(line: LocatedSpan) -> IResult<ProgramInstruction> {
    let expr = alt((
        program_instruction,
        map(take(0usize), |_| {
            ProgramInstruction::empty_line_representation()
        }),
    ));
    let result = terminated(
        expr,
        preceded(expect(not(anychar), "expected end-of-line"), rest),
    )(line);
    // dbg!(&result);
    result
}

pub fn parse(_line_number: usize, input: &str) -> (ProgramInstruction, Vec<Error>) {
    let errors = RefCell::new(Vec::new());
    let input = LocatedSpan::new_extra(input, State(&errors));
    let (_, expr) = all_consuming(source_line)(input).expect("parser cannot fail");
    (expr, errors.into_inner())
}
