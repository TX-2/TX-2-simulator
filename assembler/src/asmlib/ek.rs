// Code derived from an example by Eyal Kalderon;
// copied from https://github.com/ebkalderon/example-fault-tolerant-parser/commit/5f64f73055527c389c22d9fff30ee1adc72e6dbc#diff-42cb6807ad74b3e201c5a7ca98b911c5fa08380e942be6e4ac5807f8377f87fc
// Code is "unlicense" licensed code.

use std::cell::RefCell;
use std::ops::Range;

use nom::character::complete::anychar;
use nom::combinator::{all_consuming, map, not, rest};
use nom::sequence::preceded;

use crate::parser::ErrorLocation;
use crate::state::{Error, State, StateExtra};

pub type LocatedSpan<'a, 'b> = nom_locate::LocatedSpan<&'a str, StateExtra<'b>>;
pub type IResult<'a, 'b, T> = nom::IResult<LocatedSpan<'a, 'b>, T>;

pub trait ToRange {
    fn to_range(&self) -> Range<usize>;
}

impl<'a, 'b> ToRange for LocatedSpan<'a, 'b> {
    fn to_range(&self) -> Range<usize> {
        let start = self.location_offset();
        let end = start + self.fragment().len();
        start..end
    }
}

pub fn expect<'a, 'b, F, E, T>(
    parser: F,
    error_msg: E,
) -> impl Fn(LocatedSpan<'a, 'b>) -> IResult<'a, 'b, Option<T>>
where
    F: Fn(LocatedSpan<'a, 'b>) -> IResult<'a, 'b, T>,
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

pub(crate) fn expect_end_of_file<'a, 'b>(body: LocatedSpan<'a, 'b>) -> IResult<'a, 'b, ()> {
    map(
        preceded(expect(not(anychar), "expected end-of-file"), rest),
        |_| (),
    )(body)
}

pub(crate) fn parse_with<'a, T, F, M>(
    input_text: &'a str,
    parser: F,
    mut state_setup: M,
) -> (T, Vec<Error>)
where
    F: for<'b> Fn(LocatedSpan<'a, 'b>) -> IResult<'a, 'b, T>,
    M: FnMut(&mut State),
{
    let mut state: State = State::new();
    state_setup(&mut state);
    let rstate = RefCell::new(state);
    let input: LocatedSpan<'a, '_> = LocatedSpan::new_extra(input_text, StateExtra::new(&rstate));
    let (_, output) = all_consuming(parser)(input).expect("parser cannot fail");
    (output, rstate.into_inner().errors)
}

#[cfg(test)]
pub(crate) fn parse_partially_with<'a, T, F>(
    input_text: &'a str,
    parser: F,
) -> (&'a str, T, Vec<Error>)
where
    F: for<'b> Fn(LocatedSpan<'a, 'b>) -> IResult<'a, 'b, T>,
{
    let state: State = State::new();
    //state_setup(&mut state.borrow_mut());
    let rstate = RefCell::new(state);
    let input: LocatedSpan<'a, '_> = LocatedSpan::new_extra(input_text, StateExtra::new(&rstate));
    let (tail, output) = parser(input).expect("parser cannot fail");
    (tail.fragment(), output, rstate.into_inner().errors)
}
