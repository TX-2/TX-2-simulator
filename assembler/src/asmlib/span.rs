use chumsky::prelude::SimpleSpan;
use std::ops::Range;

pub(crate) type Span = SimpleSpan;

pub(crate) fn span(range: Range<usize>) -> Span {
    Span::from(range)
}
