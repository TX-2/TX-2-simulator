use chumsky::prelude::SimpleSpan;
use std::ops::Range;

pub(crate) type Span = SimpleSpan;

pub(crate) trait Spanned {
    fn span(&self) -> Span;
}

pub(crate) fn span(range: Range<usize>) -> Span {
    Span::from(range)
}

#[derive(Debug, Clone)]
pub(crate) struct OrderableSpan(pub(crate) Span);

impl From<Span> for OrderableSpan {
    fn from(span: Span) -> OrderableSpan {
        OrderableSpan(span)
    }
}

impl Ord for OrderableSpan {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.start.cmp(&other.0.start)
    }
}

impl PartialOrd for OrderableSpan {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for OrderableSpan {
    fn eq(&self, other: &Self) -> bool {
        self.0.start.cmp(&other.0.start).is_eq()
    }
}

impl Eq for OrderableSpan {}

impl OrderableSpan {
    pub(super) fn as_span(&self) -> &Span {
        &self.0
    }
}
