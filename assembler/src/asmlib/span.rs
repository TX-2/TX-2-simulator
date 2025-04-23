use chumsky::prelude::SimpleSpan;
use std::ops::Range;

pub(crate) type Span = SimpleSpan;

pub(crate) fn span(range: Range<usize>) -> Span {
    Span::from(range)
}

pub(crate) fn extract_span<'a>(body: &'a str, span: &Span) -> &'a str {
    &body[span.start..span.end]
}

pub(crate) fn extract_prefix(body: &str, pos: usize) -> &str {
    let body_prefix = &body[0..pos];
    let line_start = match body_prefix.rfind('\n') {
        None => 0,
        Some(n) => n + 1,
    };
    let prefix = &body[line_start..pos];
    if prefix.chars().all(|ch| ch.is_whitespace()) {
        prefix
    } else {
        ""
    }
}

#[test]
fn test_extract_prefix() {
    assert_eq!(extract_prefix("hello", 0), "");
    assert_eq!(extract_prefix(" hello", 0), "");
    assert_eq!(extract_prefix(" hello", 1), " ");
    assert_eq!(extract_prefix("x\nhello", 2), "");
    assert_eq!(extract_prefix("x\n hello", 3), " ");
    assert_eq!(extract_prefix("x\nY hello", 4), "");
}
