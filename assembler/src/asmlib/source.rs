//! Representation of the original input.
use std::fmt::{self, Display, Formatter};
use std::ops::Range;

#[derive(Debug)]
pub(super) struct Source<'s> {
    body: &'s str,
}

impl<'s> Source<'s> {
    pub(super) fn new(body: &'s str) -> Source<'s> {
        Source { body }
    }

    pub(super) fn as_str(&self) -> &str {
        self.body
    }

    pub(super) fn extract(&self, range: Range<usize>) -> &str {
        &self.body[range]
    }

    pub(super) fn location_of(&self, pos: usize) -> LineAndColumn {
        const START_COL: u32 = 1;
        const START_LINE: u32 = 1;

        let mut line = START_LINE;
        let mut column = START_COL;
        for (i, ch) in self.body.char_indices() {
            if i == pos {
                break;
            }
            match ch {
                '\n' => {
                    column = START_COL;
                    line += 1;
                }
                _ => {
                    column += 1;
                }
            }
        }
        LineAndColumn { line, column }
    }

    pub(crate) fn extract_prefix(&self, pos: usize) -> &'s str {
        let body_prefix = &self.body[0..pos];
        let line_start = match body_prefix.rfind('\n') {
            None => 0,
            Some(n) => n + 1,
        };
        let prefix = &self.body[line_start..pos];
        if prefix.chars().all(char::is_whitespace) {
            prefix
        } else {
            ""
        }
    }
}

#[test]
fn test_extract_prefix() {
    fn extract_prefix(s: &str, pos: usize) -> &str {
        let src = Source::new(s);
        src.extract_prefix(pos)
    }

    assert_eq!(extract_prefix("hello", 0), "");
    assert_eq!(extract_prefix(" hello", 0), "");
    assert_eq!(extract_prefix(" hello", 1), " ");
    assert_eq!(extract_prefix("x\nhello", 2), "");
    assert_eq!(extract_prefix("x\n hello", 3), " ");
    assert_eq!(extract_prefix("x\nY hello", 4), "");
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct LineAndColumn {
    line: u32,
    column: u32,
}

impl Display for LineAndColumn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, column {}", self.line, self.column)
    }
}

pub trait Located {
    fn location(&self) -> LineAndColumn;
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct WithLocation<T> {
    pub(crate) inner: T,
    pub(crate) location: LineAndColumn,
}

impl<T> Located for WithLocation<T> {
    fn location(&self) -> LineAndColumn {
        self.location.clone()
    }
}

impl<T: Located> From<T> for WithLocation<T> {
    fn from(inner: T) -> WithLocation<T> {
        WithLocation {
            location: inner.location().clone(),
            inner,
        }
    }
}

impl<T> WithLocation<T> {
    pub fn location(&self) -> &LineAndColumn {
        &self.location
    }
}

impl<T: Display> Display for WithLocation<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", &self.location, &self.inner)
    }
}
