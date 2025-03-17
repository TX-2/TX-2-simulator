use std::{ops::Deref, sync::OnceLock};

use regex::Regex;

pub(crate) struct LazyRegex {
    once: OnceLock<Regex>,
    pattern: &'static str,
}

impl LazyRegex {
    pub(crate) const fn new(pattern: &'static str) -> Self {
        LazyRegex {
            once: OnceLock::new(),
            pattern,
        }
    }
}

impl Deref for LazyRegex {
    type Target = Regex;

    fn deref(&self) -> &Regex {
        self.once.get_or_init(|| match Regex::new(self.pattern) {
            Ok(r) => r,
            Err(e) => {
                panic!("'{}' is not a valid regular expression: {e}", self.pattern,);
            }
        })
    }
}
