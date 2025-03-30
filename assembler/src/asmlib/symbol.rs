use std::fmt::{self, Debug, Display, Formatter, Write};
use std::hash::{Hash, Hasher};

#[derive(Clone, Eq, PartialOrd, Ord)]
pub struct SymbolName {
    pub(crate) canonical: String,
    // pub(crate) as_used: String,
}

impl From<String> for SymbolName {
    fn from(s: String) -> SymbolName {
        SymbolName { canonical: s }
    }
}

impl Display for SymbolName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.canonical, f)
    }
}

impl Debug for SymbolName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "SymbolName {{ canonical: \"{}\" }}", self.canonical)
    }
}

impl PartialEq for SymbolName {
    fn eq(&self, other: &SymbolName) -> bool {
        self.canonical.eq(&other.canonical)
    }
}

impl Hash for SymbolName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical.hash(state)
    }
}

#[derive(Clone, Eq, PartialOrd, Ord, PartialEq, Debug)]
pub(crate) enum SymbolOrHere {
    Named(SymbolName),
    Here,
}

impl From<&str> for SymbolOrHere {
    fn from(value: &str) -> Self {
        match value {
            "#" => SymbolOrHere::Here,
            name => SymbolOrHere::Named(SymbolName {
                canonical: name.to_owned(),
            }),
        }
    }
}

impl Display for SymbolOrHere {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolOrHere::Named(name) => write!(f, "{name}"),
            SymbolOrHere::Here => f.write_char('#'),
        }
    }
}
