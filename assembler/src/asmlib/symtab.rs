use std::collections::BTreeMap;

use super::ast::{Expression, SymbolName};

/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug, Default)]
pub(crate) struct SymbolTable {
    definitions: BTreeMap<SymbolName, Expression>,
}

impl SymbolTable {
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        true
    }

    pub(crate) fn define(&mut self, name: SymbolName, definition: Expression) {
        self.definitions.insert(name, definition);
    }

    pub(crate) fn list(&self) -> impl Iterator<Item = (&SymbolName, &Expression)> {
        self.definitions.iter()
    }
}
