use std::collections::BTreeMap;
use std::fmt::Debug;

use chumsky::{inspector::Inspector, prelude::Input};

use super::ast::MacroDefinition;
use super::symbol::SymbolName;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum NumeralMode {
    #[default]
    Octal,
    Decimal,
}

impl NumeralMode {
    pub(crate) fn radix(&self, alternate: bool) -> u32 {
        match (&self, alternate) {
            (&NumeralMode::Octal, false) | (&NumeralMode::Decimal, true) => 8,
            (&NumeralMode::Decimal, false) | (&NumeralMode::Octal, true) => 10,
        }
    }

    pub(crate) fn set_numeral_mode(&mut self, mode: NumeralMode) {
        *self = mode;
    }
}

#[test]
fn test_numeral_mode_default() {
    assert_eq!(NumeralMode::default(), NumeralMode::Octal);
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TruncatableMap<K: Eq, V: Eq> {
    in_insertion_order: Vec<K>,
    items: BTreeMap<K, V>,
}

impl<K: Eq, V: Eq> Default for TruncatableMap<K, V> {
    fn default() -> Self {
        TruncatableMap {
            in_insertion_order: Default::default(),
            items: BTreeMap::new(),
        }
    }
}

impl<K, V> TruncatableMap<K, V>
where
    K: Clone + Eq + Ord + Debug,
    V: Eq,
{
    pub(crate) fn insert(&mut self, k: K, v: V) {
        if self.items.insert(k.clone(), v).is_some() {
            panic!("cannot insert duplicate entry for {k:?}");
        } else {
            self.in_insertion_order.push(k);
        }
    }

    #[cfg(test)]
    pub(crate) fn get(&self, k: &K) -> Option<&V> {
        self.items.get(k)
    }

    pub(crate) fn len(&self) -> usize {
        self.in_insertion_order.len()
    }

    pub(crate) fn truncate(&mut self, newlen: usize) {
        for k in self.in_insertion_order.drain(newlen..) {
            self.items.remove(&k);
        }
    }

    pub(crate) fn map_ref(&self) -> &BTreeMap<K, V> {
        &self.items
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct State<'src> {
    pub(super) numeral_mode: NumeralMode,
    pub(super) body: &'src str,
    pub(super) macros: TruncatableMap<SymbolName, MacroDefinition>,
}

impl<'src> State<'src> {
    pub(crate) fn new(body: &'src str, numeral_mode: NumeralMode) -> State<'src> {
        State {
            numeral_mode,
            body,
            macros: Default::default(),
        }
    }

    pub(crate) fn define_macro(&mut self, definition: MacroDefinition) {
        // TODO: provide a diagnostic when a macro is redefined.
        self.macros.insert(definition.name.clone(), definition)
    }

    #[cfg(test)] // not yet used outside tests.
    pub(crate) fn get_macro_definition(&self, name: &SymbolName) -> Option<&MacroDefinition> {
        self.macros.get(name)
    }

    pub(crate) fn macros(&self) -> &BTreeMap<SymbolName, MacroDefinition> {
        self.macros.map_ref()
    }
}

impl<'src, I: Input<'src>> Inspector<'src, I> for State<'src> {
    type Checkpoint = usize;

    #[inline(always)]
    fn on_token(&mut self, _: &<I as Input<'src>>::Token) {}

    fn on_save<'parse>(
        &self,
        _cursor: &chumsky::input::Cursor<'src, 'parse, I>,
    ) -> Self::Checkpoint {
        self.macros.len()
    }

    fn on_rewind<'parse>(
        &mut self,
        marker: &chumsky::input::Checkpoint<'src, 'parse, I, Self::Checkpoint>,
    ) {
        self.macros.truncate(*marker.inspector())
    }
}
