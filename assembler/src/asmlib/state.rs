//! Represents the state of the source code parser.
//!
//! State information is:
//!
//! - Current numeric base (octal or decimal)
//! - Currently-known macro definitions
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Debug;

use chumsky::{inspector::Inspector, prelude::Input};

use super::manuscript::MacroDefinition;
use super::symbol::SymbolName;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum NumeralMode {
    #[default]
    Octal,
    Decimal,
}

impl NumeralMode {
    pub(crate) fn radix(self, alternate: bool) -> u32 {
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

pub(crate) trait MacroLookup {
    fn lookup_macro(&self, name: &SymbolName) -> Option<&MacroDefinition>;
    fn all_names(&self) -> BTreeSet<&SymbolName>;
}

#[derive(Debug, PartialEq, Eq, Default, Clone)]
pub(crate) struct MacroTable {
    macros: BTreeMap<SymbolName, Vec<MacroDefinition>>,
}

impl MacroTable {
    pub(crate) fn define_macro(&mut self, definition: MacroDefinition) {
        // TODO: provide a diagnostic when a macro is redefined.
        self.macros
            .entry(definition.name.clone())
            .or_default()
            .push(definition);
    }

    fn forget_after(&mut self, pos: usize) {
        for values in self.macros.values_mut() {
            values.retain(|macro_definition| macro_definition.span.end <= pos);
        }
    }

    fn latest(&self) -> usize {
        self.macros
            .values()
            .flat_map(|macro_definitions| macro_definitions.iter())
            .map(|macro_definition| macro_definition.span.end)
            .max()
            .unwrap_or(0)
    }
}

impl MacroLookup for MacroTable {
    fn lookup_macro(&self, name: &SymbolName) -> Option<&MacroDefinition> {
        match self.macros.get(name) {
            None => None,
            Some(values) => values.last(),
        }
    }

    fn all_names(&self) -> BTreeSet<&SymbolName> {
        self.macros.keys().collect()
    }
}

impl FromIterator<(SymbolName, MacroDefinition)> for MacroTable {
    fn from_iter<T: IntoIterator<Item = (SymbolName, MacroDefinition)>>(macros: T) -> Self {
        Self {
            macros: macros
                .into_iter()
                .map(|(name, definition)| (name, vec![definition]))
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct State<'src> {
    pub(super) numeral_mode: NumeralMode,
    pub(super) body: &'src str,
    pub(super) macros: MacroTable,
}

impl<'src> State<'src> {
    pub(crate) fn new(body: &'src str, numeral_mode: NumeralMode) -> Self {
        State {
            numeral_mode,
            body,
            macros: Default::default(),
        }
    }

    pub(crate) fn with_setup<F: FnMut(&mut Self)>(
        source_file_body: &'src str,
        mut setup: F,
    ) -> Self {
        let mut state = State::new(source_file_body, NumeralMode::default());
        setup(&mut state);
        state
    }

    pub(crate) fn define_macro(&mut self, definition: MacroDefinition) {
        self.macros.define_macro(definition);
    }

    pub(crate) fn get_macro_definition(&self, name: &SymbolName) -> Option<&MacroDefinition> {
        self.macros.lookup_macro(name)
    }

    pub(crate) fn macros(&self) -> &impl MacroLookup {
        &self.macros
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
        self.macros.latest()
    }

    fn on_rewind<'parse>(
        &mut self,
        marker: &chumsky::input::Checkpoint<'src, 'parse, I, Self::Checkpoint>,
    ) {
        let pos: usize = *marker.inspector();
        self.macros.forget_after(pos);
    }
}
