/// A symbol which has a reference but no definition is known, will
/// ben represented it by having it map to None.  The rules for how
/// such symbols are assigned values are indicated in "Unassigned
/// Symexes" in section 6-2.2 of the User Handbook.
#[derive(Debug)]
pub(crate) struct SymbolTable {}
impl SymbolTable {
    pub(crate) fn new() -> SymbolTable {
        SymbolTable {}
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        true
    }

    pub(crate) fn list(&self) -> Result<(), std::io::Error> {
        Ok(())
    }
}
