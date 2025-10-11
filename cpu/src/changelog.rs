//! A collection of orderable values which the caller can efficiently
//! drain in one go.
use serde::Serialize;
use std::collections::BTreeSet;

/// Efficiently accumulate as set of things and then return all the
/// members of the set.
#[derive(Debug, Serialize)]
pub(crate) struct ChangeIndex<K: Ord + Serialize> {
    changes: BTreeSet<K>,
}

impl<K: Ord + Serialize> Default for ChangeIndex<K> {
    // Cannot use derive for Default because that would require K to
    // implement Derive, while in reality it doesn't need to.
    fn default() -> Self {
        Self {
            changes: BTreeSet::new(),
        }
    }
}

impl<K: Ord + Serialize> ChangeIndex<K> {
    pub(crate) fn add(&mut self, k: K) {
        self.changes.insert(k);
    }

    pub(crate) fn drain(&mut self) -> BTreeSet<K> {
        let mut result: BTreeSet<_> = BTreeSet::new();
        result.append(&mut self.changes);
        result
    }
}
