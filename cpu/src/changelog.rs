use serde::Serialize;
use std::collections::BTreeSet;

use crate::alarm::AlarmKind;

#[derive(Debug, Serialize)]
pub enum Change {}

#[derive(Debug, Serialize, Default)]
pub struct ChangeIndex {
    alarm_changes: BTreeSet<AlarmKind>,
}

impl ChangeIndex {
    pub fn alarm_changed(&mut self, kind: AlarmKind) {
        self.alarm_changes.insert(kind);
    }

    pub fn drain_alarm_changes(&mut self) -> BTreeSet<AlarmKind> {
        let mut result: BTreeSet<AlarmKind> = BTreeSet::new();
        result.append(&mut self.alarm_changes);
        result
    }
}
