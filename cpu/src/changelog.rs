use serde::Serialize;
use std::collections::BTreeSet;

use crate::alarm::AlarmKind;
use base::prelude::*;

#[derive(Debug, Serialize, Default)]
pub struct ChangeIndex {
    alarm_changes: BTreeSet<AlarmKind>,
    device_changes: BTreeSet<Unsigned6Bit>,
}

impl ChangeIndex {
    pub fn alarm_changed(&mut self, kind: AlarmKind) {
        self.alarm_changes.insert(kind);
    }

    pub fn device_changed(&mut self, dev: Unsigned6Bit) {
        self.device_changes.insert(dev);
    }

    pub fn drain_alarm_changes(&mut self) -> BTreeSet<AlarmKind> {
        let mut result: BTreeSet<_> = BTreeSet::new();
        result.append(&mut self.alarm_changes);
        result
    }

    pub fn drain_device_changes(&mut self) -> BTreeSet<Unsigned6Bit> {
        let mut result: BTreeSet<_> = BTreeSet::new();
        result.append(&mut self.device_changes);
        result
    }
}
