//! The TX-2 can "mask" some alarms, and whether or not this is
//! happening is controlled by the AlarmUnit.
use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use tracing::{Level, event};

use super::alarm::{Alarm, AlarmDetails, AlarmKind, AlarmMaskability, Alarmer, BugActivity};
use super::changelog::ChangeIndex;
use super::diagnostics::DiagnosticFetcher;
use crate::diagnostics::CurrentInstructionDiagnostics;

#[cfg(test)]
use base::Unsigned6Bit;

#[derive(Debug, Serialize)]
pub struct AlarmStatus {
    pub name: String,
    pub maskable: bool,
    pub masked: bool,
    pub active: bool,
    pub message: String,
}

/// An alarm is in one of the following states:
///
/// - inactive: it's not happening
/// - firing: it's happening and not masked (execution will stop)
/// - active but not firing (visible on the console, execution continues)
#[derive(Debug, Default)]
pub struct AlarmUnit {
    panic_on_unmasked_alarm: bool,
    masked: BTreeSet<AlarmKind>,
    active: BTreeMap<AlarmKind, Alarm>,
    changes: ChangeIndex<AlarmKind>,
}

impl AlarmUnit {
    pub fn new() -> AlarmUnit {
        AlarmUnit::default()
    }

    fn status_for_alarm_kind(&self, kind: &AlarmKind) -> AlarmStatus {
        let maybe_firing_alarm: Option<&Alarm> = self.active.get(kind);
        AlarmStatus {
            name: kind.to_string(),
            maskable: matches!(kind.maskable(), AlarmMaskability::Maskable),
            masked: self.masked.contains(kind),
            active: maybe_firing_alarm.is_some(),
            message: match maybe_firing_alarm {
                Some(a) => a.to_string(),
                None => String::new(),
            },
        }
    }

    pub fn get_alarm_statuses(&self) -> Vec<AlarmStatus> {
        AlarmKind::all_alarm_kinds()
            .iter()
            .map(|kind| self.status_for_alarm_kind(kind))
            .collect()
    }

    pub fn drain_alarm_changes(&mut self) -> BTreeMap<AlarmKind, AlarmStatus> {
        self.changes
            .drain()
            .into_iter()
            .map(|kind| (kind, self.status_for_alarm_kind(&kind)))
            .collect()
    }

    pub fn get_status_of_alarm(&self, name: &str) -> Option<AlarmStatus> {
        AlarmKind::try_from(name)
            .map(|k| self.status_for_alarm_kind(&k))
            .ok()
    }

    pub fn new_with_panic(panic: bool) -> AlarmUnit {
        AlarmUnit {
            panic_on_unmasked_alarm: panic,
            ..AlarmUnit::new()
        }
    }

    pub fn mask(
        &mut self,
        kind: AlarmKind,
        diags: &CurrentInstructionDiagnostics,
    ) -> Result<(), Alarm> {
        match kind.maskable() {
            AlarmMaskability::Unmaskable => {
                let bug = Alarm {
                    sequence: None,
                    details: AlarmDetails::BUGAL {
                        activity: BugActivity::AlarmHandling,
                        diagnostics: diags.clone(),
                        message: format!("attempt to mask unmaskable alarm {kind}"),
                    },
                };
                Err(self.always_fire(bug, diags))
            }
            AlarmMaskability::Maskable => {
                self.changes.add(kind);
                self.masked.insert(kind);
                Ok(())
            }
        }
    }

    pub fn unmask(&mut self, kind: AlarmKind) {
        if self.masked.remove(&kind) {
            self.changes.add(kind);
        }
    }

    fn is_masked(&self, alarm_instance: &Alarm) -> bool {
        let kind = alarm_instance.kind();
        match kind.maskable() {
            AlarmMaskability::Unmaskable => false,
            AlarmMaskability::Maskable => {
                // TODO: is this correct for writes to un-mapped
                // memory?
                self.masked.contains(&kind)
            }
        }
    }

    fn maybe_panic(&self, alarm_instance: &Alarm) {
        if self.panic_on_unmasked_alarm {
            // We log an error event here primarily because the
            // current tracing span includes the program counter
            // value.
            event!(Level::ERROR, "panicing with alarm {}", alarm_instance);
            panic!(
                "unmasked alarm and panic_on_unmasked_alarm={}: {}",
                self.panic_on_unmasked_alarm, alarm_instance
            );
        }
    }

    pub fn clear_all_alarms(&mut self) {
        event!(Level::INFO, "clearing all alarms");
        self.active.clear()
    }

    pub fn unmasked_alarm_active(&self) -> bool {
        self.active.keys().any(|kind| match kind.maskable() {
            AlarmMaskability::Unmaskable => {
                assert!(!self.masked.contains(kind));
                true
            }
            AlarmMaskability::Maskable => !self.masked.contains(kind),
        })
    }

    fn set_active(&mut self, alarm_instance: Alarm) -> Result<(), Alarm> {
        let kind: AlarmKind = alarm_instance.kind();
        self.changes.add(kind);
        if self.is_masked(&alarm_instance) {
            self.active.insert(kind, alarm_instance);
            Ok(())
        } else {
            self.active.insert(kind, alarm_instance.clone());
            self.maybe_panic(&alarm_instance);
            Err(alarm_instance)
        }
    }
}

impl Alarmer for AlarmUnit {
    fn fire_if_not_masked<F: DiagnosticFetcher>(
        &mut self,
        alarm_instance: Alarm,
        _get_diags: F,
    ) -> Result<(), Alarm> {
        self.changes.add(alarm_instance.kind());
        self.set_active(alarm_instance)
    }

    fn always_fire<F: DiagnosticFetcher>(
        &mut self,
        alarm_instance: Alarm,
        get_diagnostics: F,
    ) -> Alarm {
        let kind = alarm_instance.kind();
        self.changes.add(kind);
        let sequence = alarm_instance.sequence;
        match self.set_active(alarm_instance) {
            Err(a) => a,
            Ok(()) => {
                let bug = Alarm {
                    sequence,
                    details: AlarmDetails::BUGAL {
                        activity: BugActivity::AlarmHandling,
                        diagnostics: get_diagnostics.diagnostics(),
                        message: format!(
                            "alarm {kind} is masked, but the caller assumed it could not be"
                        ),
                    },
                };
                match self.set_active(bug) {
                    Err(a) => a,
                    Ok(()) => unreachable!("Alarm BUGAL was unexpectedly masked"),
                }
            }
        }
    }
}

#[test]
fn unmaskable_alarms_are_not_maskable() {
    use base::prelude::{Address, Instruction};

    let mut alarm_unit = AlarmUnit::new_with_panic(false);
    assert!(!alarm_unit.unmasked_alarm_active());
    let diagnostics = CurrentInstructionDiagnostics {
        current_instruction: Instruction::invalid(),
        instruction_address: Address::ZERO,
    };
    // Any attempt to mask an unmaskable alarm should itself result in an error.
    assert!(
        alarm_unit
            .mask(AlarmKind::ROUNDTUITAL, &diagnostics)
            .is_err()
    );
    // Now we raise some non-maskable alarm.
    assert!(matches!(
        alarm_unit.fire_if_not_masked(
            Alarm {
                sequence: Some(Unsigned6Bit::ZERO),
                details: AlarmDetails::ROUNDTUITAL {
                    explanation: "The ROUNDTUITAL alarm is not maskable!".to_string(),
                    bug_report_url: "https://github.com/TX-2/TX-2-simulator/issues/144",
                },
            },
            &diagnostics
        ),
        Err(Alarm {
            sequence: Some(_),
            details: AlarmDetails::ROUNDTUITAL { .. },
        })
    ));
    // Verify that the alarm manager considers that an unmasked (in
    // this case because unmaskable) alarm is active.
    assert!(alarm_unit.unmasked_alarm_active());
}

#[test]
fn maskable_alarms_are_not_masked_by_default() {
    use base::prelude::{Address, Instruction};

    let mut alarm_unit = AlarmUnit::new_with_panic(false);
    assert!(!alarm_unit.unmasked_alarm_active());
    let diagnostics = CurrentInstructionDiagnostics {
        current_instruction: Instruction::invalid(),
        instruction_address: Address::ZERO,
    };
    // Now we raise some maskable, but not masked, alarm.
    let the_alarm = Alarm {
        sequence: Some(Unsigned6Bit::ZERO),
        details: AlarmDetails::PSAL(22, "some PPSAL alarm".to_string()),
    };
    // raise the alarm, verify that it really fires.
    assert!(matches!(
        alarm_unit.fire_if_not_masked(the_alarm, &diagnostics),
        Err(Alarm {
            sequence: _,
            details: AlarmDetails::PSAL(22, _),
        },)
    ));
    // Verify that the alarm manager considers that an unmasked (in
    // this case because maskable but not actually masked) alarm is active.
    assert!(alarm_unit.unmasked_alarm_active());
}

// Alarm conditions we expect to use in the emulator but
// which are not in use yet:
// SYAL1,                       // Sync alarm 1 (see User Handbook page 5-21)
// SYAL2,                       // Sync alarm 2 (see User Handbook page 5-21)

// Alarm enumerators we don't expect to use:
//
// MPAL,                     // data parity error (in STUV)
// NPAL,                     // instruction parity error (in STUV)
// XPAL,                     // parity error in X-memory
// FPAL,                     // parity error in F-memory
// TSAL,                     // voltage issue; can't happen in an emulator.
// USAL,                     // voltage issue; can't happen in an emulator.
// Mouse-trap
