use std::cmp::min;
use std::collections::BTreeMap;
use std::time::Duration;

use tracing::{event, span, Level};

use wasm_bindgen::prelude::*;

use base::prelude::*;

use super::alarm::{Alarm, AlarmKind, Alarmer, UnmaskedAlarm};
use super::alarmunit::AlarmStatus;
use super::context::Context;
use super::control::{ConfigurationMemorySetup, ControlUnit, ResetMode, RunMode};
use super::event::{InputEvent, OutputEvent};
use super::io::{set_up_peripherals, DeviceManager, ExtendedUnitState, InputFlagRaised};
use super::memory::{MemoryConfiguration, MemoryUnit};
use super::PETR;
use super::{InputEventError, PanicOnUnmaskedAlarm};

#[wasm_bindgen]
pub struct Tx2 {
    control: ControlUnit,
    mem: MemoryUnit,
    devices: DeviceManager,
    next_execution_due: Option<Duration>,
    next_hw_poll_due: Duration,
    run_mode: RunMode,
}

impl Tx2 {
    pub fn new(
        ctx: &Context,
        panic_on_unmasked_alarm: PanicOnUnmaskedAlarm,
        mem_config: &MemoryConfiguration,
    ) -> Tx2 {
        let control = ControlUnit::new(
            panic_on_unmasked_alarm,
            ConfigurationMemorySetup::Uninitialised,
        );
        event!(
            Level::DEBUG,
            "Initial control unit state iis {:?}",
            &control
        );

        let mem = MemoryUnit::new(ctx, mem_config);
        let mut devices = DeviceManager::new();
        set_up_peripherals(ctx, &mut devices);
        Tx2 {
            control,
            mem,
            devices,
            next_execution_due: None,
            next_hw_poll_due: ctx.simulated_time,
            run_mode: RunMode::InLimbo,
        }
    }

    pub fn get_status_of_alarm(&self, name: &str) -> Option<AlarmStatus> {
        self.control.get_status_of_alarm(name)
    }

    pub fn get_alarm_statuses(&self) -> Vec<AlarmStatus> {
        self.control.get_alarm_statuses()
    }

    pub fn set_alarm_masked(&mut self, kind: AlarmKind, masked: bool) -> Result<(), Alarm> {
        self.control.set_alarm_masked(kind, masked)
    }

    pub fn set_run_mode(&mut self, run_mode: RunMode) {
        self.run_mode = run_mode;
    }

    pub fn set_next_execution_due(&mut self, now: Duration, newval: Option<Duration>) {
        if let Some(t) = newval {
            assert!(now <= t);
        }
        event!(
            Level::TRACE,
            "Changing next_execution_due from {:?} to {:?}",
            self.next_execution_due,
            newval,
        );
        self.next_execution_due = newval;
    }

    fn set_next_hw_poll_due(&mut self, now: Duration, newval: Duration) {
        assert!(now <= newval);
        event!(
            Level::TRACE,
            "Changing next_hw_poll_due from {:?} to {:?}",
            self.next_hw_poll_due,
            newval,
        );
        self.next_hw_poll_due = newval;
    }

    pub fn codabo(&mut self, ctx: &Context, reset_mode: &ResetMode) -> Result<(), Alarm> {
        self.control
            .codabo(ctx, reset_mode, &mut self.devices, &mut self.mem)
    }

    fn on_input_event(
        &mut self,
        ctx: &Context,
        unit: Unsigned6Bit,
        event: InputEvent,
    ) -> Result<InputFlagRaised, InputEventError> {
        match self.devices.on_input_event(ctx, unit, event) {
            Ok(InputFlagRaised::Yes) => {
                // update the poll time for this unit to force it to
                // be polled
                self.devices.update_poll_time(ctx, unit);
                Ok(InputFlagRaised::Yes)
            }
            Ok(InputFlagRaised::No) => Ok(InputFlagRaised::No),
            Err(e) => Err(e),
        }
    }

    pub fn mount_tape(
        &mut self,
        ctx: &Context,
        data: Vec<u8>,
    ) -> Result<InputFlagRaised, InputEventError> {
        self.on_input_event(ctx, PETR, InputEvent::PetrMountPaperTape { data })
    }

    pub fn lw_input(
        &mut self,
        ctx: &Context,
        unit: Unsigned6Bit,
        codes: &[Unsigned6Bit],
    ) -> Result<(bool, InputFlagRaised), String> {
        let event = InputEvent::LwKeyboardInput {
            data: codes.to_vec(),
        };
        match self.on_input_event(ctx, unit, event) {
            Ok(flag_raise) => Ok((true, flag_raise)),
            Err(InputEventError::BufferUnavailable) => Ok((false, InputFlagRaised::No)),
            Err(e) => Err(e.to_string()),
        }
    }

    pub fn next_tick(&self) -> Duration {
        match (
            self.run_mode,
            self.next_hw_poll_due,
            self.next_execution_due,
        ) {
            (RunMode::InLimbo, hw, _) | (RunMode::Running, hw, None) => hw,
            (RunMode::Running, hw, Some(insn)) => min(hw, insn),
        }
    }

    fn poll_hw(&mut self, ctx: &Context) -> Result<(), Alarm> {
        // check for I/O alarms, flag changes.
        let now = &ctx.simulated_time;
        event!(Level::TRACE, "polling hardware for updates (now={:?})", now);
        match self
            .control
            .poll_hardware(ctx, &mut self.devices, self.run_mode)
        {
            Ok((mode, next)) => {
                self.run_mode = mode;
                self.set_next_hw_poll_due(
                    *now,
                    match next {
                        Some(when) => when,
                        None => {
                            // TODO: check why poll() doesn't always
                            // return a next-poll time.
                            *now + Duration::from_micros(5)
                        }
                    },
                );
                Ok(())
            }
            Err(alarm) => {
                event!(
                    Level::INFO,
                    "Alarm raised during hardware polling at system time {:?}",
                    now
                );
                self.control.fire_if_not_masked(alarm)
            }
        }
    }

    fn execute_one_instruction(
        &mut self,
        ctx: &Context,
    ) -> Result<(u64, Option<OutputEvent>), UnmaskedAlarm> {
        let now = &ctx.simulated_time;
        if self.run_mode == RunMode::InLimbo {
            event!(
                Level::WARN,
                "execute_one_instruction was called while machine is in LIMBO"
            );
            self.set_next_execution_due(*now, None);
            return Ok((0, None));
        }

        let mut hardware_state_changed: Option<SequenceNumber> = None;
        match self.control.execute_instruction(
            ctx,
            &mut self.devices,
            &mut self.mem,
            &mut hardware_state_changed,
        ) {
            Err((alarm, address)) => {
                event!(
                    Level::INFO,
                    "Alarm raised during instruction execution at {:o} at system time {:?}",
                    address,
                    &ctx.simulated_time
                );
                self.set_next_execution_due(*now, None);
                assert!(self.unmasked_alarm_active());
                Err(UnmaskedAlarm {
                    alarm,
                    address: Some(address),
                    when: ctx.simulated_time,
                })
            }
            Ok((ns, new_run_mode, maybe_output)) => {
                match (self.run_mode, new_run_mode) {
                    (RunMode::Running, RunMode::InLimbo) => {
                        event!(Level::DEBUG, "Entering LIMBO");
                        self.set_next_execution_due(*now, None);
                    }
                    (RunMode::InLimbo, RunMode::Running) => {
                        event!(Level::DEBUG, "Leaving LIMBO");
                        self.set_next_execution_due(*now, Some(*now + Duration::from_nanos(1)));
                    }
                    (old, new) => {
                        assert_eq!(old, new);
                    }
                }
                self.run_mode = new_run_mode;

                if let Some(seq) = hardware_state_changed {
                    // Some instruction changed the hardware, so we need to
                    // poll it again.
                    event!(
                        Level::DEBUG,
                        "hardware state change for unit {seq:?}; bringing forward next hardware poll"
                    );
                    self.set_next_hw_poll_due(*now, *now + Duration::from_nanos(1));
                } else {
                    event!(
                        Level::TRACE,
                        "current instruction did not affect the hardware"
                    );
                }
                // TODO: eliminate ns, just change state of `self`.
                Ok((ns, maybe_output))
            }
        }
    }

    pub fn tick(&mut self, ctx: &Context) -> Result<Option<OutputEvent>, UnmaskedAlarm> {
        let system_time = ctx.simulated_time;
        let tick_span = span!(Level::INFO, "tick", t=?system_time);
        let _enter = tick_span.enter();
        event!(
            Level::TRACE,
            "tick: system_time={:?}, next_execution_due={:?}, next_hw_poll_due={:?}",
            system_time,
            self.next_execution_due,
            self.next_hw_poll_due
        );
        let due: Duration = if let Some(inst_due) = self.next_execution_due {
            min(self.next_hw_poll_due, inst_due)
        } else {
            self.next_hw_poll_due
        };
        if due > system_time {
            let premature_by = due - system_time;
            event!(
                Level::WARN,
                "tick() was called {premature_by:?} prematurely"
            );
        }

        if ctx.simulated_time >= self.next_hw_poll_due {
            let prev_poll_due = self.next_hw_poll_due;
            match self.poll_hw(ctx) {
                Ok(()) => {
                    if self.next_hw_poll_due == prev_poll_due {
                        event!(Level::WARN, "polled hardware successfully at system time {:?}, but poll_hw returned with next_hw_poll_due={:?}",
                               system_time, self.next_hw_poll_due);
                    }
                }
                Err(alarm) => {
                    return Err(UnmaskedAlarm {
                        alarm,
                        address: None, // not executing an instruction
                        when: ctx.simulated_time,
                    });
                }
            }
        } else {
            event!(
                Level::TRACE,
                "not polling hardware for updates (remaining wait: {:?})",
                self.next_hw_poll_due - system_time,
            );
        }

        if self.run_mode == RunMode::InLimbo {
            // No sequence is active, so there is no CPU instruction
            // to execute.  Therefore we can only leave the limbo
            // state in response to a hardware event.  We already know
            // that we need to check for that at `next_hw_poll`.
            let interval: Duration = self.next_hw_poll_due - system_time;
            event!(
                Level::TRACE,
                "machine is in limbo, waiting {:?} for a flag to be raised",
                &interval,
            );
            // There can be no output event, because no instruction
            // was executed to generate it.
            Ok(None)
        } else if self.unmasked_alarm_active() {
            event!(
                Level::DEBUG,
                "will not execute the next instruction because there is an an unmasked alarm."
            );
            Ok(None) // no output event (as we executed no instruction)
        } else {
            // Not in limbo, it may be time to execute an instruction.
            match self.next_execution_due {
                Some(next) if next <= system_time => {
                    let (ns, maybe_output) = self.execute_one_instruction(ctx)?;
                    let mut due = next + Duration::from_nanos(ns);
                    if due <= system_time {
                        due = system_time + Duration::from_nanos(1);
                    }
                    self.set_next_execution_due(system_time, Some(due));
                    Ok(maybe_output)
                }
                None => {
                    event!(
                        Level::TRACE,
                        "instruction execution clock is not running, no instruction to execute"
                    );
                    Ok(None)
                }
                Some(next) => {
                    let wait_for = next - system_time;
                    event!(
                        Level::TRACE,
                        "next instruction execution not due for {wait_for:?}"
                    );
                    Ok(None)
                }
            }
        }
    }

    pub fn unmasked_alarm_active(&self) -> bool {
        self.control.unmasked_alarm_active()
    }

    pub fn drain_alarm_changes(&mut self) -> BTreeMap<AlarmKind, AlarmStatus> {
        self.control.drain_alarm_changes()
    }

    pub fn disconnect_all_devices(&mut self, ctx: &Context) -> Result<(), Alarm> {
        self.devices.disconnect_all(ctx, &mut self.control)
    }

    fn extended_state_of_software_sequence(&self, seq: Unsigned6Bit) -> ExtendedUnitState {
        ExtendedUnitState {
            flag: self.control.current_flag_state(&seq),
            connected: false,
            in_maintenance: false,
            name: format!("Sequence {seq:>02o}"),
            status: None,
            text_info: "(software only)".to_string(),
        }
    }

    fn software_sequence_statuses(&self) -> BTreeMap<Unsigned6Bit, ExtendedUnitState> {
        [u6!(0), u6!(0o76), u6!(0o77)]
            .into_iter()
            .map(|seq| (seq, self.extended_state_of_software_sequence(seq)))
            .collect()
    }

    pub fn sequence_statuses(
        &mut self,
        ctx: &Context,
    ) -> Result<BTreeMap<Unsigned6Bit, ExtendedUnitState>, Alarm> {
        // Get the status of the hardware units
        let mut result: BTreeMap<Unsigned6Bit, ExtendedUnitState> =
            self.devices.device_statuses(ctx, &mut self.control)?;
        // Merge in the status of the software units
        result.append(&mut self.software_sequence_statuses());
        Ok(result)
    }

    pub fn drain_device_changes(
        &mut self,
        ctx: &Context,
    ) -> Result<BTreeMap<Unsigned6Bit, ExtendedUnitState>, Alarm> {
        let mut mapping = self.devices.drain_changes(ctx, &mut self.control)?;
        for seq in self.control.drain_flag_changes().into_iter() {
            mapping
                .entry(seq)
                .or_insert_with(|| self.extended_state_of_software_sequence(seq));
        }
        Ok(mapping)
    }
}
