use std::cmp::min;
use std::time::Duration;

use tracing::{event, span, Level};

use base::prelude::*;

use crate::alarm::UnmaskedAlarm;
use crate::context::Context;
use crate::control::{ControlUnit, ResetMode, RunMode};
use crate::event::{InputEvent, OutputEvent};
use crate::io::{set_up_peripherals, DeviceManager};
use crate::memory::{MemoryConfiguration, MemoryUnit};
use crate::PanicOnUnmaskedAlarm;
use crate::PETR;

pub struct Tx2 {
    control: ControlUnit,
    mem: MemoryUnit,
    devices: DeviceManager,
    pub next_execution_due: Option<Duration>,
    pub next_hw_poll_due: Duration,
    pub run_mode: RunMode,
}

impl Tx2 {
    pub fn new(
        ctx: &Context,
        panic_on_unmasked_alarm: PanicOnUnmaskedAlarm,
        mem_config: &MemoryConfiguration,
    ) -> Tx2 {
        let control = ControlUnit::new(panic_on_unmasked_alarm);
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

    fn set_next_execution_due(&mut self, now: Duration, newval: Option<Duration>) {
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

    pub fn codabo(&mut self, ctx: &Context, reset_mode: &ResetMode) {
        self.control
            .codabo(ctx, reset_mode, &mut self.devices, &mut self.mem);
    }

    pub fn mount_tape(&mut self, ctx: &Context, data: Vec<u8>) {
        self.devices
            .on_input_event(ctx, PETR, InputEvent::PetrMountPaperTape { data });
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

    fn poll_hw(&mut self, ctx: &Context) -> Result<(), UnmaskedAlarm> {
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
                Err(UnmaskedAlarm {
                    alarm,
                    address: None,
                    when: *now,
                })
            }
        }
    }

    fn execute_one_instruction(
        &mut self,
        ctx: &Context,
    ) -> Result<(u64, Option<OutputEvent>), UnmaskedAlarm> {
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
                Err(UnmaskedAlarm {
                    alarm,
                    address: Some(address),
                    when: ctx.simulated_time,
                })
            }
            Ok((ns, new_run_mode, maybe_output)) => {
                let now = &ctx.simulated_time;
                match (self.run_mode, new_run_mode) {
                    (RunMode::Running, RunMode::InLimbo) => {
                        event!(Level::DEBUG, "Entering LIMBO");
                        self.next_execution_due = None;
                    }
                    (RunMode::InLimbo, RunMode::Running) => {
                        event!(Level::DEBUG, "Leaving LIMBO");
                        self.next_execution_due = Some(*now + Duration::from_nanos(1));
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
        if ctx.simulated_time >= self.next_hw_poll_due {
            let prev_poll_due = self.next_hw_poll_due;
            match self.poll_hw(ctx) {
                Ok(()) => {
                    if self.next_hw_poll_due == prev_poll_due {
                        event!(Level::WARN, "polled hardware successfully at system time {:?}, but poll_hw returned with next_hw_poll_due={:?}",
			       system_time, self.next_hw_poll_due);
                    }
                }
                Err(unmasked_alarm) => {
                    return Err(unmasked_alarm);
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

    pub fn disconnect_all_devices(&mut self, ctx: &Context) {
        self.devices.disconnect_all(ctx);
    }
}