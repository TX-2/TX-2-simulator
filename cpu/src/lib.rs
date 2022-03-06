//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name = "cpu"]

use std::time::Duration;

use tracing::{event, Level};

mod alarm;
mod clock;
mod control;
mod exchanger;
pub mod io;
mod memory;

pub use alarm::Alarm;
pub use clock::{BasicClock, Clock, MinimalSleeper};
pub use control::{ControlUnit, ResetMode};
pub use memory::{MemoryConfiguration, MemoryUnit};

fn time_passes(
    clk: &mut BasicClock,
    sleeper: &mut MinimalSleeper,
    t: &Duration,
    multiplier: Option<f64>,
) {
    clk.consume(t);
    if let Some(m) = multiplier {
        sleeper.sleep(&t.mul_f64(m));
    }
}

pub fn run_until_alarm(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
    multiplier: Option<f64>,
) -> Result<(), Alarm> {
    let mut elapsed_ns: u64 = 0;
    let mut sleeper = MinimalSleeper::new(Duration::from_millis(2));
    let mut next_hw_poll = clk.now();

    loop {
        let now = clk.now();
        if now >= next_hw_poll {
            // check for I/O alarms, flag changes.
            event!(Level::TRACE, "polling hardware for updates");
            match control.poll_hardware(&now) {
                Ok(Some(next)) => {
                    next_hw_poll = next;
                }
                Ok(None) => {
                    next_hw_poll = now + Duration::from_micros(5);
                }
                Err(e) => {
                    event!(
                        Level::INFO,
                        "Alarm raised during hardware polling after {}ns",
                        elapsed_ns
                    );
                    return Err(e);
                }
            }
        }
        let in_limbo = match control.fetch_instruction(mem) {
            Err(e) => {
                event!(
                    Level::INFO,
                    "Alarm raised during instruction fetch after {}ns",
                    elapsed_ns
                );
                return Err(e);
            }
            Ok(some_sequence_is_runnable) => !some_sequence_is_runnable,
        };
        if in_limbo {
            // No sequence is active, so there is no CPU instruction
            // to execute.  Therefore we can only leave the limbo
            // state in response to a hardware event.  We already know
            // that we need to check for that at `next_hw_poll`.
            let interval: Duration = next_hw_poll - now;
            event!(
                Level::TRACE,
                "machine is in limbo, waiting {:?} for a flag to be raised",
                &interval,
            );
            time_passes(clk, &mut sleeper, &interval, multiplier);
            continue;
        }
        elapsed_ns += match control.execute_instruction(&clk.now(), mem) {
            Err(e) => {
                event!(
                    Level::INFO,
                    "Alarm raised during instruction execution after {}ns",
                    elapsed_ns
                );
                return Err(e);
            }
            Ok(ns) => {
                time_passes(clk, &mut sleeper, &Duration::from_nanos(ns), multiplier);
                ns
            }
        };
    }
}
