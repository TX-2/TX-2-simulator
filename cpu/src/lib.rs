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
    clk.consume(&t);
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
    let limbo_tick = Duration::from_micros(5);

    loop {
        // Consider having poll_hardware return a (simulated) duration
        // after which there should be a succeeding call.
        control.poll_hardware(&clk.now())?; // check for I/O alarms, flag changes.
        if !control.fetch_instruction(mem)? {
            event!(
                Level::TRACE,
                "machine is in limbo, waiting {:?} for a flag to be raised",
                &limbo_tick,
            );
            time_passes(clk, &mut sleeper, &limbo_tick, multiplier);
            continue;
        }
        elapsed_ns += match control.execute_instruction(&clk.now(), mem) {
            Err(e) => {
                event!(Level::INFO, "Alarm raised after {}ns", elapsed_ns);
                return Err(e);
            }
            Ok(ns) => {
                time_passes(clk, &mut sleeper, &Duration::from_nanos(ns), multiplier);
                ns
            }
        };
    }
}
