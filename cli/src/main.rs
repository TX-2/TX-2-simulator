/// Simulate the historic TX-2 computer
use std::ffi::OsString;
use std::fs::File;
use std::fs::OpenOptions;
use std::str::FromStr;
use std::time::Duration;

use clap::{ArgEnum, Parser};
use tracing::{event, Level};
use tracing_subscriber::filter::{EnvFilter, LevelFilter};
use tracing_subscriber::prelude::*;

use base::prelude::*;
use cpu::{
    self, set_up_peripherals, Alarm, BasicClock, Clock, ControlUnit, DeviceManager,
    MemoryConfiguration, MemoryUnit, MinimalSleeper, ResetMode, RunMode, TapeIterator,
};

// Thanks to Google for allowing this code to be open-sourced.  I
// generally prefer to correspond about this project using my
// personal email address rather than my work one, though.
const AUTHOR: &str = "James Youngman <james@youngman.org>";

fn run(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    devices: &mut DeviceManager,
    clk: &mut BasicClock,
    multiplier: Option<f64>,
) -> i32 {
    control.codabo(&ResetMode::ResetTSP, devices, mem);
    let (alarm, maybe_address) = run_until_alarm(control, devices, mem, clk, multiplier);
    match maybe_address {
        Some(addr) => {
            event!(
                Level::ERROR,
                "Execution stopped at address  {:o}: {}",
                addr,
                alarm
            );
        }
        None => {
            event!(Level::ERROR, "Execution stopped: {}", alarm);
        }
    }
    1
}

fn run_until_alarm(
    control: &mut ControlUnit,
    devices: &mut DeviceManager,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
    multiplier: Option<f64>,
) -> (Alarm, Option<Address>) {
    let mut sleeper = MinimalSleeper::new(Duration::from_millis(2));
    let mut next_hw_poll = clk.now();
    let mut run_mode = RunMode::Running;

    loop {
        let now = clk.now();
        if now >= next_hw_poll {
            // check for I/O alarms, flag changes.
            event!(
                Level::TRACE,
                "polling hardware for updates (now={:?})",
                &now
            );
            match control.poll_hardware(devices, run_mode, &now) {
                Ok((mode, Some(next))) => {
                    run_mode = mode;
                    next_hw_poll = next;
                }
                Ok((mode, None)) => {
                    run_mode = mode;
                    next_hw_poll = now + Duration::from_micros(5);
                }
                Err(alarm) => {
                    event!(
                        Level::INFO,
                        "Alarm raised during hardware polling at system time {:?}",
                        now
                    );
                    return (alarm, None);
                }
            }
        } else {
            event!(
                Level::TRACE,
                "not polling hardware for updates (remaining wait: {:?})",
                next_hw_poll - now,
            );
        }
        if run_mode == RunMode::InLimbo {
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
            cpu::time_passes(clk, &mut sleeper, &interval, multiplier);
            continue;
        }
        let mut hardware_state_changed = false;
        match control.execute_instruction(&clk.now(), devices, mem, &mut hardware_state_changed) {
            Err((alarm, address)) => {
                event!(
                    Level::INFO,
                    "Alarm raised during instruction execution at {:o} at system time {:?}",
                    address,
                    now
                );
                return (alarm, Some(address));
            }
            Ok((ns, new_run_mode)) => {
                run_mode = new_run_mode;
                cpu::time_passes(clk, &mut sleeper, &Duration::from_nanos(ns), multiplier);
            }
        }
        if hardware_state_changed {
            // Some instruction changed the hardware, so we need to
            // poll it again.
            next_hw_poll = now;
        }
    }
}

#[derive(Debug)]
struct TapeSequence {
    pos: usize,
    names: Vec<OsString>,
}

impl TapeSequence {
    fn new(names: Vec<OsString>) -> TapeSequence {
        TapeSequence { pos: 0, names }
    }

    fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

impl TapeIterator for TapeSequence {
    fn next_tape(&mut self) -> Option<File> {
        match self.names.get(self.pos) {
            Some(name) => {
                self.pos += 1;
                OpenOptions::new().read(true).open(name).ok()
            }
            None => None,
        }
    }
}

/// Whether to panic when there was an unmasked alarm.
#[derive(Debug, Clone, PartialEq, Eq, ArgEnum)]
enum PanicOnUnmaskedAlarm {
    // Panic when an unmasked alarm occurs.  If the RUST_BACKTRACE
    // environment variable is also set, a stack backtrace will be
    // printed.
    No,
    /// Do not panic when an unmasked alarm occurs.  The emulator will
    /// stop, but no panic will happen.
    Yes,
}

impl FromStr for PanicOnUnmaskedAlarm {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "true" | "yes" => Ok(PanicOnUnmaskedAlarm::Yes),
            "false" | "no" => Ok(PanicOnUnmaskedAlarm::No),
            _ => Err(format!(
                "unexpected value '{}': expected 'true', 'false', 'yes' or 'no'",
                s
            )),
        }
    }
}

/// Command-line simulator for the historical TX-2 computer
#[derive(Parser, Debug)]
#[clap(author = AUTHOR, version, about, long_about = None)]
struct Cli {
    /// Run this many times faster than real-time ('MAX' for as-fast-as-possible)
    #[clap(long = "speed-multiplier")]
    speed_multiplier: Option<String>,

    /// When set, panic if an alarm occurs (so that a stack backtrace
    /// is produced when the RUST_BACKTRACE environment variable is
    /// also set).  When unset, stop the emulator without panic.
    #[clap(long = "panic-on-unmasked-alarm", arg_enum)]
    panic_on_unmasked_alarm: Option<PanicOnUnmaskedAlarm>,

    /// Files containing paper tape data
    tape: Vec<OsString>,
}

fn run_simulator() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    // By default, display info messages.
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    // See https://docs.rs/tracing-subscriber/0.3.11/tracing_subscriber/filter/struct.EnvFilter.html#examples
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(env_filter)
        .init();

    let mem_config = MemoryConfiguration {
        with_u_memory: false,
    };

    let tapes = TapeSequence::new(cli.tape.clone());
    if tapes.is_empty() {
        event!(
            Level::WARN,
            "No paper tapes were specified on the command line, so no program will be loaded"
        );
    }
    let speed_multiplier: Option<f64> = match cli.speed_multiplier.as_ref() {
        None => {
            event!(
                Level::WARN,
                "No --speed-multiplier option specified, running at maximum speed"
            );
            None
        }
        Some(value) => match value.as_str() {
            "MAX" => {
                event!(
                    Level::INFO,
                    "--speed-multiplier=MAX, running at maximum speed"
                );
                None
            }
            some_number => match some_number.parse::<f64>() {
                Ok(x) => {
                    event!(
                        Level::INFO,
                        "--speed-multiplier={}, running at speed multiplier {}",
                        some_number,
                        x
                    );
                    Some(x)
                }
                Err(e) => {
                    return Err(Box::new(e));
                }
            },
        },
    };

    let mut control = ControlUnit::new(
        // We have two simimarly-named enums here so that the cpu
        // crate does not have to depend on clap.
        match cli.panic_on_unmasked_alarm {
            Some(PanicOnUnmaskedAlarm::Yes) => cpu::PanicOnUnmaskedAlarm::Yes,
            Some(PanicOnUnmaskedAlarm::No) | None => cpu::PanicOnUnmaskedAlarm::No,
        },
    );
    event!(
        Level::DEBUG,
        "Initial control unit state iis {:?}",
        &control
    );

    let mut clk: BasicClock = BasicClock::new();

    let mut mem = MemoryUnit::new(&mem_config);
    let mut devices = DeviceManager::new();
    set_up_peripherals(&mut devices, &clk, Box::new(tapes));

    std::process::exit(run(
        &mut control,
        &mut mem,
        &mut devices,
        &mut clk,
        speed_multiplier,
    ));
}

fn main() {
    match run_simulator() {
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
