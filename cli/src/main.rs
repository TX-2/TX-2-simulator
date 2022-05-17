/// Simulate the historic TX-2 computer
mod lw;
mod sleep;

use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::OpenOptions;
use std::io::{BufReader, Read};
use std::str::FromStr;
use std::time::Duration;

use clap::{ArgEnum, Parser};
use tracing::{event, Level};
use tracing_subscriber::filter::{EnvFilter, LevelFilter};
use tracing_subscriber::prelude::*;

use base::prelude::*;
use cpu::{
    self, set_up_peripherals, Alarm, BasicClock, Clock, ControlUnit, DeviceManager,
    MemoryConfiguration, MemoryUnit, OutputEvent, ResetMode, RunMode,
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
    sleep_multiplier: Option<f64>,
) -> i32 {
    control.codabo(&ResetMode::ResetTSP, &clk.now(), devices, mem);
    let (alarm, maybe_address, system_time) =
        run_until_alarm(control, devices, mem, clk, sleep_multiplier);
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
    control.disconnect_all_devices(devices, &system_time);
    1
}

fn run_until_alarm(
    control: &mut ControlUnit,
    devices: &mut DeviceManager,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
    sleep_multiplier: Option<f64>,
) -> (Alarm, Option<Address>, Duration) {
    let mut sleeper = sleep::MinimalSleeper::new(Duration::from_millis(2));
    let mut next_hw_poll = clk.now();
    let mut run_mode = RunMode::Running;
    let mut lw66 = lw::LincolnStreamWriter::new();

    let result = loop {
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
                    return (alarm, None, now);
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
            sleep::time_passes(clk, &mut sleeper, &interval, sleep_multiplier);
            continue;
        }
        let mut hardware_state_changed = false;
        let now = clk.now();
        let maybe_output =
            match control.execute_instruction(&now, devices, mem, &mut hardware_state_changed) {
                Err((alarm, address)) => {
                    event!(
                        Level::INFO,
                        "Alarm raised during instruction execution at {:o} at system time {:?}",
                        address,
                        now
                    );
                    return (alarm, Some(address), now);
                }
                Ok((ns, new_run_mode, maybe_output)) => {
                    run_mode = new_run_mode;
                    sleep::time_passes(
                        clk,
                        &mut sleeper,
                        &Duration::from_nanos(ns),
                        sleep_multiplier,
                    );
                    maybe_output
                }
            };
        if hardware_state_changed {
            // Some instruction changed the hardware, so we need to
            // poll it again.
            next_hw_poll = now;
        }
        match maybe_output {
            None => (),
            Some(OutputEvent::LincolnWriterPrint { unit, ch }) => {
                if unit == u6!(0o66) {
                    if let Err(e) = lw66.write(ch) {
                        event!(Level::ERROR, "output error: {}", e);
                        // TODO: change state of the output unit to
                        // indicate that there has been a failure,
                        // instead of just terminating the simulation.
                        break (Alarm::MISAL { unit }, None, now);
                    }
                } else {
                    event!(
                        Level::WARN,
                        "discarding Lincoln Writer output for unit {:o}",
                        unit,
                    );
                }
            }
        }
    };
    lw66.disconnect();
    result
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

    /// File containing paper tape data
    tape: Option<OsString>,
}

#[derive(Debug)]
struct BadSpeedMultiplier(f64);

impl Display for BadSpeedMultiplier {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "speed multiplier {} is too small for reliable arithmetic operations",
            self.0
        )
    }
}

impl std::error::Error for BadSpeedMultiplier {}

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

    fn file_size_guess(file_name: &OsStr) -> Option<usize> {
        match std::fs::metadata(file_name) {
            Ok(metadata) => match usize::try_from(metadata.len()) {
                Ok(n) => Some(n),
                Err(_) => None,
            },
            Err(_) => None,
        }
    }

    let tape_data: Option<Vec<u8>> = match cli.tape.as_ref() {
        None => {
            event!(
                Level::WARN,
                "No paper tapes were specified on the command line, so no program will be loaded"
            );
            None
        }
        Some(file_name) => {
            match OpenOptions::new()
                .read(true)
                .open(file_name)
                .map(BufReader::new)
            {
                Ok(mut r) => {
                    let mut buf: Vec<u8> =
                        Vec::with_capacity(file_size_guess(file_name).unwrap_or(0));
                    if let Err(e) = r.read_to_end(&mut buf) {
                        return Err(Box::new(e));
                    } else {
                        Some(buf)
                    }
                }
                Err(e) => {
                    return Err(Box::new(e));
                }
            }
        }
    };

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
    let sleep_multiplier = match speed_multiplier {
        None => None,
        Some(sp) => {
            let sleep_multiplier = sp.recip();
            if sleep_multiplier.is_finite() {
                Some(sleep_multiplier)
            } else {
                return Err(Box::new(BadSpeedMultiplier(sp)));
            }
        }
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
    set_up_peripherals(&mut devices, &clk, tape_data);

    std::process::exit(run(
        &mut control,
        &mut mem,
        &mut devices,
        &mut clk,
        sleep_multiplier,
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
