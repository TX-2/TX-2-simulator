/// Simulate the historic TX-2 computer
mod clock;
mod lw;
mod sleep;

use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::OpenOptions;
use std::io::{BufReader, Read};
use std::str::FromStr;
use std::time::Duration;

use clap::{ArgAction::Set, Parser, ValueEnum};
use tracing::{Level, event};
use tracing_subscriber::filter::{EnvFilter, LevelFilter};
use tracing_subscriber::prelude::*;

use base::prelude::*;
use clock::{BasicClock, Clock};
use cpu::{
    self, Alarm, AlarmDetails, MemoryConfiguration, OutputEvent, ResetMode, RunMode, Tx2,
    UnmaskedAlarm,
};

// Thanks to Google for allowing this code to be open-sourced.  I
// generally prefer to correspond about this project using my
// personal email address rather than my work one, though.
const AUTHOR: &str = "James Youngman <james@youngman.org>";

fn run(
    tx2: &mut Tx2,
    clk: &mut BasicClock,
    sleep_multiplier: Option<f64>,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Err(e) = tx2.codabo(&clk.make_fresh_context(), &ResetMode::ResetTSP) {
        event!(Level::ERROR, "CODABO failed: {}", e);
        return Err(Box::new(e));
    }

    // TODO: setting next_execution_due is basically the 'start'
    // operaiton of the TX-2's sync system.  We should model that
    // directly as the user may want to use the UI to operate the sync
    // system as was possible in the real hardware.
    {
        let now = clk.now();
        tx2.set_next_execution_due(now, Some(now));
    }
    tx2.set_run_mode(RunMode::Running);

    match run_until_alarm(tx2, clk, sleep_multiplier) {
        UnmaskedAlarm {
            alarm,
            address: Some(addr),
            when: _,
        } => {
            event!(
                Level::ERROR,
                "Execution stopped at address  {:o}: {}",
                addr,
                alarm
            );
        }
        UnmaskedAlarm {
            alarm,
            address: None,
            when: _,
        } => {
            event!(Level::ERROR, "Execution stopped: {}", alarm);
        }
    };
    if let Err(e) = tx2.disconnect_all_devices(&clk.make_fresh_context()) {
        event!(Level::ERROR, "Failed in device shutdown: {}", e);
        return Err(Box::new(e));
    }
    Ok(())
}

fn run_until_alarm(
    tx2: &mut Tx2,
    clk: &mut BasicClock,
    sleep_multiplier: Option<f64>,
) -> UnmaskedAlarm {
    let mut sleeper = sleep::MinimalSleeper::new(Duration::from_millis(2));
    let mut lw66 = lw::LincolnStreamWriter::new();

    let result: UnmaskedAlarm = loop {
        {
            let now = clk.now();
            let next = tx2.next_tick();
            if now < next {
                let interval = next - now;
                sleep::time_passes(clk, &mut sleeper, &interval, sleep_multiplier);
            }
            clk.advance_to_simulated_time(next);
        }
        let tick_context = clk.make_fresh_context();
        match tx2.tick(&tick_context) {
            Ok(maybe_output) => {
                match maybe_output {
                    None => (),
                    Some(OutputEvent::LincolnWriterPrint { unit, ch }) => {
                        if unit == u6!(0o66) {
                            if let Err(e) = lw66.write(ch) {
                                event!(Level::ERROR, "output error: {}", e);
                                // TODO: change state of the output unit to
                                // indicate that there has been a failure,
                                // instead of just terminating the simulation.
                                break UnmaskedAlarm {
                                    alarm: Alarm {
                                        sequence: None,
                                        details: AlarmDetails::MISAL {
                                            affected_unit: u6!(0o66),
                                        },
                                    },
                                    address: None,
                                    when: tick_context.simulated_time,
                                };
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
            }
            Err(unmasked_alarm) => {
                break unmasked_alarm;
            }
        }
        let next_tick = tx2.next_tick();
        if next_tick <= tick_context.simulated_time {
            event!(
                Level::WARN,
                "Tx2::tick is not advancing the system clock (next tick {:?} <= current tick {:?})",
                next_tick,
                tick_context.simulated_time,
            );
        }
    };
    lw66.disconnect();
    result
}

/// Whether to panic when there was an unmasked alarm.
#[derive(Debug, Clone, PartialEq, Eq, ValueEnum)]
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
                "unexpected value '{s}': expected 'true', 'false', 'yes' or 'no'",
            )),
        }
    }
}

/// Command-line simulator for the historical TX-2 computer
#[derive(Parser, Debug)]
#[command(author = AUTHOR, version, about, long_about = None)]
struct Cli {
    /// Run this many times faster than real-time ('MAX' for as-fast-as-possible)
    #[arg(action = Set, long = "speed-multiplier")]
    speed_multiplier: Option<String>,

    /// When set, panic if an alarm occurs (so that a stack backtrace
    /// is produced when the RUST_BACKTRACE environment variable is
    /// also set).  When unset, stop the emulator without panic.
    #[arg(action = Set, long = "panic-on-unmasked-alarm", value_enum)]
    panic_on_unmasked_alarm: Option<PanicOnUnmaskedAlarm>,

    /// File containing paper tape data
    #[arg(action = Set)]
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
            Ok(metadata) => usize::try_from(metadata.len()).ok(),
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

    let mut clk: BasicClock = BasicClock::new();
    // We have two simimarly-named enums here so that the cpu crate
    // does not have to depend on clap.
    let panic_on_unmasked_alarm = match cli.panic_on_unmasked_alarm {
        Some(PanicOnUnmaskedAlarm::Yes) => cpu::PanicOnUnmaskedAlarm::Yes,
        Some(PanicOnUnmaskedAlarm::No) | None => cpu::PanicOnUnmaskedAlarm::No,
    };
    let initial_context = clk.make_fresh_context();
    let mut tx2 = Tx2::new(&initial_context, panic_on_unmasked_alarm, &mem_config);
    if let Some(tape) = tape_data {
        if let Err(e) = tx2.mount_tape(&initial_context, tape) {
            return Err(Box::new(e));
        }
    }
    run(&mut tx2, &mut clk, sleep_multiplier)
}

fn main() {
    match run_simulator() {
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
