use std::ffi::OsString;
use std::fs::File;
use std::fs::OpenOptions;
use std::time::Duration;

use clap::{App, Arg};
use tracing::{event, Level};
use tracing_subscriber::prelude::*;

use base::prelude::*;
use cpu::io::{Petr, TapeIterator};
use cpu::{
    Alarm, BasicClock, Clock, ControlUnit, MemoryConfiguration, MemoryUnit, MinimalSleeper,
    ResetMode,
};

fn run(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
    multiplier: Option<f64>,
) -> i32 {
    control.codabo(&ResetMode::ResetTSP, mem);
    if let Err(e) = run_until_alarm(control, mem, clk, multiplier) {
        event!(Level::ERROR, "Execution stopped: {}", e);
    }
    1
}

fn run_until_alarm(
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
            cpu::time_passes(clk, &mut sleeper, &interval, multiplier);
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
                cpu::time_passes(clk, &mut sleeper, &Duration::from_nanos(ns), multiplier);
                ns
            }
        };
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

fn run_simulator() -> Result<(), Box<dyn std::error::Error>> {
    let matches = App::new("TX-2 Emulator")
        .author("James Youngman <youngman@google.com>")
        .about("Simulate the historic TX-2 computer")
        .arg(
            Arg::with_name("PTAPE")
                .help("File containing paper tape data")
                .multiple(true)
                .required(false),
        )
        .arg(
            Arg::with_name("speed-multiplier")
                .help("Run this many times faster than real-time ('MAX' for as-fast-as-possible)")
                .takes_value(true)
                .long("speed-multiplier")
                .required(false),
        )
        .get_matches();

    // See
    // https://docs.rs/tracing-subscriber/0.2.19/tracing_subscriber/fmt/index.html#filtering-events-with-environment-variables
    // for instructions on how to select which trace messages get
    // printed.
    let fmt_layer = tracing_subscriber::fmt::layer().with_target(true);
    let filter_layer = match tracing_subscriber::EnvFilter::try_from_default_env()
        .or_else(|_| tracing_subscriber::EnvFilter::try_new("info"))
    {
        Err(e) => {
            return Err(Box::new(e));
        }
        Ok(layer) => layer,
    };

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let mem_config = MemoryConfiguration {
        with_u_memory: false,
    };

    let tapes = TapeSequence::new(
        matches
            .values_of_os("PTAPE")
            .unwrap_or_else(Default::default)
            .into_iter()
            .map(OsString::from)
            .collect(),
    );
    if tapes.is_empty() {
        event!(
            Level::WARN,
            "No paper tapes were specified on the command line, so no program will be loaded"
        );
    }
    let petr = Box::new(Petr::new(Box::new(tapes)));

    let speed_multiplier: Option<f64> = match matches.value_of("speed-multiplier") {
        None => {
            event!(
                Level::WARN,
                "No --speed-multiplier option specified, running at maximum speed"
            );
            None
        }
        Some("MAX") => {
            event!(
                Level::INFO,
                "--speed-multiplier=MAX, running at maximum speed"
            );
            None
        }
        Some(s) => match s.parse::<f64>() {
            Ok(x) => {
                event!(
                    Level::INFO,
                    "--speed-multiplier={}, running at speed multiplier {}",
                    s,
                    x
                );
                Some(x)
            }
            Err(e) => {
                return Err(Box::new(e));
            }
        },
    };

    let mut control = ControlUnit::new();
    let mut clk: BasicClock = BasicClock::new();

    let petr_unit: Unsigned6Bit = Unsigned6Bit::try_from(0o52_u8).unwrap();
    control.attach(&clk.now(), petr_unit, false, petr);
    event!(
        Level::DEBUG,
        "Initial control unit state iis {:?}",
        &control
    );
    let mut mem = MemoryUnit::new(&mem_config);
    std::process::exit(run(&mut control, &mut mem, &mut clk, speed_multiplier));
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
