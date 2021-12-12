use std::ffi::OsString;
use std::fs::File;
use std::fs::OpenOptions;

use clap::{App, Arg};
use tracing::{event, Level};
use tracing_subscriber::prelude::*;

use base::prelude::*;
use cpu::io::{Petr, TapeIterator};
use cpu::{
    run_until_alarm, BasicClock, Clock, ControlUnit, MemoryConfiguration, MemoryUnit, ResetMode,
};

fn run(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
    multiplier: Option<f64>,
) -> i32 {
    control.codabo(&ResetMode::ResetTSP);
    if let Err(e) = run_until_alarm(control, mem, clk, multiplier) {
        event!(Level::ERROR, "Execution stopped: {}", e);
    }
    1
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
    let petr = Box::new(Petr::new(Box::new(tapes)));

    let speed_multiplier: Option<f64> = match matches.value_of("speed-multiplier") {
        None => {
            event!(
                Level::INFO,
                "No --speed-multiplier option specified, using multiplier of 1.0"
            );
            Some(1.0)
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
