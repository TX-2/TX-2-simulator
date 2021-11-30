use std::ffi::OsString;
use std::fs::File;
use std::fs::OpenOptions;
use std::time::Duration;

use clap::{App, Arg};
use tracing::{event, Level};
use tracing_subscriber::prelude::*;

use base::prelude::*;
use cpu::{Alarm, BasicClock, Clock, ControlUnit, MemoryConfiguration, MemoryUnit, MinimalSleeper, ResetMode};
use cpu::io::{
    Petr,
    TapeIterator,
};

fn run_until_alarm(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
) -> Result<(), Alarm> {
    let mut elapsed_ns: u64 = 0;
    let mut sleeper = MinimalSleeper::new(Duration::from_millis(2));
    loop {
	control.poll_hardware(&clk.now())?; // check for I/O alarms, flag changes.
        if !control.fetch_instruction(mem)? {
            break;
        }
        elapsed_ns += match control.execute_instruction(&clk.now(), mem) {
	    Err(e) => {
		event!(Level::INFO, "Alarm raised after {}ns", elapsed_ns);
		return Err(e);
	    }
	    Ok(ns) => {
		let delay = clk.consume(&Duration::from_nanos(ns));
		sleeper.sleep(&delay);
		ns
	    }
	};
    }
    event!(Level::INFO, "Stopped after {}ns", elapsed_ns);
    Ok(())
}

fn run(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock
) -> i32 {
    control.codabo(&ResetMode::ResetTSP);
    if let Err(e) = run_until_alarm(control, mem, clk) {
        event!(Level::ERROR, "Execution stopped: {}", e);
	1
    } else {
	event!(
	    Level::INFO,
	    "machine is in limbo, terminating since there are no I/O devices yet",
	);
	0
    }
}

#[derive(Debug)]
struct TapeSequence {
    pos: usize,
    names: Vec<OsString>,
}

impl TapeSequence {
    fn new(names: Vec<OsString>) -> TapeSequence {
	TapeSequence {
	    pos: 0,
	    names,
	}
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

fn main() {
    let matches = App::new("TX-2 Emulator")
        .author("James Youngman <youngman@google.com>")
        .about("Simulate the historic TX-2 computer")
        .arg(Arg::with_name("PTAPE")
             .help("File containing paper tape data")
	     .multiple(true)
             .required(false))
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
	    eprintln!("{}", e);
            std::process::exit(1);
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
	matches.values_of_os("PTAPE")
	    .unwrap_or_else(Default::default).into_iter()
	    .map(OsString::from)
	    .collect());
    let petr = Box::new(Petr::new(Box::new(tapes)));
    let mut control = ControlUnit::new();
    let mut clk = BasicClock::new(1.0).expect("reasonable clock config");
    let petr_unit: Unsigned6Bit = Unsigned6Bit::try_from(0o52_u8).unwrap();
    control.attach(&clk.now(), petr_unit, false, petr);
    event!(Level::DEBUG, "Initial control unit state iis {:?}", &control);
    let mut mem = MemoryUnit::new(&mem_config);
    std::process::exit(run(&mut control, &mut mem, &mut clk));
}
