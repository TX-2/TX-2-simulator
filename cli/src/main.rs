use std::time::Duration;

use tracing::{event, Level};
use tracing_subscriber::prelude::*;

use cpu::{Alarm, BasicClock, Clock, ControlUnit, MemoryConfiguration, MemoryUnit, MinimalSleeper, ResetMode};

fn run_until_alarm(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit
) -> Result<(), Alarm> {
    let mut elapsed_ns: u64 = 0;
    let mut sleeper = MinimalSleeper::new(Duration::from_millis(2));
    let mut clk = BasicClock::new(1.0).expect("reasonable clock config");
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

fn run(control: &mut ControlUnit, mem: &mut MemoryUnit) -> i32 {
    control.codabo(&ResetMode::ResetTSP);
    if let Err(e) = run_until_alarm(control, mem) {
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

fn main() {
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
    let mut control = ControlUnit::new();
    event!(Level::DEBUG, "Initial control unit state iis {:?}", &control);
    let mut mem = MemoryUnit::new(&mem_config);
    std::process::exit(run(&mut control, &mut mem));
}
