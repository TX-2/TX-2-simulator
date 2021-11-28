use cpu::{Alarm, ControlUnit, MemoryConfiguration, MemoryUnit, ResetMode};

use tracing::{event, Level};
use tracing_subscriber::prelude::*;

fn run_until_alarm(control: &mut ControlUnit, mem: &mut MemoryUnit) -> Result<(), Alarm> {
    let mut elapsed_ns: u64 = 0;
    loop {
        if !control.fetch_instruction(mem)? {
            break;
        }
        elapsed_ns += match control.execute_instruction(mem) {
	    Err(e) => {
		event!(Level::INFO, "Alarm raised after {}ns", elapsed_ns);
		return Err(e);
	    }
	    Ok(ns) => ns
	};
    }
    event!(Level::INFO, "Stopped after {}ns", elapsed_ns);
    Ok(())
}

fn run(control: &mut ControlUnit, mem: &mut MemoryUnit) {
    control.codabo(&ResetMode::ResetTSP);
    if let Err(e) = run_until_alarm(control, mem) {
        event!(Level::ERROR, "Execution stopped: {}", e);
    } else {
	event!(
	    Level::INFO,
	    "machine is in limbo, terminating since there are no I/O devices yet",
	);
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
    run(&mut control, &mut mem);
}
