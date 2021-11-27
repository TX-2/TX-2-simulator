use cpu::{Alarm, ControlUnit, MemoryConfiguration, MemoryUnit, ResetMode};

fn run_until_alarm(control: &mut ControlUnit, mem: &mut MemoryUnit) -> Result<(), Alarm> {
    let mut elapsed_ns: u64 = 0;
    loop {
        if !control.fetch_instruction(mem)? {
            break;
        }
        elapsed_ns += match control.execute_instruction(mem) {
	    Err(e) => {
		println!("Alarm raised after {}ns", elapsed_ns);
		return Err(e);
	    }
	    Ok(ns) => ns
	};
    }
    println!(
	"machine is in limbo after {}ns, terminating since there are no I/O devices yet",
	elapsed_ns
    );
    Ok(())
}

fn run(control: &mut ControlUnit, mem: &mut MemoryUnit) {
    control.codabo(&ResetMode::ResetTSP);
    if let Err(e) = run_until_alarm(control, mem) {
        eprintln!("Execution stopped: {}", e);
    }
}

fn main() {
    let mem_config = MemoryConfiguration {
        with_u_memory: false,
    };
    let mut control = ControlUnit::new();
    dbg!(&control);
    let mut mem = MemoryUnit::new(&mem_config);
    run(&mut control, &mut mem);
}
