use cpu::{Alarm, ControlUnit, MemoryConfiguration, MemoryUnit, ResetMode};

fn run_until_alarm(control: &mut ControlUnit, mem: &mut MemoryUnit) -> Result<(), Alarm> {
    loop {
        if !control.fetch_instruction(mem)? {
            break;
        }
        control.execute_instruction(mem)?;
    }
    println!("machine is in limbo, terminating since there are no I/O devices yet");
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
