use cpu::Context;
use std::time::Duration;

mod utils;

use float_next_after::NextAfter;
use tracing::{event, Level};
use wasm_bindgen::prelude::*;

use cpu::*;

#[wasm_bindgen(start)]
pub fn start() -> Result<(), JsValue> {
    utils::set_panic_hook();

    // print pretty errors in wasm https://github.com/rustwasm/console_error_panic_hook
    // This is not needed for tracing_wasm to work, but it is a common tool for getting proper error line numbers for panics.
    console_error_panic_hook::set_once();

    // Add this line:
    tracing_wasm::set_as_global_default();

    Ok(())
}

fn make_context(simulated_system_time_secs: f64, elapsed_time_secs: f64) -> Context {
    Context {
        simulated_time: Duration::from_secs_f64(simulated_system_time_secs),
        real_elapsed_time: Duration::from_secs_f64(elapsed_time_secs),
    }
}

#[wasm_bindgen]
pub fn create_tx2(simulated_system_time_secs: f64, elapsed_time_secs: f64) -> Tx2 {
    let mem_config = MemoryConfiguration {
        with_u_memory: false,
    };
    let context = make_context(simulated_system_time_secs, elapsed_time_secs);
    let panic_on_unmasked_alarm = cpu::PanicOnUnmaskedAlarm::No;
    Tx2::new(&context, panic_on_unmasked_alarm, &mem_config)
}

#[wasm_bindgen]
pub fn tx2_next_simulated_tick(tx2: &Tx2) -> f64 {
    let next = tx2.next_tick();
    // We use next_after to round f up slightly to ensure that the
    // tick time used by the next JS call to tick() is actually a
    // different time to the current tick.
    let f = next.as_secs_f64().next_after(std::f64::INFINITY);
    event!(
        Level::INFO,
        "tx2_next_simulated_tick: next={next:?}, f={f:?}"
    );
    f
}

#[wasm_bindgen]
pub fn tx2_do_tick(tx2: &mut Tx2, simulated_time: f64, real_elapsed_time: f64) {
    let context = make_context(simulated_time, real_elapsed_time);
    event!(
        Level::INFO,
        "tx2_do_tick: simulated_time={simulated_time:?}, real_elapsed_time={real_elapsed_time:?}, context={context:?}"
    );
    match tx2.tick(&context) {
        Ok(Some(_output)) => {
            event!(Level::DEBUG, "dropping a Tx2 output event");
        }
        Ok(None) => (),
        Err(e) => {
            panic!("TX-2 alarm: {:?}", e);
        }
    }
}

#[wasm_bindgen]
pub fn tx2_codabo(tx2: &mut Tx2, simulated_time: f64, elapsed_time_secs: f64) {
    event!(Level::INFO, "codabo");
    let context = make_context(simulated_time, elapsed_time_secs);
    tx2.codabo(&context, &ResetMode::ResetTSP);
    tx2.set_next_execution_due(context.simulated_time, Some(context.simulated_time));
    tx2.set_run_mode(RunMode::Running);
}

#[wasm_bindgen]
pub fn tx2_load_tape(tx2: &mut Tx2, simulated_time: f64, elapsed_time_secs: f64, data: &[u8]) {
    let context = make_context(simulated_time, elapsed_time_secs);
    tx2.mount_tape(&context, data.to_vec());
}
