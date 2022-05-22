use cpu::Context;
use std::time::Duration;

mod utils;

use cpu::*;
use wasm_bindgen::prelude::*;

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

#[wasm_bindgen]
pub fn create_tx2(simulated_system_time_secs: f64, elapsed_time_secs: f64) -> Tx2 {
    let mem_config = MemoryConfiguration {
        with_u_memory: false,
    };
    let context = Context {
        simulated_time: Duration::from_secs_f64(simulated_system_time_secs),
        real_elapsed_time: Duration::from_secs_f64(elapsed_time_secs),
    };
    let panic_on_unmasked_alarm = cpu::PanicOnUnmaskedAlarm::No;
    Tx2::new(&context, panic_on_unmasked_alarm, &mem_config)
}
