#![deny(unreachable_pub)]
#![deny(unsafe_code)]
#![deny(unused_crate_dependencies)]

mod alarm;
mod context;
mod io;
mod lw;
mod samples;
mod utils;

use cpu::*;

use float_next_after::NextAfter;
use lw::display_lw_unit_output_event;
use tracing::{event, Level};
use wasm_bindgen::prelude::*;
use web_sys::{Document, Window};

pub use alarm::{
    drain_alarm_changes, get_alarm_statuses, set_alarm_masked, tx2_unmasked_alarm_active,
};
use context::make_context;
pub use io::HtmlCanvas2DPainter;
pub use io::*;

#[wasm_bindgen(start)]
pub fn start() -> Result<(), JsValue> {
    utils::set_panic_hook();
    Ok(())
}

fn try_log_level_from_str(log_level: &str) -> Result<Level, String> {
    match log_level {
        "trace" => Ok(Level::TRACE),
        "debug" => Ok(Level::DEBUG),
        "info" => Ok(Level::INFO),
        "warn" => Ok(Level::WARN),
        "error" => Ok(Level::ERROR),
        invalid => Err(format!("invalid log level '{invalid}'")),
    }
}

#[wasm_bindgen]
pub fn init(log_level: &str) -> Result<(), JsValue> {
    tracing_wasm::set_as_global_default_with_config(
        tracing_wasm::WASMLayerConfigBuilder::new()
            .set_max_level(try_log_level_from_str(log_level)?)
            .build(),
    );
    event!(
        Level::INFO,
        "init: tracing iniialised (max level is {log_level})"
    );
    Ok(())
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
        Level::TRACE,
        "tx2_next_simulated_tick: next={next:?}, f={f:?}"
    );
    f
}

fn window() -> Window {
    web_sys::window().expect("no global window exists")
}

fn document() -> Document {
    window()
        .document()
        .expect("should have a document on the window")
}

fn display_output_event(output_event: OutputEvent) {
    match output_event {
        OutputEvent::LincolnWriterPrint { unit, ch } => {
            let doc: Document = document();
            display_lw_unit_output_event(unit, ch, doc)
        }
    }
}

#[wasm_bindgen]
pub fn tx2_do_tick(tx2: &mut Tx2, simulated_time: f64, real_elapsed_time: f64) {
    let context = make_context(simulated_time, real_elapsed_time);
    event!(
        Level::TRACE,
        "tx2_do_tick: simulated_time={simulated_time:?}, real_elapsed_time={real_elapsed_time:?}, context={context:?}"
    );
    match tx2.tick(&context) {
        Ok(Some(output)) => {
            event!(
                Level::INFO,
                "tx2_do_tick: handling output event for {output:?}"
            );
            display_output_event(output);
        }
        Ok(None) => (),
        Err(e) => {
            event!(Level::ERROR, "New unmasked TX-2 alarm: {:?}", e);
        }
    }
}

#[wasm_bindgen]
pub fn tx2_codabo(tx2: &mut Tx2, simulated_time: f64, elapsed_time_secs: f64) {
    event!(Level::INFO, "codabo");
    let context = make_context(simulated_time, elapsed_time_secs);
    if let Err(e) = tx2.codabo(&context, &ResetMode::ResetTSP) {
        panic!("codabo failed: {}", e);
    }
    tx2.set_next_execution_due(context.simulated_time, Some(context.simulated_time));
    tx2.set_run_mode(RunMode::Running);
}

#[wasm_bindgen]
pub fn create_html_canvas_2d_painter(
    context: web_sys::CanvasRenderingContext2d,
) -> Result<HtmlCanvas2DPainter, JsValue> {
    HtmlCanvas2DPainter::new(context).map_err(|e| e.msg.into())
}
