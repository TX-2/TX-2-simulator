// This module is a TypeScript interface to the WASM code.
//
let wasm;			// the WASM module.
const START_TIME: number = Date.now();
let running: boolean = false;
let systemTime: number = 0.0;
let tx2;

function clamped_elapsed_time(): number {
    var now = Date.now();
    return Math.max(now - START_TIME, 0.0);
}

export function set_app_wasm_mod(m) {
    wasm = m;
}

export function create_tx2() {
    tx2 = wasm.create_tx2(systemTime, clamped_elapsed_time());
}

export function codabo() {
    wasm.tx2_codabo(tx2, systemTime, clamped_elapsed_time());
    tick_after(0.0, systemTime + 1.0e-6);
}


export function load_tape(bytes: Uint8Array) {
    wasm.tx2_load_tape(tx2, systemTime, clamped_elapsed_time(), bytes);
}

function tick_after(interval: number, system_time_then: number) {
    let delay_ms = interval * 1000.0;
    return setTimeout(do_tick, delay_ms, system_time_then);
}

function do_tick(tick_time: number) {
    console.log("do_tick for tick_time=" + tick_time);
    systemTime = tick_time;
    wasm.tx2_do_tick(tx2, tick_time, clamped_elapsed_time());
    if (running) {
	let next_tick_at: number = wasm.tx2_next_simulated_tick(tx2);
	let interval: number = next_tick_at - tick_time;
	console.log("do_tick: interval=" + interval + "; next_tick_at=", next_tick_at);
	tick_after(interval, next_tick_at);
    } else {
	console.log("System clock is not running, not scheduling next tick");
    }
}

export function start_clock() {
    running = true;
    tick_after(0.0, systemTime + 1e-6);
}

export function stop_clock() {
    running = false;
}

export function is_clock_running(): boolean {
    return running;
}
