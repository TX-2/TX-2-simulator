import * as wasm from "tx-2-wasm";

function clamped_elapsed_time(then) {
    var now = Date.now();
    return Math.max(now - then, 0.0);
}

function call_after(t, f) {
    var delay_ms = t * 1000.0;
    var id = setTimeout(f, delay_ms);
    console.log("call_after: timeout id = " + id + ", delay_ms=" + delay_ms);
    return id;
}

function tick_after(interval, system_time_then) {
    call_after(interval, function() { do_tick(system_time_then) });
}

function do_tick(tick_time) {
    var elapsed = clamped_elapsed_time(start);
    wasm.tx2_do_tick(tx2, tick_time, elapsed);
    var next_tick_at = wasm.tx2_next_simulated_tick(tx2);
    var interval = next_tick_at - tick_time;
    tick_after(interval, next_tick_at);
}

function codabo(simulated_system_time_secs, real_elapsed_time) {
    wasm.tx2_codabo(tx2, simulated_system_time_secs, real_elapsed_time)
}

var start = Date.now();
var sleep_multiplier = 1.0;

const tx2 = wasm.create_tx2(0.0, 0.0);
console.log("preparing for first tick");
codabo(0.0, start)
tick_after(1e-6, 1e-6);
