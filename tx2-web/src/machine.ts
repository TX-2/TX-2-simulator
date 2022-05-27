// This module is a TypeScript interface to the WASM code.
//
var wasm;			// the WASM module.
const START_TIME: number = Date.now();
var systemTime: number = 0.0;
var tx2;

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
}


export function load_tape(bytes: Uint8Array) {
    wasm.tx2_load_tape(tx2, systemTime, clamped_elapsed_time(), bytes);
}
