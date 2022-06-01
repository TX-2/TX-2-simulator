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
    let prev_alarm_status: AlarmStatusByAlarmName = alarm_status_by_alarm_name();
    wasm.tx2_do_tick(tx2, tick_time, clamped_elapsed_time());
    update_alarm_status_changes(prev_alarm_status, alarm_status_by_alarm_name());

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

export function alarm_names(): string[] {
    return wasm.all_alarm_info(tx2)
	.map((item) => item.name);
}

export interface AlarmStatus {
    name: string,
    maskable: boolean,
    masked: boolean,
    active: boolean,
    message: string,
}

interface AlarmStatusByAlarmName {
    [name: string]: AlarmStatus,
}

function alarm_status_by_alarm_name(): AlarmStatusByAlarmName {
    let alarm_status: AlarmStatusByAlarmName = {};
    all_alarm_info().forEach((st) => {
	console.log({st});
	alarm_status[st.name] = st;
    });
    console.log({alarm_status});
    return alarm_status;
}

export function all_alarm_info(): AlarmStatus[] {
    const result: AlarmStatus[] = wasm.get_alarm_statuses(tx2)
	.map((wasm_status) => {
	    return {
		name: wasm_status.name,
		maskable: wasm_status.maskable,
		masked: wasm_status.masked,
		active: wasm_status.active,
		message: wasm_status.message
	    };
	});
    console.log({result});
    return result;
}

export function set_alarm_masked(alarm_name: string, masked: boolean) {
    // TODO: error handling of failure in set_alarm_masked
    wasm.set_alarm_masked(tx2, alarm_name, masked);
}


let alarm_status_callbacks = {};
interface AlarmControlState {
  masked: boolean;
  active: boolean;
  message: string;
}

function alarm_status_changed(old_state: AlarmStatus, new_state: AlarmStatus): boolean {
    if (old_state.name != new_state.name) {
	console.error("comparing states for different alarms is not allowed");
	return true;
    }
    if (old_state.maskable != new_state.maskable) {
	console.error("maskable should be an immutable property");
	return true;
    }
    if (old_state.masked != new_state.masked) {
	return true;
    }
    if (old_state.active != new_state.active) {
	return true;
    }
    if (old_state.message != new_state.message) {
	return true;
    }
    return false;
}

interface AlarmStatusCallback {
    (status: AlarmControlState): void;
}

export function set_alarm_status_callback(name: string, f: AlarmStatusCallback | null): void {
    alarm_status_callbacks[name] = f;
}

function update_alarm_status_changes(prev: AlarmStatusByAlarmName, current: AlarmStatusByAlarmName): void {
    let anything_changed: boolean = false;
    for (let name in current) {
	const old_status = prev[name];
	const current_status = current[name];
	if (alarm_status_changed(old_status, current_status)) {
	    console.log("Status change for " + name + " alarm", {old_status, current_status});
	    let callback = alarm_status_callbacks[name];
	    if (callback != null) {
		console.log("Calling the callback for " + name + " alarm");
		anything_changed = true;
		callback(current_status);
	    } else {
		console.log("There is no update callback for " + name + " alarm");
	    }
	} else {
	    let status = current[name];
	    console.log("Status of " + name + " alarm is unchanged: ", {status});
	}
    }
    if (anything_changed) {
	console.log("An alarm status changed");
    } else {
	console.log("No alarm status changed");
    }
}
