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
    if (running) {
	var next_tick_at = wasm.tx2_next_simulated_tick(tx2);
	var interval = next_tick_at - tick_time;
	tick_after(interval, next_tick_at);
    } else {
	console.log("Sync system is not running, not scheduling next tick");
    }
}

function codabo(simulated_system_time_secs, real_elapsed_time) {
    wasm.tx2_codabo(tx2, simulated_system_time_secs, real_elapsed_time)
}

function load_petr_tape() {
    const file = this.files[0];
    console.log("Attempting to load a tape " + file.name + " which has length " + file.length);
    var reader = new FileReader();
    reader.addEventListener('loadend', function (e) {
	var system_time = get_current_system_time();
	var elapsed_time = get_current_elapsed_time();
	var bytes = new Uint8Array(e.target.result);
        wasm.tx2_load_tape(tx2, system_time, elapsed_time, bytes);

	// Hide the dialog again.
	var modal = document.getElementById("tapeLoadModal");
	modal.style.display = "none";
    });
    reader.readAsArrayBuffer(file);
}


function update_sync_button_text() {
    var syncBtn = document.getElementById("syncBtn");
    if (running) {
	syncBtn.innerHTML = "Sync: Stop";
    } else {
	syncBtn.innerHTML = "Sync: Start";
    }
}


function set_up_sync_system() {
    var syncBtn = document.getElementById("syncBtn");
    syncBtn.onclick = sync_start_stop;
    running = false;
    update_sync_button_text();
}

function sync_start_stop() {
    if (running) {
	console.log("sync: stop");
    } else {
	console.log("sync: stop");
    }
    running = !running;
    update_sync_button_text();
    if (running) {
	tick_after(get_current_system_time() + 1e-6, get_current_elapsed_time() + 1e-6);
    }
}

function set_up_tape_loading_dialog() {
    console.log("set_up_tape_loading_dialog...");
    // Get the modal
    var modal = document.getElementById("tapeLoadModal");

    // Get the button that opens the modal
    var btn = document.getElementById("tapeLoadBtn");

    // Get the <span> element that closes the modal
    var span = document.getElementsByClassName("close")[0];

    // When the user clicks on the button, open the modal
    btn.onclick = function() {
	modal.style.display = "block";
    }

    // When the user clicks on <span> (x), close the modal
    span.onclick = function() {
	modal.style.display = "none";
    }

    // When the user selects a file, load it.
    var input = document.getElementById("tape_load_file");
    input.addEventListener("change", load_petr_tape, false);

    // When the user clicks anywhere outside of the modal, close it
    window.onclick = function(event) {
        if (event.target == modal) {
            modal.style.display = "none";
        }
    }
}

function set_up_codabo_button() {
    var btn = document.getElementById("codaboTSRBtn");
    btn.onclick = function() {
        codabo(get_current_system_time(), get_current_elapsed_time());
    }
}

function set_up_ui() {
    set_up_sync_system();
    set_up_codabo_button();
    set_up_tape_loading_dialog();
}

function get_current_system_time() {
    return current_system_time;
}

function get_current_elapsed_time() {
    return clamped_elapsed_time(start);
}

/* Set up the TX-2. */
var running = false;
var start = Date.now();
var sleep_multiplier = 1.0;
var current_system_time = 0.0;

const tx2 = wasm.create_tx2(0.0, 0.0);

/* Set up event listeners. */
set_up_ui();
