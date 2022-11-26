import { create_tx2, get_builtin_sample_tape, Tx2, tx2_codabo, tx2_device_statuses, tx2_do_tick, tx2_drain_device_changes, tx2_load_tape, tx2_lw_keyboard_click, tx2_next_simulated_tick, tx2_unmasked_alarm_active } from '../../build/tx2_web';
import { AlarmController } from './alarms'
import { IoController } from './io'
import { WasmUnitState } from './types'

type RunChangeCallback = (run: boolean) => void;

type KeystrokeOutcome = {
    consumed: boolean;
    flag_raised: boolean;
    far_keyboard_is_active: boolean;
}

// TODO: use a consistent naming scheme for methods.
export class Tx2Controller {
    alarmController: AlarmController;
    ioController: IoController;
    running: boolean;
    startTime: number;
    systemTime: number;
    runChangeCallback: RunChangeCallback | null;
    tx2: Tx2;

    constructor() {
        this.startTime = Date.now();
        this.systemTime = 0.0;
        this.running = false;
        this.tx2 = create_tx2(this.systemTime, this.clamped_elapsed_seconds());
        this.alarmController = new AlarmController(this.tx2);
        this.ioController = new IoController(this);
        this.runChangeCallback = null;
    }

    reset_start_time(): void {
        this.startTime = Date.now() - (1000.0 * this.systemTime);
    }

    clamped_elapsed_seconds(): number {
        const  now = Date.now();
        return Math.max(now - this.startTime, 0.0) / 1000.0;
    }

    codabo(): void {
        tx2_codabo(this.tx2, this.systemTime, this.clamped_elapsed_seconds());
        this.changeRun(true);
        this.ioController.update_status();
        this.alarmController.update_status();
    }

    loadTape(bytes: Uint8Array): void {
        tx2_load_tape(this.tx2, this.systemTime, this.clamped_elapsed_seconds(), bytes);
        this.ioController.update_status();
    }

    loadSample(name: string): void {
        const data = get_builtin_sample_tape(name);
        tx2_load_tape(this.tx2, this.systemTime, this.clamped_elapsed_seconds(), data);
        this.ioController.update_status();
    }

    lwKeyPress(unit: number, far_currently_active: boolean, rgb: Uint8ClampedArray): KeystrokeOutcome {
        const result = tx2_lw_keyboard_click(this.tx2, this.systemTime, this.clamped_elapsed_seconds(), unit, far_currently_active, rgb);
        if (result.flag_raised && this.running) {
            console.log("LW key press may have resulted in a flag raise, scheduling a tick soon");
            this.tickSoon();
        }
        return result;
    }

    tick_after(interval: number, system_time_then: number): void {
        const delay_ms = interval * 1000.0;
        setTimeout(this.do_tick.bind(this), delay_ms, system_time_then);
    }

    do_tick(tick_time: number): void {
        if (!this.running) {
            console.log("System clock is not running, abandoning tick");
            return;
        }

        this.systemTime = tick_time;
        for (let iterations = 0; ; ++iterations) {
            const elapsed = this.clamped_elapsed_seconds();
            tx2_do_tick(this.tx2, tick_time, elapsed);
            if (tx2_unmasked_alarm_active(this.tx2)) {
                break;
            }
            const next_tick_at: number = tx2_next_simulated_tick(this.tx2);
            tick_time = next_tick_at;
            let yield_control = false;
            if (iterations > 20) {
                /* Bail out of the loop in order to give other things
                 * access to the main thread. */
                yield_control = true;
            } else if (next_tick_at > elapsed) {
                yield_control = true;
            }
            if (yield_control) {
                const interval: number = next_tick_at - elapsed;
                this.tick_after(interval, next_tick_at);
                break;
            }
        }
        if (tx2_unmasked_alarm_active(this.tx2)) {
            console.log("An unmasked alarm is active.");
            this.changeRun(false);
        }

        this.ioController.update_status();
        this.alarmController.update_status();
    }

    tickSoon() {
        this.tick_after(0.0, this.systemTime + 1e-6);
    }

    changeRun(run: boolean): void {
        const wasRunning = this.running;
        this.running = run;
        if (this.running &&  !wasRunning) {
            this.reset_start_time();
            this.tickSoon();
        }
        if (this.running != wasRunning) {
            // Update the UI.
            if (this.runChangeCallback != null) {
                this.runChangeCallback(this.running);
            }
        }
    }

    setRunChangeCallback(callback: (run: boolean) => void) {
        this.runChangeCallback = callback;
    }

    unsetRunChangeCallback() {
        this.runChangeCallback = null;
    }

    isClockRunning(): boolean {
        return !!this.running;
    }

    get_device_statuses(): ArrayLike<WasmUnitState> {
        return (tx2_device_statuses(this.tx2, this.systemTime, this.clamped_elapsed_seconds()) as ArrayLike<WasmUnitState>);
    }

    drain_device_status_changes(): Map<number, WasmUnitState> {
        return (tx2_drain_device_changes(this.tx2, this.systemTime, this.clamped_elapsed_seconds()) as Map<number, WasmUnitState>);
    }
}
