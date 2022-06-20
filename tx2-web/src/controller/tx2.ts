import { create_tx2, get_builtin_sample_tape, Tx2, tx2_codabo, tx2_device_statuses, tx2_do_tick, tx2_drain_device_changes, tx2_load_tape, tx2_next_simulated_tick, tx2_unmasked_alarm_active } from '../../build/tx2_web';
import { AlarmController } from './alarms'
import { IoController } from './io'
import { WasmUnitState } from './types'

type RunChangeCallback = (run: boolean) => void;

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
        this.tx2 = create_tx2(this.systemTime, this.clamped_elapsed_time());
        this.alarmController = new AlarmController(this.tx2);
        this.ioController = new IoController(this);
        this.runChangeCallback = null;
    }

    clamped_elapsed_time(): number {
        const  now = Date.now();
        return Math.max(now - this.startTime, 0.0);
    }

    codabo(): void {
	tx2_codabo(this.tx2, this.systemTime, this.clamped_elapsed_time());
        this.ioController.update_status();
        this.alarmController.update_status();
        this.changeRun(true);
    }

    loadTape(bytes: Uint8Array): void {
        tx2_load_tape(this.tx2, this.systemTime, this.clamped_elapsed_time(), bytes);
        this.ioController.update_status();
    }

    loadSample(name: string): void {
	const data = get_builtin_sample_tape(name);
        tx2_load_tape(this.tx2, this.systemTime, this.clamped_elapsed_time(), data);
        this.ioController.update_status();
    }

    tick_after(interval: number, system_time_then: number): void {
        const delay_ms = interval * 1000.0;
        setTimeout(this.do_tick.bind(this), delay_ms, system_time_then);
    }

    do_tick(tick_time: number): void {
        this.systemTime = tick_time;
        tx2_do_tick(this.tx2, tick_time, this.clamped_elapsed_time());
        this.ioController.update_status();
        this.alarmController.update_status();

        if (tx2_unmasked_alarm_active(this.tx2)) {
            console.log("An unmasked alarm is active.");
            this.changeRun(false);
        }
        if (this.running) {
            const next_tick_at: number = tx2_next_simulated_tick(this.tx2);
            const interval: number = next_tick_at - tick_time;
            this.tick_after(interval, next_tick_at);
        } else {
            console.log("System clock is not running, not scheduling next tick");
        }
    }

    changeRun(run: boolean): void {
        const wasRunning = this.running;
        this.running = run;
        if (this.running &&  !wasRunning) {
            this.tick_after(0.0, this.systemTime + 1e-6);
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
        return (tx2_device_statuses(this.tx2, this.systemTime, this.clamped_elapsed_time()) as ArrayLike<WasmUnitState>);
    }

    drain_device_status_changes(): Map<number, WasmUnitState> {
        return (tx2_drain_device_changes(this.tx2, this.systemTime, this.clamped_elapsed_time()) as Map<number, WasmUnitState>);
    }
}
