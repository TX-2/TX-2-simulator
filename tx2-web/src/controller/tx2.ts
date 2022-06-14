import { create_tx2, Tx2, tx2_codabo, tx2_device_statuses, tx2_do_tick, tx2_load_tape, tx2_next_simulated_tick, tx2_unmasked_alarm_active } from '../../build/tx2_web';
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
        this.ioController.update_status_around(() => {
            this.alarmController.update_status_around(() => {
		tx2_codabo(this.tx2, this.systemTime, this.clamped_elapsed_time());
            });
        });
        this.tick_after(0.0, this.systemTime + 1.0e-6);
    }

    loadTape(bytes: Uint8Array): void {
        this.ioController.update_status_around(() => {
            tx2_load_tape(this.tx2, this.systemTime, this.clamped_elapsed_time(), bytes);
        })
    }

    tick_after(interval: number, system_time_then: number): void {
        const delay_ms = interval * 1000.0;
        setTimeout(this.do_tick.bind(this), delay_ms, system_time_then);
    }

    do_tick(tick_time: number): void {
        console.log("do_tick for tick_time=" + tick_time.toString());
        this.systemTime = tick_time;
        this.ioController.update_status_around(() => {
            this.alarmController.update_status_around(
                () => {
                    tx2_do_tick(this.tx2, tick_time, this.clamped_elapsed_time());
                });
        });
        if (tx2_unmasked_alarm_active(this.tx2)) {
            console.log("An unmasked alarm is active.");
            this.changeRun(false);
        }
        if (this.running) {
            const next_tick_at: number = tx2_next_simulated_tick(this.tx2);
            const interval: number = next_tick_at - tick_time;
            console.log("do_tick: interval=" + interval.toString() + "; next_tick_at=", next_tick_at.toString());
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
                console.log("Tx2Controller: invoking runChangeCallback");
                this.runChangeCallback(this.running);
            } else {
                console.log("Tx2Controller: skipping runChangeCallback, no callback is registered");
            }
        } else {
            console.log("Tx2Controller: skipping runChangeCallback, no change");
        }
    }

    setRunChangeCallback(callback: (run: boolean) => void) {
        this.runChangeCallback = callback;
    }

    unsetRunChangeCallback() {
        this.runChangeCallback = null;
    }

    isClockRunning(): boolean {
        const result = !!this.running;
        console.log("Tx2Controller: isClockRunning: " + result.toString());
        return result;
    }

    get_device_statuses(): ArrayLike<WasmUnitState> {
        return (tx2_device_statuses(this.tx2, this.systemTime, this.clamped_elapsed_time()) as ArrayLike<WasmUnitState>);
    }
}
