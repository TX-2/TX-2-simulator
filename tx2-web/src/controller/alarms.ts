import { get_app_wasm_mod } from '../model/machine'
import { Tx2Controller } from './tx2'

export interface AlarmStatus {
    name: string,
    maskable: boolean,
    masked: boolean,
    active: boolean,
    message: string,
}

export interface AlarmStatusByAlarmName {
    [name: string]: AlarmStatus,
}

export interface AlarmStatusCallback {
    (status: AlarmControlState): void;
}

export interface AlarmControlState {
  masked: boolean;
  active: boolean;
  message: string;
}

function alarm_status_changed(
    old_state: AlarmStatus | undefined,
    new_state: AlarmStatus
): boolean {
    if (!old_state) {
        return true;
    }
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

interface AlarmStatusCallbackByName {
    [index: string]: AlarmStatusCallback | null
}

export class AlarmController {
    alarm_status_callbacks: AlarmStatusCallbackByName;
    tx2: Tx2Controller;
    wasm;

    constructor(tx2: Tx2Controller) {
        this.alarm_status_callbacks = {};
        this.tx2 = tx2;
        this.wasm = get_app_wasm_mod();
    }

    // TODO: The binding between this callback and the properties of
    // AlarmPanel happens in MainGrid.tsx, at the point where the
    // AlarmPanel is created.  But this looks to me like too much of
    // the internals of AlarmPanel being exposed to MainGrid.
    set_alarm_status_callback(name: string, f: AlarmStatusCallback | null): void {
        this.alarm_status_callbacks[name] = f;
    }

    update_status_around(f: ()=>void): void {
        const prev_alarm_status: AlarmStatusByAlarmName = this.alarm_status_by_alarm_name();
        f();
        this.update_alarm_status_changes(prev_alarm_status, this.alarm_status_by_alarm_name());
    }

    private update_alarm_status_changes(prev: AlarmStatusByAlarmName | null,
                                        current: AlarmStatusByAlarmName): void {
        let anything_changed: boolean = !prev;
        for (let name in current) {
            const old_status = prev?.[name];
            const current_status = current[name];
            if ((!prev) || alarm_status_changed(old_status, current_status)) {
                let callback = this.alarm_status_callbacks[name];
                if (callback != null) {
                    anything_changed = true;
                    callback(current_status);
                }
            }
        }
    }

    alarm_names(): string[] {
        // TODO: is this function used?
        return this.all_alarm_info()
            .map((item) => item.name);
    }

    private alarm_status_by_alarm_name(): AlarmStatusByAlarmName {
        // TODO: is this function used?
        let alarm_status: AlarmStatusByAlarmName = {};
        this.all_alarm_info().forEach((st) => {
            alarm_status[st.name] = st;
        });
        return alarm_status;
    }

    all_alarm_info(): AlarmStatus[] {
        const result: AlarmStatus[] = this.wasm.get_alarm_statuses(this.tx2)
            .map((wasm_status: any) => {
                return {
                    name: wasm_status.name,
                    maskable: wasm_status.maskable,
                    masked: wasm_status.masked,
                    active: wasm_status.active,
                    message: wasm_status.message
                };
            });
        return result;
    }

    set_alarm_masked(alarm_name: string, masked: boolean): void {
        // TODO: error handling of failure in set_alarm_masked
        this.wasm.set_alarm_masked(this.tx2, alarm_name, masked);
    }
}
