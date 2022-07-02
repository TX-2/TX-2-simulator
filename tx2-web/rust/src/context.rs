use std::time::Duration;

use cpu::Context;

pub(crate) fn make_context(simulated_system_time_secs: f64, elapsed_time_secs: f64) -> Context {
    Context {
        simulated_time: Duration::from_secs_f64(simulated_system_time_secs),
        real_elapsed_time: Duration::from_secs_f64(elapsed_time_secs),
    }
}
