use core::time::Duration;

#[derive(Debug)]
pub struct Context {
    pub simulated_time: Duration,
    pub real_elapsed_time: Duration,
}

impl Context {
    pub fn new(simulated_time: Duration, real_elapsed_time: Duration) -> Context {
        Context {
            simulated_time,
            real_elapsed_time,
        }
    }
}
