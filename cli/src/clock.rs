//! Simulation of elapsed time in the simulated system.
use cpu::Context;
use std::time::{Duration, SystemTime};
use tracing::{Level, event};

/// Clock is a simulated system clock.  Its run rate may be real-time
/// (i.e. one simulated second per actual wall-clock second) or it may
/// run faster or slower than real-time.
///
/// The clock keeps track of how many of its cycles have been
/// "consumed" by callers.  Callers requiring more clock cycles will
/// find that their calls to [`Clock::consume`] block so that their
/// average consumption of cycles matches the simulated clock rate.
///
/// On the other hand, if the simulated clock produces ticks very
/// rapidly (for example because it is set up to run 1,000,000x "real"
/// time) then callers will never block and hence can proceed as fast
/// as they are able.
pub trait Clock {
    /// Retrieves the current (simulated) time.
    fn now(&self) -> Duration;

    /// The caller calls `consume` to simulate the passing of a
    /// duration `interval`.  The returned value is the interval
    /// after which it is next OK to call `consume`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::thread::sleep;
    /// use std::time::Duration;
    /// use cpu::Clock;
    ///
    /// fn g<C: Clock>(clk: &mut C) {
    ///   // We just performed an action which would have taken
    ///   // one millisecond on the simulated machine.
    ///   clk.consume(&Duration::from_millis(1));
    /// }
    /// ```
    fn consume(&mut self, inteval: &Duration);
}

/// BasicClock provides a simulated clock.
///
/// # Examples
/// ```
/// use std::time::Duration;
/// use cpu::BasicClock;
/// use cpu::Clock;
/// let mut clk = BasicClock::new();
/// clk.consume(&Duration::from_micros(12));
/// ```
///
///
#[derive(Debug)]
pub struct BasicClock {
    /// Elapsed time as measured by the simulated clock.
    simulator_elapsed: Duration,

    /// Origin time for the simulated RTC.  When the SystemTime
    /// implementation appears to have advanced non-monotonically, we
    /// update wall_clock_time_origin.
    wall_clock_time_origin: SystemTime,
}

impl BasicClock {
    pub fn new() -> BasicClock {
        BasicClock {
            simulator_elapsed: Duration::new(0, 0),
            wall_clock_time_origin: SystemTime::now(),
        }
    }

    pub fn advance_to_simulated_time(&mut self, when: Duration) {
        self.simulator_elapsed = when;
    }

    pub fn make_fresh_context(&mut self) -> Context {
        let real_now = SystemTime::now();
        let elapsed = match real_now.duration_since(self.wall_clock_time_origin) {
            Ok(delta) => delta,
            Err(_) => {
                // simulate an RTC reset.
                event!(
                    Level::WARN,
                    "System time went backward, simulating RTC reset"
                );
                self.wall_clock_time_origin = real_now;
                Duration::new(0, 0)
            }
        };
        Context {
            simulated_time: self.simulator_elapsed,
            real_elapsed_time: elapsed,
        }
    }
}

impl Default for BasicClock {
    fn default() -> Self {
        Self::new()
    }
}

impl Clock for BasicClock {
    fn now(&self) -> Duration {
        self.simulator_elapsed
    }

    fn consume(&mut self, interval: &Duration) {
        self.simulator_elapsed += *interval;
    }
}
