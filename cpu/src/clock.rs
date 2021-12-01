//! Simulation of elapsed time in the simulated system.

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::thread::sleep;
use std::time::{Duration, Instant};

use tracing::{event, Level};

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
    ///   // one millisecond on the simulated machine.  Let the
    ///   // clock know so that our rate of simulated progress is
    ///   // forced to match the simulated clock rate.
    ///   let wait = clk.consume(&Duration::from_millis(1));
    ///   sleep(wait);
    /// }
    /// ```
    fn consume(&mut self, inteval: &Duration) -> Duration;

    /// Discard any accumulated surplus of ticks.  We might do this
    /// for example where the machine has gone into the _Limbo_ state
    /// where no sequence is runnable (i.e. progress cannot be made
    /// and the system clock is not the constraining factor).
    fn consume_all(&mut self);
}

/// BasicClock provides a simulated clock which runs slower or faster
/// than real time by a specified multiplier.
///
/// # Examples
/// ```
/// use std::time::Duration;
/// use cpu::BasicClock;
/// use cpu::Clock;
/// // `clk` tracks real time.
/// let mut clk = BasicClock::new(1.0);
/// ```
///
/// ```
/// use std::time::Duration;
/// use cpu::BasicClock;
/// // `clk_half` allows the caller to consume, on average, half a
/// // second of simulated clock time per actual second of elapsed
/// // time as measured by the host.   When the simulated clock time
/// // is not far enough ahead of real time to allow [`consume`] to
/// // complete without blocking, it will sleep for at least 6
/// // milliseconds of host time.
/// let mut clk_half = BasicClock::new(0.5);
/// ```
#[derive(Debug)]
pub struct BasicClock {
    /// The host time at which the clock started running.  At this
    /// time, the "real" time and the "simulated" time coincided.  We
    /// periodically move the origin in order to avoid subtracting
    /// pairs of nearly-equal large numbers (which risks loss of
    /// precision).
    origin: Instant,

    /// Elapsed time as measured by the simulated clock.
    simulator_elapsed: Duration,

    /// The duration "used up" by calls to [`SleepyClock::consume`].
    simulator_consumed: Duration,

    /// How much faster the simulated blocks runs compared to
    /// real-time.  A value of 1.0 means that we try to match
    /// real-time.  A value of 0.01 means that we try to run the
    /// simulated clock at 1/100 real-time (that is, the simulated
    /// machine will appear to be very slow).
    multiplier: f64,
}

#[derive(Debug)]
pub enum BadClockConfig {
    BadMultiplier(String),
}

impl Display for BadClockConfig {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BadClockConfig::BadMultiplier(msg) => write!(f, "bad clock multiplier: {}", msg),
        }
    }
}

impl Error for BadClockConfig {}

impl BasicClock {
    pub fn new(multiplier: f64) -> Result<BasicClock, BadClockConfig> {
        if multiplier < 0.0 {
            Err(BadClockConfig::BadMultiplier(format!(
                "negative multiplier {}",
                multiplier
            )))
        } else if multiplier < 1.0e-12 {
            Err(BadClockConfig::BadMultiplier(format!(
                "excessively tiny multiplier {}",
                multiplier
            )))
        } else {
            let zero_duration = Duration::new(0, 0);
            Ok(BasicClock {
                origin: Instant::now(),
                // Clocks initially coincide, so actual and simulated
                // elapsed time are both zero.
                simulator_elapsed: zero_duration,
                simulator_consumed: zero_duration,
                multiplier,
            })
        }
    }

    fn zero_duration() -> Duration {
        Duration::new(0, 0)
    }
}

impl Clock for BasicClock {
    fn now(&self) -> Duration {
        self.simulator_consumed
    }

    fn consume(&mut self, interval: &Duration) -> Duration {
        let deficit: Duration = match self.simulator_elapsed.checked_sub(self.simulator_consumed) {
            Some(surplus) if surplus > *interval => {
                self.simulator_consumed += *interval;
                Self::zero_duration()
            }
            Some(surplus) => {
                self.simulator_consumed += surplus;
                match interval.checked_sub(surplus) {
                    Some(deficit) => deficit,
                    // We do not expect overflow because the `surplus
                    // > interval` test failed above.
                    None => unreachable!(),
                }
            }
            None => {
                // `self.simulator_consumed > self.simulator_elapsed`,
                // which should not happen.
                *interval
            }
        };
        // deficit is measured in simulated clock time; convert it to
        // host time.
        deficit.div_f64(self.multiplier)
    }

    fn consume_all(&mut self) {
        self.origin = Instant::now();
        self.simulator_elapsed = Duration::new(0, 0);
        self.simulator_consumed = Duration::new(0, 0);
    }
}

#[derive(Debug)]
struct SignedDuration {
    negative: bool,
    magnitude: Duration,
}

impl SignedDuration {
    pub const ZERO: SignedDuration = SignedDuration {
        negative: false,
        magnitude: Duration::ZERO,
    };
}

impl From<Duration> for SignedDuration {
    fn from(magnitude: Duration) -> Self {
        Self {
            negative: false,
            magnitude,
        }
    }
}

impl SignedDuration {
    fn checked_sub(&self, d: Duration) -> Option<SignedDuration> {
        if self.negative {
            match self.magnitude.checked_add(d) {
                Some(result) => Some(SignedDuration {
                    negative: true,
                    magnitude: result,
                }),
                None => None, // actual overflow
            }
        } else {
            match self.magnitude.checked_sub(d) {
                Some(diff) => Some(SignedDuration {
                    negative: false,
                    magnitude: diff,
                }),
                None => match d.checked_sub(self.magnitude) {
                    Some(diff) => Some(SignedDuration {
                        negative: true,
                        magnitude: diff,
                    }),
                    None => {
                        panic!(
                            "checked_sub inconsistent for {:?} - {:?}",
                            self.magnitude, d
                        );
                    }
                },
            }
        }
    }

    fn checked_add(&self, d: Duration) -> Option<SignedDuration> {
        if self.negative {
            match d.checked_sub(self.magnitude) {
                Some(diff) => Some(SignedDuration {
                    negative: false,
                    magnitude: diff,
                }),
                None => match self.magnitude.checked_sub(d) {
                    Some(diff) => Some(SignedDuration {
                        negative: true,
                        magnitude: diff,
                    }),
                    None => {
                        panic!(
                            "checked_add inconsistent for {:?} - {:?}",
                            self.magnitude, d
                        );
                    }
                },
            }
        } else {
            match self.magnitude.checked_add(d) {
                Some(tot) => Some(SignedDuration {
                    negative: false,
                    magnitude: tot,
                }),
                None => None, // actual overflow
            }
        }
    }
}

/// MinimalSleeper provides a facility for periodically sleeping such
/// that on average we sleep for the requested amount of time, even
/// though we don't necessarily sleep on every call.  The idea is to
/// be efficient in the use of system calls.
///
/// # Examples
/// ```
/// use std::time::Duration;
/// use cpu::MinimalSleeper;
/// // `s` will try to sleep, on average, for the indicated amounts
/// // of time, but will never sleep for less than 1 millisecond.
/// let mut s = MinimalSleeper::new(Duration::from_millis(10));
/// ```
#[derive(Debug)]
pub struct MinimalSleeper {
    /// Minimum period for which we will try to sleep.
    min_sleep: Duration,

    sleep_owed: SignedDuration,

    total_cumulative_sleep: Duration,
}

impl MinimalSleeper {
    pub fn new(min_sleep: Duration) -> MinimalSleeper {
        MinimalSleeper {
            min_sleep,
            sleep_owed: SignedDuration::ZERO,
            total_cumulative_sleep: Duration::ZERO,
        }
    }

    fn really_sleep(&mut self) {
        match self.sleep_owed {
            SignedDuration {
                negative: false,
                magnitude,
            } => {
                let then = Instant::now();
                event!(Level::DEBUG, "Sleeping for {:?}...", self.sleep_owed);
                sleep(magnitude);
                self.total_cumulative_sleep += magnitude;
                let now = Instant::now();
                let slept_for = now - then;
                event!(
                    Level::TRACE,
                    "MinimalSleeper: owed sleep is {:?}, actually slept for {:?}",
                    self.sleep_owed,
                    slept_for
                );
                match self.sleep_owed.checked_sub(slept_for) {
                    Some(remainder) => {
                        self.sleep_owed = remainder;
                    }
                    None => {
                        panic!("MinimalSleeper::really_sleep: overflow in sleep_owed");
                    }
                }
            }
            _ => unreachable!(), // should not have been called.
        }
        event!(
            Level::DEBUG,
            "MinimalSleeper: updated sleep debt is {:?}...",
            self.sleep_owed
        );
    }

    pub fn sleep(&mut self, duration: &Duration) {
        match self.sleep_owed.checked_add(*duration) {
            Some(more) => {
                self.sleep_owed = more;
                match self.sleep_owed {
                    SignedDuration {
                        negative: false,
                        magnitude,
                    } if magnitude > self.min_sleep => self.really_sleep(),
                    _ => {
                        // We did not build up enough sleep debt to exceed the
                        // threshold, or our sleep debt is negative.  Wait for
                        // more calls to sleep to bring us over the threshold.
                    }
                }
            }
            None => {
                panic!("MinimalSleeper::really_sleep: overflow in sleep_owed");
            }
        }
    }
}

impl Drop for MinimalSleeper {
    fn drop(&mut self) {
        event!(
            Level::INFO,
            "MinimalSleeper: drop: total cumulative sleep is {:?}",
            self.total_cumulative_sleep
        );
    }
}
