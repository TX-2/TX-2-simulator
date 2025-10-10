//! This module manages the context in which the emulator is performing a single operation.
//!
//! In general, a function call into the emulator represents an
//! opportunity to execute an instruction or to emulatge a state
//! change for a peripheral.
//!
//! The emulator is most concerned with keeping track of hoe much time
//! would have elapsed for the TX-2 machine it is emulating.  This
//! allows is to know, for example, when the Lincoln Writer would have
//! finished printing a character, when the next value from the paper
//! tape reader would be ready and so on.  But the caller also keeps
//! track of the actual elapsed time.
//!
//! In order to avoid confusion between these related quantities of
//! the same type, we keep them together in a struct so that we can
//! give them very clear names.
use core::time::Duration;

#[derive(Debug)]
pub struct Context {
    pub simulated_time: Duration,
    pub real_elapsed_time: Duration,
}

impl Context {
    #[must_use]
    pub fn new(simulated_time: Duration, real_elapsed_time: Duration) -> Context {
        Context {
            simulated_time,
            real_elapsed_time,
        }
    }
}
