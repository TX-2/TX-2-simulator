//! Photoelectric Paper tape reader, unit 52
//!
//! The paper tape reader has 7 channels.
//!
//! Tape movement can occur in either of two directions, in the bin
//! direction and in the reel direction.  Tape reads occur in the
//! "reel" direction.  The modes of operation of the motor in the
//! "bin" direction both stop and reverse direction when the END MARK
//! is detected.  In other words, this is analogous to rewinding to the
//! beginning-of-file in preparation for reading the file.
//!
//! The reader can read both strip tape and reel tape, and does so at
//! different speeds (because of the different levels of rubustness of
//! the two types of tape), but we operate as if all tapes are read
//! at the same speed.
//!
//! We do not currently simulate acceleration/deceleration of the
//! tape.  On start, reading beings immediately at full speed, and on
//! stop, the tape movement stops immediately.  This will likely
//! change in the future.
use base::prelude::*;
use base::subword;
use std::cmp;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::File;
use std::io::Read;
use std::ops::Shl;
use std::time::Duration;

use tracing::{event, Level};

use crate::io::{FlagChange, TransferFailed, Unit, UnitStatus};

/// Is the tape motor running?
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Activity {
    Stopped,
    Started,
}

impl Display for Activity {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            Activity::Stopped => "stopped",
            Activity::Started => "running",
        })
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Direction {
    // Capstan drive is running in the bin direction (as in
    // immediately after IOS 30104, before END MARK has been read).
    Bin,

    // Capstan drive is running in the reel direction (as in after IOS
    // 30104, after END MARK has been read).
    Reel,
}

impl Display for Direction {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            Direction::Bin => "bin",
            Direction::Reel => "reel",
        })
    }
}

fn next_line_time(direction: Direction, system_time: &Duration) -> Duration {
    // The reader reads at between 400 and 2500 lines per second.
    //
    // We don't want to avoidably generate missing data alarms, so
    // for now, we simulate data reading at the slowest speed and
    // non-reading tape movements at the highest speed.
    *system_time
        + match direction {
            Direction::Bin => {
                // At 2500 lines per second, the interval between
                // lines is 1s / 2500 = 400 microseconds.
                Duration::from_micros(2500)
            }
            Direction::Reel => {
                // At 400 lines per second, the interval between lines
                // is 1s / 400 = 2500 microseconds.
                Duration::from_micros(400)
            }
        }
}

pub trait TapeIterator {
    fn next_tape(&mut self) -> Option<File>;
}

pub struct Petr {
    // Activity and direction cannot just be left encoded in mode,
    // because we need to be able to start/stop the motor and change
    // direction without changing the mode value (since the programmer
    // controls that).
    activity: Activity,
    direction: Direction,
    data_file: Option<File>,
    tapes: Box<dyn TapeIterator>,
    data: Option<u8>,
    read_failed: bool,
    overrun: bool,
    time_of_next_read: Option<Duration>,
    rewind_line_counter: usize,
    mode: Unsigned12Bit,
}

impl Debug for Petr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Petr")
            .field("activity", &self.activity)
            .field("direction", &self.direction)
            .field("data_file", &self.data_file)
            .field("data", &self.data)
            .field("read_failed", &self.read_failed)
            .field("overrun", &self.overrun)
            .field("time_of_next_read", &self.time_of_next_read)
            .field("rewind_line_counter", &self.rewind_line_counter)
            .field("mode", &self.mode)
            .finish_non_exhaustive()
    }
}

impl Petr {
    pub fn new(tapes: Box<dyn TapeIterator>) -> Petr {
        Petr {
            activity: Activity::Stopped,
            direction: Direction::Bin,
            data_file: None,
            tapes,
            data: None,
            read_failed: false,
            overrun: false,
            time_of_next_read: None,
            rewind_line_counter: 0,
            mode: Unsigned12Bit::ZERO,
        }
    }

    fn close_data_file(&mut self) {
        self.data_file = None;
    }

    fn open_data_file(&mut self) {
        if self.data_file.is_some() {
            return; // already open
        }
        self.data_file = self.tapes.next_tape();
    }

    fn next_poll_time(&mut self, system_time: &Duration) -> Duration {
        match self.time_of_next_read {
            Some(t) => cmp::max(t, *system_time),
            None => Duration::from_secs(1),
        }
    }

    fn do_rewind(&mut self) {
        match self.rewind_line_counter.checked_sub(1) {
            None | Some(0) => {
                // We reached - or were already at - the END MARK,
                // reverse direction.
                event!(Level::INFO, "reached the end mark");
                assert!(self.direction == Direction::Bin);
                self.direction = Direction::Reel;
            }
            Some(reduced_by_1) => {
                self.rewind_line_counter = reduced_by_1;
                event!(
                    Level::DEBUG,
                    "rewound over a line: {} more to go",
                    self.rewind_line_counter
                );
            }
        }
    }

    fn do_read(&mut self) {
        // A line of the simulated tape should have appeared under the
        // read head.
        let mut buf: [u8; 1] = [0];
        match self.data_file.as_mut() {
            Some(f) => match f.read(&mut buf) {
                Err(_) => {
                    self.read_failed = true;
                    self.overrun = false;
                    self.data = None;
                }
                Ok(0) => {
                    // At EOF.  We don't stop the motor, but if the
                    // real PETR device can detect when the whole tape
                    // has already passed through, perhaps we should.
                    self.data = None;
                }
                Ok(_) => {
                    self.overrun = self.data.is_some();
                    self.data = Some(buf[0]);
                }
            },
            None => {
                // There is no tape.
                self.data = None;
                self.activity = Activity::Stopped;
                self.time_of_next_read = None;
            }
        }
    }

    fn maybe_simulate_event(&mut self, system_time: &Duration) {
        match self.activity {
            Activity::Started => {
                if let Some(t) = self.time_of_next_read {
                    if t > *system_time {
                        // The next line has not yet appeared under the read
                        // head.
                        let to_wait = || t - *system_time;
                        event!(
                            Level::TRACE,
                            "motor running ({}) but next line will not be read for {:?} yet",
                            self.direction,
                            to_wait()
                        );
                        return;
                    }
                }
                match self.direction {
                    Direction::Bin => {
                        event!(Level::TRACE, "motor running, doing rewind action");
                        self.do_rewind()
                    }
                    Direction::Reel => {
                        event!(Level::TRACE, "motor running, doing read action");
                        self.do_read()
                    }
                }
                // do_read may have stopped the motor, so take account
                // of that.
                self.time_of_next_read = match self.activity {
                    Activity::Started => Some(next_line_time(self.direction, system_time)),
                    Activity::Stopped => None,
                }
            }
            Activity::Stopped => {
                // The motor is not running.  So no events (of lines
                // passing under the photodetector) will happen.
                event!(Level::TRACE, "motor stopped, nothing more to simulate");
            }
        }
    }
}

impl Unit for Petr {
    fn poll(&mut self, system_time: &Duration) -> UnitStatus {
        self.maybe_simulate_event(system_time);
        let data_ready: bool = self.data.is_some();

        UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag: if data_ready {
                Some(FlagChange::Raise)
            } else {
                None
            },
            buffer_available_to_cpu: data_ready,
            inability: self.read_failed,
            missed_data: self.overrun,
            mode: self.mode,
            poll_after: self.next_poll_time(system_time),
            is_input_unit: true,
        }
    }

    fn connect(&mut self, system_time: &Duration, mode: Unsigned12Bit) {
        self.direction = if mode & 0o04 != 0 {
            Direction::Bin
        } else {
            Direction::Reel
        };
        self.activity = if mode & 0o100 != 0 {
            self.open_data_file();
            self.time_of_next_read = Some(next_line_time(self.direction, system_time));
            Activity::Started
        } else {
            // While the motor is not running, no data will arrive.
            self.close_data_file();
            self.time_of_next_read = None;
            Activity::Stopped
        };
        self.mode = mode; // encodes Assembly/Normal
        event!(
            Level::INFO,
            "PETR connected; motor {}, direction {}; mode {:o}",
            self.activity,
            self.direction,
            self.mode,
        );
    }

    fn read(
        &mut self,
        system_time: &Duration,
        target: &mut Unsigned36Bit,
    ) -> Result<(), TransferFailed> {
        match self.data {
            None => Err(TransferFailed::BufferNotFree),
            Some(byte) => {
                self.time_of_next_read = Some(next_line_time(self.direction, system_time));
                let value_read = Unsigned6Bit::try_from(byte & 0o77).unwrap();
                let assemby_mode: bool = self.mode & 0o02 != 0;
                if assemby_mode {
                    // The data goes into the following bit positions:
                    // bit 1 (0 counting from 0) goes to 1.1 = 1 <<  0 (dec)
                    // bit 2 (1 counting from 0) goes to 1.7 = 1 <<  6 (dec)
                    // bit 3 (2 counting from 0) goes to 2.4 = 1 << 12 (dec)
                    // bit 4 (3 counting from 0) goes to 3.1 = 1 << 18 (dec)
                    // bit 5 (4 counting from 0) goes to 3.7 = 1 << 24 (dec)
                    // bit 6 (5 counting from 0) goes to 4.4 = 1 << 30 (dec)
                    let mut updated = target.shl(1);
                    for srcbit in 0_u8..=5_u8 {
                        let destbit: u32 = (srcbit * 6).into();
                        updated = updated & !(Unsigned36Bit::ONE.shl(destbit))
                            | (Unsigned36Bit::from(value_read) & 1 << srcbit).shl(destbit);
                    }
                    *target = updated;
                    Ok(())
                } else {
                    let (left, right) = subword::split_halves(*target);
                    let (q2, _) = subword::split_halfword(right);
                    let right = subword::join_quarters(q2, Unsigned9Bit::from(value_read));
                    *target = subword::join_halves(left, right);
                    Ok(())
                }
            }
        }
    }

    fn write(
        &mut self,
        _system_time: &Duration,
        _source: Unsigned36Bit,
    ) -> Result<(), TransferFailed> {
        unreachable!()
    }

    fn name(&self) -> String {
        "PETR photoelectric paper tape reader".to_string()
    }
}
