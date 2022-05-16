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
//! tape.  On start, reading begins immediately at full speed, and on
//! stop, the tape movement stops immediately.  This will likely
//! change in the future.
use base::prelude::*;
use std::cmp;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::File;
use std::io::Read;
use std::time::Duration;

use tracing::{event, Level};

use super::*;
use crate::io::{TransferFailed, Unit, UnitStatus};

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
    tape_pos: usize,
    tapes: Box<dyn TapeIterator>,
    data: Option<u8>,
    already_warned_eof: bool,
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
            .field("tape_pos", &self.tape_pos)
            .field("data", &self.data)
            .field("already_warned_eof", &self.already_warned_eof)
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
            tape_pos: 0,
            tapes,
            data: None,
            already_warned_eof: false,
            read_failed: false,
            overrun: false,
            time_of_next_read: None,
            rewind_line_counter: 0,
            mode: Unsigned12Bit::ZERO,
        }
    }

    fn close_data_file(&mut self) {
        self.data_file = None;
        self.tape_pos = 0;
    }

    fn open_data_file(&mut self) {
        if self.data_file.is_some() {
            return; // already open
        }
        self.tape_pos = 0;
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
                event!(Level::INFO, "reached the end mark, reversing direction");
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
        let mut buf: [u8; 1] = [0o377]; // deliberately > Unsigned6Bit::MAX.
        match self.data_file.as_mut() {
            Some(f) => match f.read(&mut buf) {
                Err(_) => {
                    self.read_failed = true;
                    self.overrun = false;
                    self.data = None;
                    self.time_of_next_read = None;
                }
                Ok(0) => {
                    // At EOF.  We don't stop the motor, but if the
                    // real PETR device can detect when the whole tape
                    // has already passed through, perhaps we should.
                    if self.already_warned_eof {
                        event!(
                            Level::DEBUG,
                            "reading again at end-of-file at position {}",
                            self.tape_pos
                        );
                    } else {
                        self.already_warned_eof = true;
                        event!(
                            Level::WARN,
                            "end-of-file on tape input file at position {}",
                            self.tape_pos
                        );
                    }
                    self.time_of_next_read = None;
                }
                Ok(read_len) => {
                    match read_len {
                        0 => unreachable!(),
                        1 => event!(
                            Level::DEBUG,
                            "read 1 byte: {:04o} at file position {}",
                            buf[0],
                            self.tape_pos
                        ),
                        n => event!(
                            Level::DEBUG,
                            "read {} bytes at file position {}: {:?}",
                            n,
                            self.tape_pos,
                            &buf
                        ),
                    }
                    self.already_warned_eof = false;
                    if !self.overrun {
                        self.overrun = self.data.is_some();
                        if self.overrun {
                            event!(Level::WARN, "input overrun");
                        }
                    }
                    self.data = Some(buf[0]);
                    self.tape_pos += read_len;
                }
            },
            None => {
                // There is no tape.
                event!(Level::TRACE, "paper tape: there is no tape");
                self.data = None;
                self.activity = Activity::Stopped;
                self.time_of_next_read = None;
            }
        }
    }

    fn maybe_simulate_event(&mut self, system_time: &Duration) {
        event!(
            Level::TRACE,
            "maybe_simulate_event: activity={:?}",
            &self.activity
        );
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
                self.time_of_next_read = None;
            }
        }
    }

    fn transfer_mode(&self) -> TransferMode {
        if self.mode & 0o02 != 0 {
            TransferMode::Assembly
        } else {
            TransferMode::Exchange
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
        self.mode = mode;
        let transfer_mode_name = match self.transfer_mode() {
            TransferMode::Assembly => "assembly",
            TransferMode::Exchange => "exchange",
        };
        event!(
            Level::INFO,
            "PETR connected; motor {}, direction {}; {} mode {:o}",
            self.activity,
            self.direction,
            transfer_mode_name,
            self.mode,
        );
    }

    fn transfer_mode(&self) -> TransferMode {
        self.transfer_mode()
    }

    fn read(&mut self, system_time: &Duration) -> Result<MaskedWord, TransferFailed> {
        match self.data.take() {
            None => {
                event!(Level::DEBUG, "no data is ready yet");
                Err(TransferFailed::BufferNotFree)
            }
            Some(byte) => {
                // This calculation of time_of_next_read is not right,
                // as the interval is between physical paper-tape
                // lines, not between I/O instrucitons.
                self.time_of_next_read = Some(next_line_time(self.direction, system_time));
                event!(Level::DEBUG, "read value {:03o}", byte & 0o77);
                Ok(MaskedWord {
                    bits: Unsigned36Bit::from(byte & 0o77),
                    mask: u36!(0o77),
                })
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

    fn disconnect(&mut self, _system_time: &Duration) {
        self.activity = Activity::Stopped;
    }
}
