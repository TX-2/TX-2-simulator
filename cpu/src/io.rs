//! This module simulates the CPU behaviours which relate to I/O
//! devices (connect/disconnect, the ways the IOS and TSD instructions
//! with devices).
//!
//! ## Report Word
//!
//! The Report word of I/O units looks like this:
//!
//! | Special - Mag tape | Sequence Number | Flag  | Avail | Maint  | Connected |  EIA  | MISIND |    Mode |
//! | ------------------ | --------------- | ----- | ----- | -----  | --------- | ----- | ------ | ------- |
//! | 3.7-4.9            | 3.1-3.6         | 2.9   | 2.8   | 2.7    | 2.6       | 2.5   | 2.4    | 1.1-2.3 |
//! | (12 bits)          | (6 bits)        |(1 bit)|(1 bit)|(1 bit )| (1 bit)   |(1 bit)|(1 bit) |(12 bits)|
//!
//!
//! ## Sequence Number Assignments
//! 0: Sequence which is run to start the computer (e.g. when "CODABO"
//! or "START OVER" is pressed).
//!
//! 41: Handles various I/O alarm conditions.
//! 42: Handles various trap conditions (see Users Handbook page 42).
//! 47: Handles miscellaneous inputs
//! 50: DATRAC (A/D converter)
//! 51: Xerox printer
//! 52: PETR (paper tape reader)
//! 54: Interval timer
//! 55: Light pen
//! 60: Oscilloscope display
//! 61: RNG
//! 63: Punch
//! 65: Lincoln Writer input
//! 66: Lincoln Writer output
//! 71: Lincoln Writer input
//! 72: Lincoln Writer output
//! 75: Misc output
//! 76: Not for physical devices.
//! 77: Not for physical devices.
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Formatter};
use std::ops::Shl;
use std::time::Duration;

use tracing::{event, span, Level};

use super::types::*;
use crate::alarm::{Alarm, AlarmUnit};
use crate::Clock;
use base::prelude::*;

mod dev_lincoln_writer;
mod dev_petr;
mod pollq;

use dev_lincoln_writer::LincolnWriterOutput;
pub use dev_petr::{Petr, TapeIterator};
use pollq::PollQueue;

/// When set, indicates that the controlling sequence has missed a data item.
pub const IO_MASK_MISIND: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_010_000);

/// When set, indicates the unit is (already) connected.
pub const IO_MASK_CONNECTED: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_040_000);

/// When set, indicates that the unit is in maintenance mode (i.e. is not available)
pub const IO_MASK_MAINT: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_100_000);

/// When set, indicates that the unit's buffer is available for use (read or write)
/// by the CPU.
pub const IO_MASK_AVAIL: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_200_000);

/// When set, indicates that the unit wants attention.  That is, is ready for a
/// TSD instruction or has just been connected.
pub const IO_MASK_FLAG: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_400_000);

/// Units report their status (which is used to construct their report
/// word) with this struct.
#[derive(Debug)]
pub struct UnitStatus {
    pub special: Unsigned12Bit,
    pub change_flag: Option<FlagChange>,
    pub buffer_available_to_cpu: bool,
    pub inability: bool,
    pub missed_data: bool,
    pub mode: Unsigned12Bit,

    /// Indicates that the unit wishes to be polled for its status
    /// before the indicated (simulated) duration has elapsed.
    pub poll_after: Duration,

    /// True for units which are input units.  Some devices (Lincoln
    /// Writers for example) occupy two units, one for read (input)o
    /// and the other for write (output).
    pub is_input_unit: bool,
}

fn make_unit_report_word(
    unit: Unsigned6Bit,
    is_connected: bool,
    is_maint: bool,
    current_flag: bool,
    status: &UnitStatus,
) -> Unsigned36Bit {
    let mut report: Unsigned36Bit = Unsigned36Bit::from(status.mode);
    if status.missed_data {
        report = report | IO_MASK_MISIND;
    }
    if is_connected {
        report = report | IO_MASK_CONNECTED;
    }
    if is_maint {
        report = report | IO_MASK_MAINT;
    }
    if status.buffer_available_to_cpu {
        report = report | IO_MASK_AVAIL;
    }
    // A unit can raise but not lower its flag.
    if current_flag || status.change_flag == Some(FlagChange::Raise) {
        report = report | IO_MASK_FLAG;
    }
    report | Unsigned36Bit::from(unit).shl(18) | Unsigned36Bit::from(status.special).shl(24)
}

fn make_report_word_for_invalid_unit(unit: Unsigned6Bit, current_flag: bool) -> Unsigned36Bit {
    make_unit_report_word(
        unit,
        false, // not connected
        true,  // in maintenance
        current_flag,
        &UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag: None,
            buffer_available_to_cpu: false,
            inability: true,
            missed_data: false,
            mode: Unsigned12Bit::ZERO,
            poll_after: Duration::from_secs(10),
            is_input_unit: false,
        },
    )
}

pub trait Unit {
    fn poll(&mut self, system_time: &Duration) -> UnitStatus;
    fn connect(&mut self, system_time: &Duration, mode: Unsigned12Bit);
    fn disconnect(&mut self, system_time: &Duration);
    fn transfer_mode(&self) -> TransferMode;
    fn read(&mut self, system_time: &Duration) -> Result<MaskedWord, TransferFailed>;
    fn write(
        &mut self,
        system_time: &Duration,
        source: Unsigned36Bit,
    ) -> Result<(), TransferFailed>;
    fn name(&self) -> String;
}

pub struct AttachedUnit {
    inner: RefCell<Box<dyn Unit>>,

    /// True for units which are input units.  Some devices (Lincoln
    /// Writers for example) occupy two units, one for read (input)
    /// and the other for write (output).
    pub is_input_unit: bool,

    pub connected: bool,
    pub in_maintenance: bool,
}

impl AttachedUnit {
    fn is_disconnected_output_unit(&self) -> bool {
        (!self.is_input_unit) && (!self.connected)
    }

    pub fn poll(&self, system_time: &Duration) -> UnitStatus {
        self.inner.borrow_mut().poll(system_time)
    }

    pub fn connect(&self, system_time: &Duration, mode: Unsigned12Bit) {
        self.inner.borrow_mut().connect(system_time, mode)
    }

    pub fn disconnect(&self, system_time: &Duration) {
        self.inner.borrow_mut().disconnect(system_time)
    }

    pub fn transfer_mode(&self) -> TransferMode {
        self.inner.borrow().transfer_mode()
    }

    pub fn read(&self, system_time: &Duration) -> Result<MaskedWord, TransferFailed> {
        self.inner.borrow_mut().read(system_time)
    }

    pub fn write(
        &mut self,
        system_time: &Duration,
        source: Unsigned36Bit,
    ) -> Result<(), TransferFailed> {
        self.inner.borrow_mut().write(system_time, source)
    }

    pub fn name(&self) -> String {
        self.inner.borrow().name()
    }
}

impl Debug for AttachedUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("AttachedUnit")
            .field("inner", &format_args!("<unit: {}>", self.name()))
            .field("is_input_unit", &self.is_input_unit)
            .field("connected", &self.connected)
            .field("in_maintenance", &self.in_maintenance)
            .finish()
    }
}

// TODO: actually delete this
//#[derive(Debug)]
//enum DeviceType {
//    Input { in_maintenance: bool },
//    Output { in_maintenance: bool },
//    Nonexistent,
//    AttachedButNotConnected,
//}

/// Manages a collection of devices.  Does not actually correspond to
/// a tangible physical component of the TX-2 system.
#[derive(Debug)]
pub struct DeviceManager {
    devices: BTreeMap<Unsigned6Bit, AttachedUnit>,
    poll_queue: PollQueue,
}

impl DeviceManager {
    pub fn new() -> DeviceManager {
        DeviceManager {
            devices: BTreeMap::new(),
            poll_queue: PollQueue::new(),
        }
    }

    pub fn get(&self, unit_number: &Unsigned6Bit) -> Option<&AttachedUnit> {
        self.devices.get(unit_number)
    }

    pub fn get_mut(&mut self, unit_number: &Unsigned6Bit) -> Option<&mut AttachedUnit> {
        self.devices.get_mut(unit_number)
    }

    pub fn update_poll_time(&mut self, seq: SequenceNumber, when: Duration) {
        if self.poll_queue.update(seq, when).is_err() {
            // This happens when we complete an IOS or TSD
            // instruction from a sequence that has no attached
            // hardware.  For example software-only sequences such
            // as 0o0, 0o76 or 0o77.  It's harmless.
        }
    }

    // TODO: actually delete this
    //fn get_type(&self, unit_number: Unsigned6Bit) -> DeviceType {
    //    match self.devices.get(&unit_number) {
    //        Some(attached) => {
    //            if attached.is_input_unit {
    //                DeviceType::Input {
    //                    in_maintenance: attached.in_maintenance,
    //                }
    //            } else {
    //                DeviceType::Output {
    //                    in_maintenance: attached.in_maintenance,
    //                }
    //            }
    //        }
    //        None => DeviceType::Nonexistent,
    //    }
    //}

    pub fn attach(
        &mut self,
        system_time: &Duration,
        unit_number: Unsigned6Bit,
        in_maintenance: bool,
        mut unit: Box<dyn Unit>,
    ) {
        let status: UnitStatus = unit.poll(system_time);
        self.devices.insert(
            unit_number,
            AttachedUnit {
                inner: RefCell::new(unit),
                is_input_unit: status.is_input_unit,
                connected: false,
                in_maintenance,
            },
        );
        self.poll_queue.push(unit_number, status.poll_after);
    }

    pub fn report(
        &mut self,
        system_time: &Duration,
        unit: Unsigned6Bit,
        current_flag: bool,
        alarm_unit: &AlarmUnit,
    ) -> Result<Unsigned36Bit, Alarm> {
        match self.devices.get_mut(&unit) {
            Some(attached) => {
                // Because the unit report word contains a `Connect`
                // (2.6) and `Maintenance` bit (2.7) we need to be
                // able to collect status from a unit which is
                // attached but not otherwise usable.
                let unit_status = attached.poll(system_time);
                self.poll_queue.push(unit, unit_status.poll_after);
                Ok(make_unit_report_word(
                    unit,
                    attached.connected,
                    attached.in_maintenance,
                    current_flag,
                    &unit_status,
                ))
            }
            None => {
                alarm_unit.fire_if_not_masked(Alarm::IOSAL {
                    unit,
                    operand: None,
                    message: format!("unit {} is not known", unit),
                })?;
                // IOSAL is masked.
                Ok(make_report_word_for_invalid_unit(unit, current_flag))
            }
        }
    }

    pub fn poll(&mut self, system_time: &Duration) -> (u64, Option<Alarm>, Option<Duration>) {
        let mut raised_flags: u64 = 0;
        let mut alarm: Option<Alarm> = None;
        let mut next_poll: Option<Duration> = None;

        loop {
            match self.poll_queue.peek() {
                None => {
                    break;
                }
                Some((_, poll_time)) => {
                    if poll_time > system_time {
                        // Next poll action is not due yet.
                        event!(
                            Level::TRACE,
                            "poll: next poll is not due yet; due={:?}, now={:?}",
                            poll_time,
                            system_time
                        );
                        next_poll = Some(*poll_time);
                        break;
                    }
                }
            }
            match self.poll_queue.pop() {
                None => unreachable!(),
                Some((devno, poll_time)) => {
                    let span = span!(Level::ERROR, "poll", unit=%devno);
                    let _enter = span.enter();

                    event!(
                        Level::TRACE,
                        "poll: next poll is now due; due={:?}, now={:?}",
                        poll_time,
                        system_time
                    );
                    assert!(poll_time <= *system_time);

                    let attached = match self.devices.get_mut(&devno) {
                        Some(attached) => attached,
                        None => {
                            event!(
				Level::ERROR,
				"Device {:?} is present in the polling queue but not in the device map; ignoring it",
				devno
			    );
                            continue;
                        }
                    };
                    if !attached.connected {
                        event!(Level::TRACE, "not polling unit. it's not connected");
                        continue;
                    }
                    assert!(!attached.in_maintenance); // cannot connect in-maint devices.
                    event!(
                        Level::TRACE,
                        "polling unit at system time {:?}",
                        system_time
                    );
                    let unit_status = attached.poll(system_time);
                    event!(Level::TRACE, "unit status is {:?}", unit_status);
                    self.poll_queue.push(devno, unit_status.poll_after);
                    if let Some(FlagChange::Raise) = unit_status.change_flag {
                        event!(Level::TRACE, "unit has raised its flag");
                        raised_flags |= 1 << u8::from(devno);
                    }
                    if alarm.is_none() {
                        // TODO: support masking for alarms (hardware and
                        // software masking are both available; either should
                        // be able to mask it).
                        if unit_status.inability {
                            alarm = Some(Alarm::IOSAL {
                                unit: devno,
                                operand: None,
                                message: format!("unit {} reports inability (EIA)", devno),
                            });
                        } else if unit_status.missed_data {
                            alarm = Some(Alarm::MISAL { unit: devno });
                        }
                    }
                }
            }
        }
        (raised_flags, alarm, next_poll)
    }

    pub fn disconnect_all(&mut self, system_time: &Duration) {
        for (_, attached) in self.devices.iter_mut() {
            if attached.connected {
                attached.disconnect(system_time);
                attached.connected = false;
            }
        }
    }

    pub fn disconnect(
        &mut self,
        device: &Unsigned6Bit,
        alarm_unit: &AlarmUnit,
    ) -> Result<(), Alarm> {
        if *device == u6!(0o42) {
            return Ok(());
        }
        match self.devices.get_mut(device) {
            Some(attached) => {
                attached.connected = false;
                Ok(())
            }
            None => {
                alarm_unit.fire_if_not_masked(Alarm::IOSAL {
                    unit: *device,
                    operand: None,
                    message: format!("Attempt to disconnect missing unit {}", device),
                })?;
                Ok(()) // IOSAL is masked, carry on.
            }
        }
    }

    pub fn connect(
        &mut self,
        system_time: &Duration,
        device: &Unsigned6Bit,
        mode: Unsigned12Bit,
        alarm_unit: &AlarmUnit,
    ) -> Result<Option<FlagChange>, Alarm> {
        match self.devices.get_mut(device) {
            Some(attached) => {
                if attached.in_maintenance {
                    Err(Alarm::IOSAL {
                        unit: *device,
                        operand: None,
                        message: format!("Attempt to connect in-maint unit {}", device),
                    })
                } else {
                    let flag_change = if attached.is_disconnected_output_unit() {
                        Some(FlagChange::Raise)
                    } else {
                        None
                    };
                    attached.connect(system_time, mode);
                    attached.connected = true;
                    Ok(flag_change)
                }
            }
            None => {
                alarm_unit.fire_if_not_masked(Alarm::IOSAL {
                    unit: *device,
                    operand: None,
                    message: format!("Attempt to connect missing unit {}", device),
                })?;
                Ok(None) // IOSAL is masked, carry on
            }
        }
    }
}

impl Default for DeviceManager {
    /// We're implementing this mainly to keep clippy happy.
    fn default() -> DeviceManager {
        Self::new()
    }
}

pub fn set_up_peripherals<C: Clock>(
    devices: &mut DeviceManager,
    clock: &C,
    tapes: Box<dyn TapeIterator>,
) {
    let now = clock.now();
    fn attach_lw_output(unit: Unsigned6Bit, now: &Duration, devices: &mut DeviceManager) {
        devices.attach(now, unit, false, Box::new(LincolnWriterOutput::new(unit)));
    }

    devices.attach(&now, u6!(0o52_u8), false, Box::new(Petr::new(tapes)));
    attach_lw_output(u6!(0o66), &now, devices);
}
