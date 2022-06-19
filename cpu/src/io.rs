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
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Shl;
use std::time::Duration;

use serde::Serialize;
use tracing::{event, span, Level};

use super::types::*;
use crate::alarm::{Alarm, Alarmer};
use crate::alarmunit::AlarmUnit;
use crate::context::Context;
use crate::event::*;
use crate::PETR;
use base::prelude::*;

mod dev_lincoln_writer;
mod dev_petr;
mod pollq;

use dev_lincoln_writer::LincolnWriterOutput;
pub use dev_petr::Petr;
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

#[derive(Debug)]
pub enum TransferFailed {
    BufferNotFree,
    Alarm(Alarm),
}

impl Display for TransferFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            TransferFailed::BufferNotFree => {
                f.write_str("Unit buffer not available for use by the CPU")
            }
            TransferFailed::Alarm(alarm) => write!(f, "{}", alarm),
        }
    }
}

impl std::error::Error for TransferFailed {}

/// Units report their status (which is used to construct their report
/// word) with this struct.
#[derive(Debug, Serialize)]
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

#[derive(Debug, Serialize)]
pub struct ExtendedConnectedUnitStatus {
    pub buffer_available_to_cpu: bool,
    pub inability: bool,
    pub missed_data: bool,
    pub special: u16,
    pub mode: u16,
}

#[derive(Debug, Serialize)]
pub struct ExtendedUnitState {
    pub flag: bool,
    pub connected: bool,
    pub in_maintenance: bool,
    pub name: String,
    pub text_info: String,
    /// status is None for units which are attached but not currently
    /// connected.
    pub status: Option<ExtendedConnectedUnitStatus>,
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
    fn poll(&mut self, ctx: &Context) -> UnitStatus;
    /// Provide a text summary of the state of the device.
    fn text_info(&self, ctx: &Context) -> String;
    fn connect(&mut self, ctx: &Context, mode: Unsigned12Bit);
    fn disconnect(&mut self, ctx: &Context);
    fn transfer_mode(&self) -> TransferMode;
    /// Handle a TSD on an input channel.
    fn read(&mut self, ctx: &Context) -> Result<MaskedWord, TransferFailed>;
    /// Handle a TSD on an output channel.
    fn write(
        &mut self,
        ctx: &Context,
        source: Unsigned36Bit,
    ) -> Result<Option<OutputEvent>, TransferFailed>;
    fn name(&self) -> String;
    fn on_input_event(&mut self, ctx: &Context, event: InputEvent);
}

pub struct AttachedUnit {
    inner: RefCell<Box<dyn Unit>>,

    unit: Unsigned6Bit,

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

    fn call_inner<A, F, T>(&self, what: &str, alarmer: &mut A, f: F) -> Result<T, Alarm>
    where
        A: Alarmer,
        F: Fn(&dyn Unit) -> T,
    {
        if self.connected {
            let output = f(self.inner.borrow().as_ref());
            Ok(output)
        } else {
            Err(alarmer.always_fire(Alarm::BUGAL {
                instr: None,
                message: format!(
                    "attempt read-only use (for {}) of disconnected unit {:o}",
                    what, self.unit
                ),
            }))
        }
    }

    fn call_mut_inner<A, F, T>(&self, what: &str, alarmer: &mut A, mut f: F) -> Result<T, Alarm>
    where
        A: Alarmer,
        F: FnMut(&mut dyn Unit) -> T,
    {
        if self.connected {
            let output = f(self.inner.borrow_mut().as_mut());
            Ok(output)
        } else {
            Err(alarmer.always_fire(Alarm::BUGAL {
                instr: None,
                message: format!(
                    "attempt read-write use (for {}) of disconnected unit {:o}",
                    what, self.unit
                ),
            }))
        }
    }

    pub fn poll<A: Alarmer>(&self, ctx: &Context, _alarmer: &mut A) -> Result<UnitStatus, Alarm> {
        Ok(self.inner.borrow_mut().poll(ctx))
    }

    fn text_info(&self, ctx: &Context) -> String {
        // It is OK to call text_info on an attached but not connected unit.
        self.inner.borrow().text_info(ctx)
    }

    pub fn connect(&self, ctx: &Context, mode: Unsigned12Bit) {
        // It's permissible to call connect() on an attached but not connected unit.
        self.inner.borrow_mut().connect(ctx, mode)
    }

    pub fn disconnect<A: Alarmer>(&self, ctx: &Context, _alarmer: &mut A) -> Result<(), Alarm> {
        if !self.connected {
            // It's permissible to disconnect an attached but not
            // connected unit.  But we generate a warning, since the
            // code shouldn't do it.
            //
            // TODO: eliminate this special case (i.e. don't
            // disconnect a disconnected unit).
            event!(
                Level::WARN,
                "disconnecting the not-connected unit {:o}",
                self.unit
            );
        }
        self.inner.borrow_mut().disconnect(ctx);
        Ok(())
    }

    pub fn transfer_mode<A: Alarmer>(&self, alarmer: &mut A) -> Result<TransferMode, Alarm> {
        self.call_inner("transfer_mode", alarmer, |unit: &dyn Unit| {
            unit.transfer_mode()
        })
    }

    pub fn read<A: Alarmer>(
        &self,
        ctx: &Context,
        alarmer: &mut A,
    ) -> Result<MaskedWord, TransferFailed> {
        match self.call_mut_inner("read", alarmer, |unit: &mut dyn Unit| unit.read(ctx)) {
            Ok(Ok(mw)) => Ok(mw),
            Ok(Err(e)) => Err(e),
            Err(alarm) => Err(TransferFailed::Alarm(alarm)),
        }
    }

    pub fn write(
        &mut self,
        ctx: &Context,
        source: Unsigned36Bit,
    ) -> Result<Option<OutputEvent>, TransferFailed> {
        self.inner.borrow_mut().write(ctx, source)
    }

    pub fn on_input_event(&self, ctx: &Context, event: InputEvent) {
        self.inner.borrow_mut().on_input_event(ctx, event)
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

    pub fn update_poll_time(&mut self, ctx: &Context, seq: SequenceNumber) {
        if self.poll_queue.update(seq, ctx.simulated_time).is_err() {
            // This happens when we complete an IOS or TSD
            // instruction from a sequence that has no attached
            // hardware.  For example software-only sequences such
            // as 0o0, 0o76 or 0o77.  It's harmless.
        }
    }

    pub fn device_statuses<A: Alarmer>(
        &self,
        ctx: &Context,
        alarmer: &mut A,
    ) -> Result<BTreeMap<Unsigned6Bit, ExtendedUnitState>, Alarm> {
        fn get_extended_status<A: Alarmer>(
            ctx: &Context,
            unit: &AttachedUnit,
            alarmer: &mut A,
        ) -> Result<ExtendedUnitState, Alarm> {
            let (extended_unit_status, flag): (Option<ExtendedConnectedUnitStatus>, bool) =
                if unit.connected {
                    let unit_status = unit.poll(ctx, alarmer)?;
                    let flag: bool = matches!(unit_status.change_flag, Some(FlagChange::Raise));
                    let ext_status = ExtendedConnectedUnitStatus {
                        buffer_available_to_cpu: unit_status.buffer_available_to_cpu,
                        inability: unit_status.inability,
                        missed_data: unit_status.missed_data,
                        special: u16::from(unit_status.special),
                        mode: u16::from(unit_status.mode),
                    };
                    (Some(ext_status), flag)
                } else {
                    (None, false)
                };
            Ok(ExtendedUnitState {
                flag,
                connected: unit.connected,
                in_maintenance: unit.in_maintenance,
                name: unit.name(),
                text_info: unit.text_info(ctx),
                status: extended_unit_status,
            })
        }
        let mut result: BTreeMap<Unsigned6Bit, ExtendedUnitState> = BTreeMap::new();
        for (unit, attached) in self.devices.iter() {
            let ext_status = get_extended_status(ctx, attached, alarmer)?;
            result.insert(*unit, ext_status);
        }
        Ok(result)
    }

    pub fn attach(
        &mut self,
        ctx: &Context,
        unit_number: Unsigned6Bit,
        in_maintenance: bool,
        mut unit: Box<dyn Unit>,
    ) {
        let status: UnitStatus = unit.poll(ctx);
        self.devices.insert(
            unit_number,
            AttachedUnit {
                inner: RefCell::new(unit),
                unit: unit_number,
                is_input_unit: status.is_input_unit,
                connected: false,
                in_maintenance,
            },
        );
        self.poll_queue.push(unit_number, status.poll_after);
    }

    pub fn on_input_event(
        &mut self,
        ctx: &Context,
        unit_number: Unsigned6Bit,
        input_event: InputEvent,
    ) {
        match self.devices.get_mut(&unit_number) {
            Some(attached) => attached.on_input_event(ctx, input_event),
            None => {
                // TODO: consider returning an error result for this
                // case.
            }
        }
    }

    pub fn report(
        &mut self,
        ctx: &Context,
        unit: Unsigned6Bit,
        current_flag: bool,
        alarm_unit: &mut AlarmUnit,
    ) -> Result<Unsigned36Bit, Alarm> {
        match self.devices.get_mut(&unit) {
            Some(attached) => {
                // Because the unit report word contains a `Connect`
                // (2.6) and `Maintenance` bit (2.7) we need to be
                // able to collect status from a unit which is
                // attached but not otherwise usable.
                let unit_status = attached.poll(ctx, alarm_unit)?;
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

    pub fn poll(
        &mut self,
        ctx: &Context,
        alarm_unit: &mut AlarmUnit,
    ) -> Result<(u64, Option<Alarm>, Option<Duration>), Alarm> {
        let system_time = &ctx.simulated_time;
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
                    let unit_status = attached.poll(ctx, alarm_unit)?;
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
        Ok((raised_flags, alarm, next_poll))
    }

    pub fn disconnect_all<A: Alarmer>(
        &mut self,
        ctx: &Context,
        alarmer: &mut A,
    ) -> Result<(), Alarm> {
        for (_, attached) in self.devices.iter_mut() {
            if attached.connected {
                attached.disconnect(ctx, alarmer)?;
                attached.connected = false;
            }
        }
        Ok(())
    }

    pub fn disconnect(
        &mut self,
        ctx: &Context,
        device: &Unsigned6Bit,
        alarm_unit: &mut AlarmUnit,
    ) -> Result<(), Alarm> {
        if *device == u6!(0o42) {
            return Ok(());
        }
        match self.devices.get_mut(device) {
            Some(attached) => {
                if attached.connected {
                    attached.connected = false;
                } else {
                    event!(
                        Level::WARN,
                        "disconnecting unit {device:o} but it is not connected"
                    );
                }
                attached.disconnect(ctx, alarm_unit)
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
        ctx: &Context,
        device: &Unsigned6Bit,
        mode: Unsigned12Bit,
        alarm_unit: &mut AlarmUnit,
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
                    attached.connect(ctx, mode);
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

pub fn set_up_peripherals(ctx: &Context, devices: &mut DeviceManager) {
    fn attach_lw_output(ctx: &Context, unit: Unsigned6Bit, devices: &mut DeviceManager) {
        devices.attach(ctx, unit, false, Box::new(LincolnWriterOutput::new(unit)));
    }

    devices.attach(ctx, PETR, false, Box::new(Petr::new()));
    attach_lw_output(ctx, u6!(0o66), devices);
}
