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

use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Shl;
use std::time::Duration;

use tracing::{event, span, Level};

use crate::alarm::{Alarm, AlarmUnit, BadMemOp};
use crate::memory::{MemoryMapped, MemoryOpFailure, MemoryUnit, MetaBitChange};
use crate::{Clock, ControlUnit};
use base::prelude::*;

mod dev_petr;
mod pollq;

pub use dev_petr::{Petr, TapeIterator};
use pollq::PollQueue;

/// The mode with which the unit is connected; specified with IOS command 0o3X_XXX.
pub const IO_MASK_MODE: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_007_777);

/// When set, indicates that the controlling sequence has missed a data item.
pub const IO_MASK_MISIND: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_010_000);

/// When set, indicates an "inability"; i.e.a failure.
pub const IO_MASK_EIA: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_020_000);

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

/// Indicates the sequence number associated with this unit.
pub const IO_MASK_SEQNO: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_077_000_000);

/// Reserved for use by magnetic tape devices.
pub const IO_MASK_SPECIAL: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_777_700_000_000);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagChange {
    Raise,
}

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

#[derive(Debug)]
pub enum TransferFailed {
    BufferNotFree,
}

impl Display for TransferFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            TransferFailed::BufferNotFree => "Unit buffer not available for use by the CPU",
        })
    }
}

impl std::error::Error for TransferFailed {}

pub trait Unit {
    fn poll(&mut self, system_time: &Duration) -> UnitStatus;
    fn connect(&mut self, system_time: &Duration, mode: Unsigned12Bit);
    fn read(
        &mut self,
        system_time: &Duration,
        target: &mut Unsigned36Bit,
    ) -> Result<(), TransferFailed>;
    fn write(
        &mut self,
        system_time: &Duration,
        source: Unsigned36Bit,
    ) -> Result<(), TransferFailed>;
    fn name(&self) -> String;
}

struct AttachedUnit {
    inner: Box<dyn Unit>,

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
}

impl Debug for AttachedUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("AttachedUnit")
            .field("inner", &format_args!("<unit: {}>", self.inner.name()))
            .field("is_input_unit", &self.is_input_unit)
            .field("connected", &self.connected)
            .field("in_maintenance", &self.in_maintenance)
            .finish()
    }
}

/// Manages a collection of devices.  Does not actually correspond to
/// a tangible physical component of the TX-2 system.
#[derive(Debug)]
pub struct DeviceManager {
    devices: BTreeMap<Unsigned6Bit, AttachedUnit>,
    poll_queue: PollQueue,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TransferOutcome {
    /// When the outcome is successful, let the caller know if the
    /// memory location's meta bit was set.  This allows the trap
    /// circuit to be triggered if necessary.
    Success(bool),

    /// When the outcome of the TSD is dismiss and wait, we don't
    /// trigger the trap circuit (not because we think the TX-2 behaved
    /// this way, but because it keeps the code simpler and we don't
    /// know if the oposite behaviour is needed).
    DismissAndWait,
}

type OpConversion = fn(Address) -> BadMemOp;

fn bad_read(addr: Address) -> BadMemOp {
    BadMemOp::Read(addr.into())
}

fn bad_write(addr: Address) -> BadMemOp {
    BadMemOp::Write(addr.into())
}

fn make_tsd_qsal(inst: Instruction, op: BadMemOp) -> Alarm {
    Alarm::QSAL(inst, op, "TSD address is not mapped".to_string())
}

impl DeviceManager {
    pub fn new() -> DeviceManager {
        DeviceManager {
            devices: BTreeMap::new(),
            poll_queue: PollQueue::new(),
        }
    }

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
                inner: unit,
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
                let unit_status = attached.inner.poll(system_time);
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
                    let unit_status = attached.inner.poll(system_time);
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

    pub fn disconnect_all(&mut self) {
        for (_, attached) in self.devices.iter_mut() {
            attached.connected = false;
        }
    }

    pub fn disconnect(
        &mut self,
        device: &Unsigned6Bit,
        alarm_unit: &AlarmUnit,
    ) -> Result<(), Alarm> {
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
                    attached.inner.connect(system_time, mode);
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

    /// Perform a TSD instruction.
    #[allow(clippy::too_many_arguments)]
    pub fn transfer(
        &mut self,
        system_time: &Duration,
        device: &Unsigned6Bit,
        // TODO: reduce argument count, perhaps pass the whole
        // instruction.
        config: &Unsigned5Bit,
        address: &Address,
        mem: &mut MemoryUnit,
        inst: &Instruction,
        meta_op: &MetaBitChange,
        alarm_unit: &AlarmUnit,
    ) -> Result<TransferOutcome, Alarm> {
        if *config != Unsigned5Bit::ZERO {
            return Err(alarm_unit.always_fire(Alarm::ROUNDTUITAL(format!(
                "TSD instruction has non-zero configuration value {:o}",
                config,
            ))));
        }

        let not_mapped = |op_conv: OpConversion| -> Alarm {
            let op: BadMemOp = op_conv(*address);
            make_tsd_qsal(*inst, op)
        };

        match u8::from(*device) {
            0o40..=0o75 => {
                // This is an "INOUT" channel, per Users Handbook,
                // page 4-2.
                match self.devices.get_mut(device) {
                    None => {
                        event!(Level::WARN, "TSD on unknown unit {:o}", *device);
                        Ok(TransferOutcome::DismissAndWait)
                    }
                    Some(attached) => {
                        // When the result of the TSD is dismiss and
                        // wait, we don't trigger traps relating to
                        // the state of the meta bit.
                        if !attached.connected {
                            event!(Level::WARN, "TSD on disconnected unit {:o}", *device);
                            return Ok(TransferOutcome::DismissAndWait);
                        }

                        // TODO: consider rewriting this function to
                        // use MemoryUnit::write_with_read_fallback().
                        let inner_result: Result<TransferOutcome, TransferFailed> = if attached
                            .is_input_unit
                        {
                            event!(Level::TRACE, "Read TSD on unit {:o}", *device);
                            // Because a TSD may only affect part of a
                            // word, we perform a memory fetch and
                            // then write the value back.
                            match mem.fetch(address, meta_op) {
                                Ok((mut word, extra_bits)) => {
                                    match attached.inner.read(system_time, &mut word) {
                                        Ok(()) => match mem.store(address, &word, meta_op) {
                                            Ok(()) => {
                                                event!(
                                                    Level::TRACE,
                                                    "Read TSD succeeded on unit {:o} (stored word at {:>06o} is {:o})",
                                                    *device, &address, &word,
                                                );
                                                Ok(TransferOutcome::Success(extra_bits.meta))
                                            }
                                            Err(MemoryOpFailure::ReadOnly(_, _)) => {
                                                event!(
							Level::WARN,
							"Read TSD attempted to write into read-only location {} (this is valid but unusual)",
							address
						    );
                                                Ok(TransferOutcome::Success(extra_bits.meta))
                                            }
                                            Err(MemoryOpFailure::NotMapped(addr)) => {
                                                return Err(Alarm::BUGAL {
                                                    instr: Some(*inst),
                                                    message: format!(
							    "Read TSD found memory location {} was mapped on read but not write" ,
							    addr,
							),
                                                });
                                            }
                                        },
                                        Err(TransferFailed::BufferNotFree) => {
                                            event!(Level::TRACE, "Read TSD on unit {:o} resulted in dismiss and wait", *device);
                                            Ok(TransferOutcome::DismissAndWait)
                                        }
                                    }
                                }
                                Err(MemoryOpFailure::ReadOnly(_, _)) => unreachable!(),
                                Err(MemoryOpFailure::NotMapped(_)) => {
                                    alarm_unit.fire_if_not_masked(not_mapped(bad_read))?;
                                    // QSAL is masked, carry on.
                                    Ok(TransferOutcome::Success(false)) // act as if metabit unset
                                }
                            }
                        } else {
                            event!(Level::TRACE, "Write TSD on unit {:o}", *device);
                            match mem.fetch(address, meta_op) {
                                Ok((word, extra_bits)) => {
                                    match attached.inner.write(system_time, word) {
                                        Ok(()) => Ok(TransferOutcome::Success(extra_bits.meta)),
                                        Err(e) => Err(e),
                                    }
                                }
                                Err(MemoryOpFailure::ReadOnly(_, _)) => unreachable!(),
                                Err(MemoryOpFailure::NotMapped(_)) => {
                                    alarm_unit.fire_if_not_masked(not_mapped(bad_write))?;
                                    // QSAL is masked, carry on.
                                    Ok(TransferOutcome::Success(false)) // act as if metabit unset
                                }
                            }
                        };

                        match inner_result {
                            Err(TransferFailed::BufferNotFree) => {
                                event!(
                                    Level::DEBUG,
                                    "Buffer of unit {:o} is not free, will dismiss and wait",
                                    *device
                                );
                                Ok(TransferOutcome::DismissAndWait)
                            }
                            Ok(outcome) => Ok(outcome),
                        }
                    }
                }
            }
            _ => {
                // Not an "INOUT" channel.  Cycle the target word one
                // place to the left (Users Handbook, page 4-2).
                match mem.cycle_word(address) {
                    Ok(extra_bits) => Ok(TransferOutcome::Success(extra_bits.meta)),
                    Err(MemoryOpFailure::ReadOnly(_address, extra_bits)) => {
                        // The read-only case is not an error, it's
                        // normal.  The TSD instruction simply has no
                        // effect when the target address is
                        // read-only.
                        Ok(TransferOutcome::Success(extra_bits.meta))
                    }
                    Err(MemoryOpFailure::NotMapped(_)) => {
                        alarm_unit.fire_if_not_masked(not_mapped(bad_write))?;
                        // QSAL is masked, carry on.
                        Ok(TransferOutcome::Success(false)) // act as if metabit unset
                    }
                }
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
    control: &mut ControlUnit,
    clock: &C,
    tapes: Box<dyn TapeIterator>,
) {
    let now = clock.now();
    control.attach(&now, u6!(0o52_u8), false, Box::new(Petr::new(tapes)));
}
