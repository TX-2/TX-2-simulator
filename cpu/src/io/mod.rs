//! Input/Output.
//!
//! The Report word of I/O units looks like this:
//!
//! | Special - Mag tape | Sequence Number | Flag  | Avail | Maint  | Connected |  EIA  | MISIND |    Mode |
//! | ------------------ | --------------- | ----- | ----- | -----  | --------- | ----- | ------ | ------- |
//! | 3.7-4.9            | 3.1-3.6         | 2.9   | 2.8   | 2.7    | 2.6       | 2.5   | 2.4    | 1.1-2.3 |
//! | (12 bits)          | (6 bits)        |(1 bit)|(1 bit)|(1 bit )| (1 bit)   |(1 bit)|(1 bit) |(12 bits)|
//!

use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Shl;
use std::time::Duration;

use base::prelude::*;
use crate::alarm::Alarm;

/// The mode with which the unit is connected; specified with IOS command 0o3X_XXX.
pub const IO_MASK_MODE: Unsigned36Bit = Unsigned36Bit::MAX.and(     0o_000_000_007_777);

/// When set, indicates that the controlling sequence has missed a data item.
pub const IO_MASK_MISIND: Unsigned36Bit = Unsigned36Bit::MAX.and(   0o_000_000_010_000);

/// When set, indicates an "inability"; i.e.a failure.
pub const IO_MASK_EIA: Unsigned36Bit = Unsigned36Bit::MAX.and(      0o_000_000_020_000);


/// When set, indicates the unit is (already) connected.
pub const IO_MASK_CONNECTED: Unsigned36Bit = Unsigned36Bit::MAX.and(0o_000_000_040_000);

/// When set, indicates that the unit is in maintenance mode (i.e. is not available)
pub const IO_MASK_MAINT: Unsigned36Bit = Unsigned36Bit::MAX.and(    0o_000_000_100_000);

/// When set, indicates that the unit's buffer is available for use (read or write)
/// by the CPU.
pub const IO_MASK_AVAIL: Unsigned36Bit = Unsigned36Bit::MAX.and(    0o_000_000_200_000);

/// When set, indicates that the unit wants attention.  That is, is ready for a
/// TSD instruction or has just been connected.
pub const IO_MASK_FLAG: Unsigned36Bit = Unsigned36Bit::MAX.and(     0o_000_000_400_000);

/// Indicates the sequence number associated with this unit.
pub const IO_MASK_SEQNO: Unsigned36Bit = Unsigned36Bit::MAX.and(    0o_000_077_000_000);

/// Reserved for use by magnetic tape devices.
pub const IO_MASK_SPECIAL: Unsigned36Bit = Unsigned36Bit::MAX.and(  0o_777_700_000_000);


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FlagChange {
    Raise,
}

/// Units report their status (which is used to construct their report
/// word) with this struct.
#[derive(Debug)]
pub struct UnitStatus {
    special: Unsigned12Bit,
    change_flag: Option<FlagChange>,
    buffer_available_to_cpu: bool,
    inability: bool,
    missed_data: bool,
    mode: Unsigned12Bit,

    /// Indicates that the unit wishes to be polled for its status
    /// before the indicated (simulated) duration has elapsed.
    pub poll_before: Duration,

    /// True for units which are input units.  Some devices (Lincoln
    /// Writers for example) occupy two units, one for read (input)
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
    report
	| Unsigned36Bit::from(unit).shl(18)
	| Unsigned36Bit::from(status.special).shl(24)
}


#[derive(Debug)]
pub enum TransferFailed {
    MissingUnit,
    UnitNotConnected,
    UnitInMaintenance,
    ReadOnWriteChannel,
    WriteOnReadChannel,
}

impl Display for TransferFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
	f.write_str(
	    match self {
		TransferFailed::MissingUnit => "missing unit",
		TransferFailed::UnitNotConnected => "unit not connected",
		TransferFailed::UnitInMaintenance => "unit in maintenance",
		TransferFailed::ReadOnWriteChannel => "read on write-only unit",
		TransferFailed::WriteOnReadChannel => "write on read-only unit",
	    }
	)
    }
}

impl std::error::Error for TransferFailed {}

pub trait Unit {
    fn poll(&self) -> UnitStatus;
    fn connect(&mut self, mode: Unsigned12Bit);
    fn read(&mut self, target: &mut Unsigned36Bit) -> Result<(), TransferFailed>;
    fn write(&mut self, source: Unsigned36Bit) -> Result<(), TransferFailed>;
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
    fn assert_unit_connected(&self) -> Result<(), TransferFailed> {
	if self.in_maintenance{
	    Err(TransferFailed::UnitInMaintenance)
	} else if !self.connected {
	    Err(TransferFailed::UnitNotConnected)
	} else {
	    Ok(())
	}
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
    devices: BTreeMap<Unsigned6Bit, AttachedUnit>
}

impl DeviceManager {
    pub fn new() -> DeviceManager {
	DeviceManager {
	    devices: BTreeMap::new(),
	}
    }

    pub fn attach(
	&mut self,
	unit_number: Unsigned6Bit,
	in_maintenance: bool,
	unit: Box<dyn Unit>,
    ) {
	let status: UnitStatus = unit.poll();
	self.devices.insert(unit_number, AttachedUnit {
	    inner: unit,
	    is_input_unit: status.is_input_unit,
	    connected: false,
	    in_maintenance,
	});
    }

    pub fn report(&mut self, unit: Unsigned6Bit, current_flag: bool) -> Result<Unsigned36Bit, Alarm> {
	match self.devices.get_mut(&unit) {
	    Some(attached) => {
		// Because the unit report word contains a `Connect`
		// (2.6) and `Maintenance` bit (2.7) we need to be
		// able to collect status from a unit which is
		// attached but not otherwise usable.
		let unit_status = attached.inner.poll();
		Ok(make_unit_report_word(unit, attached.connected, attached.in_maintenance, current_flag, &unit_status))
	    }
	    None => {
		Err(Alarm::IOSAL {
		    unit,
		    operand: None,
		    message: format!("unit {} is not known", unit),
		})
	    }
	}
    }

    pub fn poll(&mut self) -> (u64, Option<Alarm>) {
	let mut raised_flags: u64 = 0;
	let mut alarm: Option<Alarm> = None;
	for (devno, attached) in self.devices.iter_mut() {
	    if !attached.connected {
		continue;
	    }
	    assert!(!attached.in_maintenance); // cannot connect in-maint devices.
	    let unit_status = attached.inner.poll();
	    match unit_status.change_flag {
		Some(FlagChange::Raise) => {
		    raised_flags |= 1 << u8::from(*devno);
		}
		None => ()
	    }
	    if alarm.is_none() {
		// TODO: support masking for alarms (hardware and
		// software masking are both available; either should
		// be able to mask it).
		if unit_status.inability {
		    alarm = Some(Alarm::IOSAL {
			unit: *devno,
			operand: None,
			message: format!("unit {} reports inability (EIA)", devno),
		    });
		} else if unit_status.missed_data {
		    alarm = Some(Alarm::MISAL { unit: *devno, });
		}
	    }
	}
	(raised_flags, alarm)
    }

    pub fn connect(&mut self, device: &Unsigned6Bit, mode: Unsigned12Bit) -> Result<bool, Alarm> {
	match self.devices.get_mut(device) {
	    Some(attached) => {
		let was_already_connected: bool = attached.connected;
		attached.inner.connect(mode);
		Ok(was_already_connected)
	    }
	    None => Err(Alarm::IOSAL {
		unit: *device,
		operand: None,
		message: format!("Attempt to connect missing unit {}", device),
	    }),
	}
    }

    pub fn read(&mut self, device: &Unsigned6Bit, target: &mut Unsigned36Bit) -> Result<(), TransferFailed> {
	match self.devices.get_mut(device) {
	    Some(attached) => {
		attached.assert_unit_connected()?;
		if !attached.is_input_unit {
		    Err(TransferFailed::ReadOnWriteChannel)
		} else {
		    attached.inner.read(target)
		}
	    }
	    None => Err(TransferFailed::MissingUnit),
	}
    }

    pub fn write(&mut self, device: &Unsigned6Bit, source: Unsigned36Bit) -> Result<(), TransferFailed> {
	match self.devices.get_mut(device) {
	    Some(attached) => {
		attached.assert_unit_connected()?;
		if attached.is_input_unit {
		    Err(TransferFailed::WriteOnReadChannel)
		} else {
		    attached.inner.write(source)
		}
	    }
	    None => Err(TransferFailed::MissingUnit),
	}
    }
}
