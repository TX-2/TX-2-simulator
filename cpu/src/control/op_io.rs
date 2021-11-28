use base::prelude::*;

use crate::alarm::Alarm;
use crate::control::{
    ControlUnit,
};

impl ControlUnit {
    /// Implements the IOS opcode
    pub fn op_ios(&mut self) -> Result<(), Alarm> {
        let j = self.regs.n.index_address();
	let cf = self.regs.n.configuration();

	if cf & 1 != 0 {
	    // Setting the report bit in the configuration value
	    // causes the device's status word from before any mode
	    // change to be copied into the E register.  (as stated in
	    // section 4-3.6 of the User Handbook).
	    let flag_raised: bool = self.regs.flags.current_flag_state(&j);
	    self.regs.e = self.devices.report(j, flag_raised)?;
	}

        let operand = self.regs.n.operand_address_and_defer_bit();
	match u32::from(operand) {
	    0o20_000 => self.disconnect_unit(j),
	    0o30_000..=0o37_777 => {
		let mode: Unsigned12Bit = Unsigned12Bit::try_from(operand & 0o07_777).unwrap();
		self.connect_unit(j, mode)
	    }
	    0o40_000 => {
		self.regs.flags.lower(&j);
		if self.regs.k == Some(j) {
		    // J is the current sequence, so the flag is
		    // lowered but don't perform a drop-out (see User
		    // Handbook page 4-7).
		    self.regs.current_sequence_is_runnable = true;
		}
		Ok(())
	    }
	    0o50_000 => {
		self.regs.flags.raise(&j);
		Ok(())
	    }
	    0o60_000..=0o60777 => {
		// Select unit XXX
		Err(Alarm::ROUNDTUITAL(
		    format!(
			"IOS operand {:o}: Select Unit command is not yet implemented.",
			operand)))
	    }
	    _ => {
		let command: u8 = (u32::from(operand) >> 12) as u8;
		Err(Alarm::IOSAL {
		    unit: j,
		    operand: Some(operand),
		    message: format!(
			"IOS operand {:o} has unrecognised leading command digit {:o}",
			operand,
			command,
		    ),
		})
	    }
	}
    }

    fn connect_unit(&mut self, unit: Unsigned6Bit, mode: Unsigned12Bit) -> Result<(), Alarm> {
	let result = match u8::from(unit) {
	    0o42 => {
		self.trap.connect(&mode)?;
		// I assume this is not an "output" unit so connecting
		// it should not have the side effect of raising the
		// flag.
		Ok(false)	// not an input unit
	    }
	    _ => self.devices.connect(&unit, mode)
	};
	match result {
	    Ok(true) => {
		// must be an input unit.
		self.regs.flags.raise(&unit);
		Ok(())
	    }
	    Ok(false) => Ok(()),
	    Err(e) => Err(e),
	}
    }

    fn disconnect_unit(&mut self, unit: Unsigned6Bit) -> Result<(), Alarm> {
	match u8::from(unit) {
	    0o42 => self.trap.disconnect(),
	    _ => Err(Alarm::ROUNDTUITAL(format!("I/O unit {} is not yet implemented.", unit))),
	}
    }
}
