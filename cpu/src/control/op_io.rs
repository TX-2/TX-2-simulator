use base::prelude::*;

use crate::alarm::Alarm;
use crate::control::{
    ControlUnit,
};

impl ControlUnit {
    /// Implements the IOS opcode
    pub fn op_ios(&mut self) -> Result<(), Alarm> {
        let j = self.regs.n.index_address();
        let operand = self.regs.n.operand_address_and_defer_bit();
	match u32::from(operand) {
	    0o20_000 => self.disconnect_unit(j),
	    0o30_000..=0o37_777 => self.connect_unit(j, operand & 0o07_777),
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
		    operand,
		    message: format!(
			"IOS operand {:o} has unrecognised leading command digit {:o}",
			operand,
			command,
		    ),
		})
	    }
	}
    }

    fn connect_unit(&mut self, unit: Unsigned6Bit, mode: Unsigned18Bit) -> Result<(), Alarm> {
	// TODO: connecting some unit J (when not previous connected)
	// where J is an output unit should also cause its flag to be
	// raised.
	match u8::from(unit) {
	    0o42 => {
		// I assume this is not an "output" unit so connecting
		// it should not have the side effect of raising the
		// flag.
		self.trap.connect(&mode)
	    }
	    _ => Err(Alarm::ROUNDTUITAL(format!("I/O unit {} is not yet implemented.", unit))),
	}
    }

    fn disconnect_unit(&mut self, unit: Unsigned6Bit) -> Result<(), Alarm> {
	match u8::from(unit) {
	    0o42 => self.trap.disconnect(),
	    _ => Err(Alarm::ROUNDTUITAL(format!("I/O unit {} is not yet implemented.", unit))),
	}
    }
}
