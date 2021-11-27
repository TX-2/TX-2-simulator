use base::prelude::*;
use base::subword;

use crate::alarm::Alarm;
use crate::control::{
    ControlUnit,
    ProgramCounterChange,
};
use crate::memory::{
    BitChange,
    MemoryMapped,
    MemoryUnit,
    MemoryOpFailure,
    WordChange,
};

/// ## "Jump Skip Class" opcodes
///
/// - JMP: [`ControlUnit::op_jmp`]
/// - JPA (unimplemented)
/// - JNA (unimplemented)
/// - JOV (unimplemented)
/// - SKM: [`ControlUnit::op_skm`]
/// - SED (unimplemented)
impl ControlUnit {
    /// Implements the JMP opcode and its variations (all of which are unconditional jumps).
    pub fn op_jmp(&mut self) -> Result<(), Alarm> {
        // For JMP the configuration field in the instruction controls
        // the behaviour of the instruction, without involving
        // a load from F-memory.
        fn nonzero(value: Unsigned5Bit) -> bool {
            !value.is_zero()
        }
        let cf = self.regs.n.configuration();
        let dismiss = nonzero(cf & 0b10000_u8);
        let save_q = nonzero(cf & 0b01000_u8);
        let savep_e = nonzero(cf & 0b00100_u8);
        let savep_ix = nonzero(cf & 0b00010_u8);
        let indexed = nonzero(cf & 0b00001_u8);
        let left: Unsigned18Bit = if save_q {
            Unsigned18Bit::from(self.regs.q)
        } else {
            subword::left_half(self.regs.e)
        };
        let right: Unsigned18Bit = if savep_e {
            Unsigned18Bit::from(self.regs.p)
        } else {
            subword::right_half(self.regs.e)
        };
        self.regs.e = subword::join_halves(left, right);

        if savep_ix {
            let j = self.regs.n.index_address();
            if j != 0 {
                // Xj is fixed at 0.
                let p = self.regs.p;
                self.regs.set_index_register_from_address(j, &p);
            }
        }

        let physical: Address = match self.regs.n.operand_address() {
            OperandAddress::Deferred(_) => {
                // TODO: I don't know whether this is allowed or
                // not, but if we disallow this for now, we can
                // use any resulting error to identify cases where
                // this is in fact used.
                return Err(Alarm::PSAL(
                    u32::from(self.regs.n.operand_address_and_defer_bit()),
                    format!(
                        "JMP target has deferred address {:#o}",
                        self.regs.n.operand_address()
                    ),
                ));
            }
            OperandAddress::Direct(phys) => phys,
        };

	let new_pc: Address = if indexed {
	    physical.index_by(self.regs.n.index_address().reinterpret_as_signed())
        } else {
	    physical
        };
	self.set_program_counter(ProgramCounterChange::Jump(new_pc));
        if dismiss {
	    self.dismiss_unless_held();
        }
        Ok(())
    }

    /// Implement the SKM instruction.  This has a number of
    /// supernumerary mnemonics.  The index address field of the
    /// instruction identifies which bit (within the target word) to
    /// operate on, and the instruction configuration value determines
    /// both how to manipulate that bit, and what to do on the basis
    /// of its original value.
    ///
    /// The SKM instruction is documented on pages 7-34 and 7-35 of
    /// the User Handbook.
    pub fn op_skm(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
	let bit = index_address_to_bit_selection(self.regs.n.index_address());
	// Determine the operand address; any initial deferred cycle
	// must use 0 as the indexation, as the index address of the
	// SKM instruction is used to identify the bit to operate on.
	let target = self.resolve_operand_address(mem, Some(Unsigned6Bit::ZERO))?;
	let cf: u8 = u8::from(self.regs.n.configuration());
	let change: WordChange = WordChange {
	    bit,
	    bitop: match cf & 0b11 {
		0b00 => None,
		0b01 => Some(BitChange::Flip),
		0b10 => Some(BitChange::Clear),
		0b11 => Some(BitChange::Set),
		_ => unreachable!(),
	    },
	    cycle: cf & 0b100 != 0,
	};
	let prev_bit_value: Option<bool> = match mem.change_bit(&target, &change) {
	    Ok(prev) => prev,
	    Err(MemoryOpFailure::NotMapped) => {
		return Err(Alarm::QSAL(
		    self.regs.n,
		    target.into(),
                    format!(
			"SKM instruction attempted to access address {:o} but it is not mapped",
			target,
                    ),
		));
	    }
	    Err(MemoryOpFailure::ReadOnly) => {
		return Err(Alarm::QSAL(
		    self.regs.n,
		    target.into(),
                    format!(
			"SKM instruction attempted to modify (instruction configuration={:o}) a read-only location {:o}",
			cf,
			target,
                    ),
		));
	    }
	};
	let skip: bool = if let Some(prevbit) = prev_bit_value {
	    match (cf >> 3) & 3 {
		0b00 => false,
		0b01 => true,
		0b10 => !prevbit,
		0b11 => prevbit,
		_ => unreachable!(),
	    }
	} else {
	    // The index address specified a nonexistent bit
	    // (e.g. 1.0) and so we do not perform a skip.
	    false
	};
	// The location of the currently executing instruction is referred to by M4
	// as '#'.  The next instruction would be '#+1' and that's where the P register
	// currently points.  But "skip" means to set P=#+2.
	if skip {
	    self.set_program_counter(ProgramCounterChange::CounterUpdate);
	}
	Ok(())
    }

}
