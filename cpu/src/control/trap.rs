//! Emulates the trap circuit and I/O Unit 42.  See TX-2 User Handbook
//! Chapter 4 section 42.

use base::prelude::*;

use crate::alarm::Alarm;

#[derive(Debug)]
pub struct TrapCircuit {
    mode: Unsigned18Bit,
    set_metabits_disabled: bool,
}

impl TrapCircuit {
    /// When this bit is set in `mode`, fetching an instruction word
    /// whose metabit is set causes a trap to occur.
    const TRAP_ON_MARKED_INSTRUCTION: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_001_u32);

    /// When this bit is set in `mode`, an instruction cycle which
    /// uses a marked deferred address causes the TRAP flag to be
    /// raised.
    const TRAP_ON_DEFERRED_ADDRESS: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_002_u32);

    /// When this bit is set in `mode`, use of a marked operand causes
    /// the TRAP flag to be raised soon afterward (within a few
    /// instructions).
    const TRAP_ON_OPERAND: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_004_u32);

    /// When this bit is set, change of sequence number causes the
    /// TRAP flag to be raised.  Change of sequence away from sequence
    /// 0o42 (the TRAP sequence itself) does not cause the flag to be
    /// raised).
    const TRAP_ON_CHANGED_SEQUENCE: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_010_u32);

    /// When this bit is set, fetching an instruction from a memory
    /// word causes the meta bit of that word to be set.
    const SET_METABITS_OF_INSTRUCTIONS: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_100_u32);

    /// When this bit is set, the metabit of all deferred addresses used will be set.
    const SET_METABITS_OF_DEFERRED_ADDRESSES: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_200_u32);

    /// When this bit is set, the metabits of memory words containing operands will be set.
    const SET_METABITS_OF_OPERANDS: Unsigned18Bit = Unsigned18Bit::MAX.and(0o000_400_u32);

    pub const fn new() -> TrapCircuit {
	TrapCircuit {
	    mode: Unsigned18Bit::ZERO,
	    set_metabits_disabled: false,
	}
    }

    /// Does nothing.
    pub fn disconnect(&mut self) -> Result<(), Alarm> {
	Ok(())
    }

    /// Connect the TRAP unit and set the software mode (which can
    /// enable setting of metabits, assuming the hardware switch
    /// setting permits it).
    pub fn connect(&mut self, mode: &Unsigned18Bit) -> Result<(), Alarm> {
	self.mode = *mode;
	Ok(())
    }

    /// Query the hardware switch setting which would disable all
    /// setting of metabits.
    pub fn is_set_metabits_disabled(&self) -> bool {
	self.set_metabits_disabled
    }

    /// Change the (emulated) hardware switch setting which (when
    /// `disable` is true) would disable all setting of metabits.
    pub fn set_metabits_disabled(&mut self, disable: bool) {
	self.set_metabits_disabled = disable
    }

    /// Indicate whether the machine should set the metabits of words
    /// from which it fetches instructions.
    pub fn set_metabits_of_instructions(&self) -> bool {
	!self.is_set_metabits_disabled() && self.mode & Self::SET_METABITS_OF_INSTRUCTIONS != 0
    }

    /// Indicate whether the machine should set the metabits of words
    /// from which it fetches deferred addresses.
    pub fn set_metabits_of_deferred_addresses(&self) -> bool {
	!self.is_set_metabits_disabled() && self.mode & Self::SET_METABITS_OF_DEFERRED_ADDRESSES != 0
    }

    /// Indicate whether the machine should set the metabits of words
    /// from which it fetches operands.
    pub fn set_metabits_of_operands(&self) -> bool {
	!self.is_set_metabits_disabled() && self.mode & Self::SET_METABITS_OF_OPERANDS != 0
    }

    /// Indicate whether the TRAP flag should be raised during
    /// execution of an instruction whose metabit is set.
    pub fn trap_on_marked_instruction(&self) -> bool {
	self.mode & Self::TRAP_ON_MARKED_INSTRUCTION != 0
    }

    /// Indicate whether an instruction cycle which uses a marked
    /// deferred address causes the TRAP flag to be raised.
    pub fn trap_on_deferred_address(&self) -> bool {
	self.mode & Self::TRAP_ON_DEFERRED_ADDRESS != 0
    }

    /// Indicate whether use of a marked operand causes the TRAP flag
    /// to be raised soon afterward (within a few instructions).
    pub fn trap_on_operand(&self) -> bool {
	self.mode & Self::TRAP_ON_OPERAND != 0
    }

    /// Indicate whether change of sequence number causes the TRAP
    /// flag to be raised.  Change of sequence away from sequence 0o42
    /// (the TRAP sequence itself) does not cause the flag to be
    /// raised).
    pub fn trap_on_changed_sequence(&self) -> bool {
	self.mode & Self::TRAP_ON_CHANGED_SEQUENCE != 0
    }
}
