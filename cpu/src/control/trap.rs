//! Emulates the trap circuit and I/O Unit 42.  See TX-2 User Handbook
//! Chapter 4 section 42.
use base::prelude::*;
use std::time::Duration;

use super::super::*;
use crate::context::Context;
use crate::event::InputEvent;
use crate::io::{Unit, UnitStatus};

#[derive(Debug)]
pub struct TrapCircuit {
    mode: Unsigned12Bit,
    set_metabits_disabled: bool,
}

impl TrapCircuit {
    /// When this bit is set in `mode`, fetching an instruction word
    /// whose metabit is set causes a trap to occur.
    const TRAP_ON_MARKED_INSTRUCTION: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_001_u16);

    /// When this bit is set in `mode`, an instruction cycle which
    /// uses a marked deferred address causes the TRAP flag to be
    /// raised.
    const TRAP_ON_DEFERRED_ADDRESS: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_002_u16);

    /// When this bit is set in `mode`, use of a marked operand causes
    /// the TRAP flag to be raised soon afterward (within a few
    /// instructions).
    const TRAP_ON_OPERAND: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_004_u16);

    /// When this bit is set, change of sequence number causes the
    /// TRAP flag to be raised.  Change of sequence away from sequence
    /// 0o42 (the TRAP sequence itself) does not cause the flag to be
    /// raised).
    const TRAP_ON_CHANGED_SEQUENCE: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_010_u16);

    /// When this bit is set, fetching an instruction from a memory
    /// word causes the meta bit of that word to be set.
    const SET_METABITS_OF_INSTRUCTIONS: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_100_u16);

    /// When this bit is set, the metabit of all deferred addresses used will be set.
    const SET_METABITS_OF_DEFERRED_ADDRESSES: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_200_u16);

    /// When this bit is set, the metabits of memory words containing operands will be set.
    const SET_METABITS_OF_OPERANDS: Unsigned12Bit = Unsigned12Bit::MAX.and(0o000_400_u16);

    pub const fn new() -> TrapCircuit {
        TrapCircuit {
            mode: Unsigned12Bit::ZERO,
            set_metabits_disabled: false,
        }
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
        !self.is_set_metabits_disabled()
            && self.mode & Self::SET_METABITS_OF_DEFERRED_ADDRESSES != 0
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

impl Unit for TrapCircuit {
    fn poll(&mut self, ctx: &Context) -> UnitStatus {
        UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag: None,
            buffer_available_to_cpu: false,
            inability: false,
            missed_data: false,
            mode: self.mode,
            // The trap circuit does not need to be polled.
            poll_after: ctx.simulated_time + Duration::from_secs(60),
            is_input_unit: true,
        }
    }

    fn connect(&mut self, _ctx: &Context, mode: Unsigned12Bit) {
        self.mode = mode;
    }

    fn transfer_mode(&self) -> TransferMode {
        TransferMode::Exchange
    }

    /// The TRAP unit doesn't perform I/O but reads retain the
    /// cycle-left and dismiss features (See Users Handbook, section
    /// 4-15 ("TRAP").  Because it cycles left, it must be an "input"
    /// unit.
    fn read(&mut self, _ctx: &Context) -> Result<MaskedWord, TransferFailed> {
        // TODO: add unit tests for the cycle-left and dismiss
        // behaviours.
        Ok(MaskedWord {
            bits: Unsigned36Bit::ZERO,
            mask: Unsigned36Bit::ZERO,
        })
    }

    /// I don't know whether this is supposed to behave like an input
    /// unit or an output unit.
    fn write(
        &mut self,
        _ctx: &Context,
        _source: Unsigned36Bit,
    ) -> Result<Option<OutputEvent>, TransferFailed> {
        unreachable!()
    }

    fn name(&self) -> String {
        "trap circuit".to_string()
    }

    fn disconnect(&mut self, _ctx: &Context) {
        // Does nothing.
    }

    fn on_input_event(&mut self, _ctx: &Context, _event: InputEvent) {
        // Does nothing.
    }
}
