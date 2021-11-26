//! Implementations of "Index Register Class" opcodes
//! - RSX (unimplemented)
//! - DPX: [`ControlUnit::op_dpx`]
//! - EXX (unimplemented)
//! - AUX (unimplemented)
//! - ADX (unimplemented)
//! - SKX: [`ControlUnit::op_skx`]
//! - JPX: [`ControlUnit::op_jpx`]
//! - JNX: [`ControlUnit::op_jnx`]

use base::prelude::*;
use base::subword;

use crate::alarm::Alarm;
use crate::control::{
    ControlUnit,
    sign_extend_index_value,
    ProgramCounterChange,
};
use crate::memory::MemoryUnit;
use crate::memorymap::MetaBitChange;

/// ## "Index Register Class" opcodes
///
/// - RSX (unimplemented)
/// - DPX: [`ControlUnit::op_dpx`]
/// - EXX (unimplemented)
/// - AUX (unimplemented)
/// - ADX (unimplemented)
/// - SKX: [`ControlUnit::op_skx`]
/// - JPX: [`ControlUnit::op_jpx`]
/// - JNX: [`ControlUnit::op_jnx`]
///
impl ControlUnit {
    /// Implements the DPX instruction (Opcode 016, User Handbook,
    /// page 3-16).
    pub fn op_dpx(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
	let j = self.regs.n.index_address();
        let xj: Unsigned36Bit = sign_extend_index_value(&self.regs.get_index_register(j));
        let target: Address = self.operand_address_with_optional_defer_and_index(mem)?;
        let (dest, _meta) = self.fetch_operand_from_address(mem, &target)?;
        self.memory_store_with_exchange(
            mem,
            &target,
            &xj,
            &dest,
            &MetaBitChange::None,
        )
    }

    /// Implements the SKX instruction (Opcode 012, User Handbook,
    /// page 3-24).
    pub fn op_skx(&mut self) -> Result<(), Alarm> {
        let inst = &self.regs.n;
        let j = inst.index_address();
        // SKX does not cause an access to STUV memory; instead the
        // operand is the full value of the operand and defer fields
        // of the instruction.  This allows us to use SKX to mark a
        // placeholder for use with TRAP 42.
        let operand = inst.operand_address_and_defer_bit();
        match u8::from(inst.configuration()) {
            0o0 | 0o10 => {
                if j != 0 {
                    // Xj is fixed at 0.
                    self.regs.set_index_register(j.into(), &operand.reinterpret_as_signed());
                }
                if j & 0o10 != 0 {
                    self.regs.flags.raise(&j.into());
                }
                Ok(())
            }
	    0o1 => {
                if j != 0 {  // Xj is fixed at 0.
		    // Calculate -T
		    let t_negated = Signed18Bit::ZERO.wrapping_sub(operand.reinterpret_as_signed());
                    self.regs.set_index_register(j.into(), &t_negated);
                }
                Ok(())
	    }
            _ => Err(Alarm::ROUNDTUITAL(format!(
                "SKX configuration {:#o} is not implemented yet",
                inst.configuration()
            ))),
        }
    }

    /// Implements the JPX (jump on positive index) opcode (06).
    pub fn op_jpx(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
	let is_positive_address = |xj: &Signed18Bit| xj.is_positive();
	self.impl_op_jpx_jnx(is_positive_address, mem)
    }

    /// Implements the JNX (jump on positive index) opcode (07).
    pub fn op_jnx(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
	let is_negative_address = |xj: &Signed18Bit| xj.is_negative();
	self.impl_op_jpx_jnx(is_negative_address, mem)
    }

    // Implements JPX (opcode 06) and JNX.  Note that these opcodes
    // handle deferred addressing in a unique way.  This is described
    // on page 5-9 of the User Handbook:
    //
    // EXCEPT when the operation is JNX or JPX (codes 6 and 7), for on
    // these two operations the right half of N is used for the sign
    // extended index increment (18 bits).  (BUT if the JNX or JPX is
    // deferred, the increment is not addded until PK3 so N is not
    // changed during PK1).
    pub fn impl_op_jpx_jnx<F: FnOnce(&Signed18Bit)->bool>(
	&mut self,
	predicate: F,
	mem: &mut MemoryUnit,
    ) -> Result<(), Alarm> {
	let dismiss = !self.regs.n.is_held();
	let j = self.regs.n.index_address();
	let xj = self.regs.get_index_register(j);
	let do_jump: bool = predicate(&xj);

	// Compute the jump target (which possibly involves indexing)
	// before modifying Xj.  See note 3 on page 3-27 of the User
	// Handbook, which says
	//
	// The address of a deferred JNX or JPX is completely
	// determined before the index register is changed.  Therefore
	// a ⁻¹JPXₐ|ₐ S would jump to Sₐ as defined by the original
	// contents of Xₐ - if it jumps at all.
        let target: Address = self.resolve_operand_address(mem, Some(Unsigned6Bit::ZERO))?;
	let cf: Signed5Bit = self.regs.n.configuration().reinterpret_as_signed();
	let new_xj: Signed18Bit = xj.wrapping_add(Signed18Bit::from(cf));
	self.regs.set_index_register(j, &new_xj);

	if do_jump {
            self.dismiss_unless_held();
            self.regs.e = subword::join_halves(subword::left_half(self.regs.e),
					       Unsigned18Bit::from(self.regs.p));
            self.set_program_counter(ProgramCounterChange::Jump(target));
	}
        if dismiss {
            if let Some(current_seq) = self.regs.k {
                self.regs.flags.lower(&current_seq);
		self.regs.current_sequence_is_runnable = false;
            }
        }
        Ok(())
     }
}
