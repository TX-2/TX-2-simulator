//! Implementations of "Index Register Class" opcodes
//! - RSX [`ControlUnit::op_rsx`]
//! - DPX: [`ControlUnit::op_dpx`]
//! - EXX (unimplemented)
//! - AUX [`ControlUnit::op_aux`]
//! - ADX (unimplemented)
//! - SKX: [`ControlUnit::op_skx`]
//! - JPX: [`ControlUnit::op_jpx`]
//! - JNX: [`ControlUnit::op_jnx`]

use base::prelude::*;
use base::subword;

use crate::alarm::{Alarm, BadMemOp};
use crate::control::{sign_extend_index_value, ControlUnit, ProgramCounterChange};
use crate::memory::{MemoryUnit, MetaBitChange};

/// ## "Index Register Class" opcodes
///
/// - RSX: [`ControlUnit::op_rsx`]
/// - DPX: [`ControlUnit::op_dpx`]
/// - AUX [`ControlUnit::op_aux`]
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

        // DPX is trying to perform a write.  But to do this in some
        // subword configurations, we need to read the existing value.
        match self.fetch_operand_from_address(mem, &target) {
            Ok((dest, _meta)) => {
                self.memory_store_with_exchange(mem, &target, &xj, &dest, &MetaBitChange::None)
            }
            Err(Alarm::QSAL(inst, BadMemOp::Read(addr), msg)) => {
                // That read operation just failed.  So we handle this
                // as a _write_ failure, meaning that we change
                // BadMemOp::Read to BadMemOp::Write.
                self.alarm_unit.fire_if_not_masked(Alarm::QSAL(
                    inst,
                    BadMemOp::Write(addr),
                    msg,
                ))?;
                Ok(()) // QSAL is masked, we just carry on (the DPX instruction has no effect).
            }
            Err(other) => Err(other),
        }
    }

    /// Implements the AUX instruction (Opcode 010, User Handbook,
    /// page 3-22).
    pub fn op_aux(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
        let j = self.regs.n.index_address();
        // The AUX instruction is not indexed.
        let source: Address = self.operand_address_with_optional_defer_without_index(mem)?;
        // If j == 0 nothing is going to happen (X₀ is always 0) but
        // we still need to make sure we raise an alarm if the memory
        // access is invalid.
        let (word, _extra) = self.fetch_operand_from_address(mem, &source)?;
        if !j.is_zero() {
            let xj: Signed18Bit = self.regs.get_index_register(j);
            let m: Signed18Bit = subword::right_half(word).reinterpret_as_signed();
            let mut newvalue = xj.wrapping_add(m);
            // If the system configuration states that only some
            // quarters are active, the other quarters of the index
            // register are set to zero (Users Handbook, page 3-22).
            // The call to [`ControlUnit::fetch_operand_from_address`]
            // will already have applied the correct subword form to
            // `word`.
            let quarter_activity = self.get_config().active_quarters();
            if !quarter_activity.is_active(&0) {
                // Zero out the right quarter of newvalue.
                newvalue = newvalue
                    .reinterpret_as_unsigned()
                    .and(0o777000)
                    .reinterpret_as_signed();
            }
            if !quarter_activity.is_active(&1) {
                // Zero out the left quarter of newvalue.
                newvalue = newvalue
                    .reinterpret_as_unsigned()
                    .and(0o0777)
                    .reinterpret_as_signed();
            }
            self.regs.set_index_register(j, &newvalue);
        }
        Ok(())
    }

    /// Implements the RSX instruction (Opcode 011, User Handbook,
    /// page 3-14).
    pub fn op_rsx(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
        let j = self.regs.n.index_address();
        // If j == 0 nothing is going to happen (X₀ is always 0) but
        // we still need to make sure we raise an alarm if the memory
        // access is invalid.
        let source: Address = self.operand_address_with_optional_defer_and_index(mem)?;
        let (word, _extra) = self.fetch_operand_from_address(mem, &source)?;
        if !j.is_zero() {
            let xj: Signed18Bit = subword::right_half(word).reinterpret_as_signed();
            self.regs.set_index_register(j, &xj);
        }
        Ok(())
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
        let config = u8::from(inst.configuration());
        match config {
            0o0 | 0o10 => {
                if j != 0 {
                    // Xj is fixed at 0.
                    self.regs
                        .set_index_register(j, &operand.reinterpret_as_signed());
                }
                if config & 0o10 != 0 {
                    self.regs.flags.raise(&j);
                }
                Ok(())
            }
            0o1 => {
                if j != 0 {
                    // Xj is fixed at 0.
                    // Calculate -T
                    let t_negated = Signed18Bit::ZERO.wrapping_sub(operand.reinterpret_as_signed());
                    self.regs.set_index_register(j, &t_negated);
                }
                Ok(())
            }
            _ => Err(self.alarm_unit.always_fire(Alarm::ROUNDTUITAL(format!(
                "SKX configuration {:#o} is not implemented yet",
                inst.configuration()
            )))),
        }
    }

    /// Implements the JPX (jump on positive index) opcode (06).
    pub fn op_jpx(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
        let is_positive_address = |xj: &Signed18Bit| !xj.is_zero() && xj.is_positive();
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
    pub fn impl_op_jpx_jnx<F: FnOnce(&Signed18Bit) -> bool>(
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
            self.regs.e = subword::join_halves(
                subword::left_half(self.regs.e),
                Unsigned18Bit::from(self.regs.p),
            );
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

#[cfg(test)]
mod tests {
    use crate::exchanger::SystemConfiguration;
    use crate::memory::MetaBitChange;
    use crate::{MemoryConfiguration, MemoryUnit};
    use base::instruction::{Opcode, SymbolicInstruction};
    use base::prelude::*;

    use super::ControlUnit;

    /// Simulate some AUX instructions and return the result
    /// of the addition, and the final value in the E register.
    ///
    /// # Arguments
    ///
    /// * `j` - which index register to use
    /// * `initial` - initial value of the X-register
    /// * `addends` - items to add to `initial`
    /// * `addend_lhs` - contents for the left subword of all added items
    /// * `defer` - whether the operand should be deferred
    /// * `cfg` - the system configuration to use when adding
    fn simulate_aux(
        j: Unsigned6Bit,
        initial: Signed18Bit,
        addends: &[Signed18Bit],
        addend_lhs: Unsigned18Bit,
        defer: bool,
        cfg: SystemConfiguration,
    ) -> (Signed18Bit, Unsigned36Bit) {
        const COMPLAIN: &str = "failed to set up AUX test data";

        // Given...
        let mut control = ControlUnit::new();
        let mut mem = MemoryUnit::new(&MemoryConfiguration {
            with_u_memory: false,
        });
        control.regs.set_index_register(j, &initial);
        control.regs.f_memory[1] = cfg;
        let defer_address = OperandAddress::Deferred(Address::from(u18!(0o100)));
        const ADDEND_BASE: u32 = 0o101;
        for (offset, addend) in addends.iter().enumerate() {
            let addend_address = Address::from(
                u18!(ADDEND_BASE).wrapping_add(Unsigned18Bit::try_from(offset).expect(COMPLAIN)),
            );
            let memval = join_halves(addend_lhs, addend.reinterpret_as_unsigned());
            control
                .memory_store_without_exchange(
                    &mut mem,
                    &addend_address,
                    &memval,
                    &MetaBitChange::None,
                )
                .expect(COMPLAIN);
        }

        // When... we perform a sequence of AUX instructions
        for offset in 0..(addends.len()) {
            let operand_address = if defer {
                let pos: u32 = ADDEND_BASE + u32::try_from(offset).expect(COMPLAIN);
                let deferred = Unsigned18Bit::try_from(pos).expect(COMPLAIN);
                let ignored_lhs = u18!(0o500);
                // Set up the word at the deferred address
                control
                    .memory_store_without_exchange(
                        &mut mem,
                        &Address::from(u18!(0o100)),
                        &join_halves(ignored_lhs, deferred),
                        &MetaBitChange::None,
                    )
                    .expect(COMPLAIN);
                defer_address
            } else {
                OperandAddress::Direct(Address::from(
                    Unsigned18Bit::try_from(ADDEND_BASE + u32::try_from(offset).expect(COMPLAIN))
                        .expect(COMPLAIN),
                ))
            };
            let inst = SymbolicInstruction {
                held: false,
                configuration: Unsigned5Bit::ONE,
                opcode: Opcode::Aux,
                index: j,
                operand_address,
            };
            control
                .update_n_register(Instruction::from(&inst).bits())
                .expect(COMPLAIN);
            if let Err(e) = control.op_aux(&mut mem) {
                panic!("AUX instruction failed: {}", e);
            }
        }
        (control.regs.get_index_register(j), control.regs.e)
    }

    /// Check that AUX thinks that 0 + 1 = 1.
    #[test]
    fn op_aux_zero_plus_one_equals_one() {
        let ignored_lhs = u18!(300);
        let (sum, e) = simulate_aux(
            Unsigned6Bit::ONE, // Use register X₁
            Signed18Bit::ZERO,
            &[Signed18Bit::ONE],
            ignored_lhs,
            false,
            SystemConfiguration::from(0_u8),
        );
        assert_eq!(sum, Signed18Bit::ONE);
        assert_eq!(
            e,
            join_halves(ignored_lhs, Signed18Bit::ONE.reinterpret_as_unsigned())
        );
    }

    /// Check that AUX can correctly add negative values.
    #[test]
    fn op_aux_negative() {
        const COMPLAIN: &str = "failed to set up AUX test data";
        let ignored_lhs = u18!(503);
        let minus_three = Signed18Bit::try_from(-3).expect(COMPLAIN);
        let items_to_add = [Signed18Bit::try_from(-1).expect(COMPLAIN), minus_three];
        let (sum, e) = simulate_aux(
            Unsigned6Bit::ONE,                                // Use register X₁
            Signed18Bit::try_from(0o250077).expect(COMPLAIN), // initial value
            &items_to_add,
            ignored_lhs,
            false,
            // System configuration 0o340 uses only the right-hand
            // subword, which is how AUX behaves anyway - so this
            // should make no difference.
            SystemConfiguration::from(0o340_u8),
        );
        assert_eq!(sum, Signed18Bit::try_from(0o250073).expect(COMPLAIN));
        assert_eq!(
            e,
            join_halves(ignored_lhs, minus_three.reinterpret_as_unsigned()),
        );
    }

    /// Check that AUX applies a configuration in which only q2 is
    /// active.
    #[test]
    fn op_aux_q2_only() {
        let ignored_lhs = u18!(507);
        let items_to_add = [
            // q2 is 0o020, q1 is 0o010
            u18!(0o020_010).reinterpret_as_signed(),
        ];
        let (sum, _e) = simulate_aux(
            Unsigned6Bit::ONE,                       // Use register X₁
            u18!(0o300_555).reinterpret_as_signed(), // initial value
            &items_to_add,
            ignored_lhs,
            false,
            SystemConfiguration::from(u9!(0o750)), // 0o750: q2 only
        );
        // The sum should be formed from q2 of the initial value
        // (0o300) plus q2 of the addend (0o020), yielding 0o320.  The
        // inactive quarter (q1) should be zeroed.  This is explained
        // on page 3-22 of the Users Handbook.
        assert_eq!(sum, u18!(0o320_000).reinterpret_as_signed());
    }
}
