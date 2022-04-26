//! Implementations of "Load-Store Class" opcodes
//! - LDA: (unimplemented)
//! - LDB: (unimplemented)
//! - LDC: (unimplemented)
//! - LDD: (unimplemented)
//! - LDE: (unimplemented)
//! - STA: (unimplemented)
//! - STB: (unimplemented)
//! - STC: (unimplemented)
//! - STD: (unimplemented)
//! - STE: [`ControlUnit::op_ste`]
//! - EXA: (unimplemented)

use crate::alarm::Alarm;
use crate::control::{ControlUnit, MemoryUnit, UpdateE};
use base::prelude::*;

impl ControlUnit {
    /// Implements the STE instruction (Opcode 030, User Handbook,
    /// page 3-8).
    pub fn op_ste(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
        // STE is a special case in that it does not itself modify the
        // E register.  See paragraph 1 on page 3-8 of the Users
        // Handbook.
        self.op_store_ae_register(self.regs.e, mem, &UpdateE::No)
    }

    /// Implement opcodes ST{A,B,C,D,E}.
    fn op_store_ae_register(
        &mut self,
        register_value: Unsigned36Bit,
        mem: &mut MemoryUnit,
        update_e: &UpdateE,
    ) -> Result<(), Alarm> {
        let target: Address = self.operand_address_with_optional_defer_and_index(mem)?;
        self.memory_read_and_update_with_exchange(mem, &target, update_e, |_| register_value)
    }
}

#[cfg(test)]
mod tests {
    use super::{ControlUnit, UpdateE};
    use crate::exchanger::SystemConfiguration;
    use crate::memory::{MemoryMapped, MetaBitChange};
    use crate::{MemoryConfiguration, MemoryUnit};
    use base::prelude::*;
    use base::subword::right_half;

    fn set_up<F>(
        mem_word: Unsigned36Bit,
        working_address: &Address,
        mut reg_init: F,
    ) -> (ControlUnit, MemoryUnit)
    where
        F: FnMut(&mut ControlUnit),
    {
        const COMPLAIN: &str = "failed to set up load/store test data";
        let mut control = ControlUnit::new();
        let mut mem = MemoryUnit::new(&MemoryConfiguration {
            with_u_memory: false,
        });
        control
            .memory_store_without_exchange(
                &mut mem,
                &working_address,
                &mem_word,
                &UpdateE::No,
                &MetaBitChange::None,
            )
            .expect(COMPLAIN);
        reg_init(&mut control);
        (control, mem)
    }

    fn simulate_store(
        control: &mut ControlUnit,
        mem: &mut MemoryUnit,
        working_address: &Address,
        j: Unsigned6Bit,
        opcode: Opcode,
        defer: bool,
        configuration: SystemConfiguration,
    ) -> (Unsigned36Bit, Unsigned36Bit) {
        let complain = format!("failed to execute store instruction {:?}", opcode);
        control.regs.f_memory[1] = configuration;
        let inst = SymbolicInstruction {
            held: false,
            configuration: Unsigned5Bit::ONE,
            opcode,
            index: j,
            operand_address: if defer {
                todo!("defer is not yet implemented");
            } else {
                OperandAddress::Direct(*working_address)
            },
        };
        control
            .update_n_register(Instruction::from(&inst).bits())
            .expect(&complain);
        let f = match opcode {
            Opcode::Ste => ControlUnit::op_ste,
            _ => {
                panic!("opcode {:?} is not yet supported", opcode);
            }
        };
        dbg!(&control.regs.e);
        dbg!(&control.regs.f_memory[1]);
        dbg!(&mem.s_memory[0o100]);
        if let Err(e) = f(control, mem) {
            panic!("{:?} instruction failed: {}", opcode, e);
        }
        match mem.fetch(working_address, &MetaBitChange::None) {
            Ok((stored, _)) => (stored, control.regs.e),
            Err(e) => {
                panic!("unable to retrieve the stored word: {}", e);
            }
        }
    }

    #[test]
    fn test_ste_example_1() {
        let input = u36!(0o004_003_002_001);
        let working_address: Address = Address::from(u18!(0o100));
        let (mut control, mut mem) = set_up(u36!(0o444_333_222_111), &working_address, |control| {
            control.regs.e = input;
        });
        // The instruction actually uses System Configuration number
        // 1, but we put Unsigned9Bit::ZERO in register F₁.
        let (result, _e) = simulate_store(
            &mut control,
            &mut mem,
            &working_address,
            Unsigned6Bit::ZERO, // no indexing
            Opcode::Ste,
            false,
            SystemConfiguration::from(Unsigned9Bit::ZERO),
        );
        assert_eq!(input, result);
    }

    /// This test resembles example 3 on page 3-8 of the Users
    /// Handbook.
    #[test]
    fn test_ste_example_3() {
        let initial_value_at_100 = u36!(0o004_003_002_001);
        let initial_e = u36!(0o444_333_222_111);
        let working_address: Address = Address::from(u18!(0o100));
        let (mut control, mut mem) = set_up(initial_value_at_100, &working_address, |control| {
            control.regs.e = initial_e;
        });
        dbg!(&control.regs.e);

        // The instruction actually uses System Configuration number
        // 1, but we put 0342 (which is the value normally in F₂) in
        // register F₁.  This gives the effect of `²STE₀ 100`.
        //
        // This configuration loads R(E) into L(100).  R(100) is unchanged.
        let (result, e) = simulate_store(
            &mut control,
            &mut mem,
            &working_address,
            Unsigned6Bit::ZERO, // no indexing
            Opcode::Ste,
            false,
            // This is configuration 2.
            SystemConfiguration::from(u9!(0o342)),
        );
        dbg!(&control.regs.e);
        // The E register should still hold the original value
        // (0o004_003_002_001).
        assert_eq!(e, initial_e, "E register should be unchanged");
        // R(E) (which is 0o222_1111) should have been loaded into
        // L(100) and R(100) (which is 0o002_001) should be unchanged.
        let expected = u36!(0o222_111_002_001);
        let expected2 = join_halves(right_half(initial_e), right_half(initial_value_at_100));
        assert_eq!(expected, expected2, "test is internally inconsistent");
        assert_eq!(result, expected, "incorrect value stored at 0o100");
    }
}
