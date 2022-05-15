//! Implementations of "Load-Store Class" opcodes
//! - LDA: [`ControlUnit::op_lda`]
//! - LDB: [`ControlUnit::op_ldb`]
//! - LDC: [`ControlUnit::op_ldc`]
//! - LDD: [`ControlUnit::op_ldd`]
//! - LDE: [`ControlUnit::op_lde`]
//! - STA: (unimplemented)
//! - STB: (unimplemented)
//! - STC: (unimplemented)
//! - STD: (unimplemented)
//! - STE: [`ControlUnit::op_ste`]
//! - EXA: (unimplemented)

use tracing::{event, Level};

use crate::alarm::Alarm;
use crate::control::{ControlUnit, MemoryUnit, OpcodeResult, UpdateE};
use crate::exchanger::exchanged_value_for_load;
use base::prelude::*;

impl ControlUnit {
    /// Implements the LDA instruction (Opcode 024, User Handbook,
    /// page 3-6).
    pub(crate) fn op_lda(&mut self, mem: &mut MemoryUnit) -> Result<OpcodeResult, Alarm> {
        let new_value = self.op_load_value(&mem.get_a_register(), mem, &UpdateE::Yes)?;
        mem.set_a_register(new_value);
        Ok(OpcodeResult::default())
    }

    /// Implements the LDB instruction (Opcode 025, User Handbook,
    /// page 3-6).
    pub(crate) fn op_ldb(&mut self, mem: &mut MemoryUnit) -> Result<OpcodeResult, Alarm> {
        let new_value = self.op_load_value(&mem.get_b_register(), mem, &UpdateE::Yes)?;
        mem.set_b_register(new_value);
        Ok(OpcodeResult::default())
    }

    /// Implements the LDC instruction (Opcode 026, User Handbook,
    /// page 3-6).
    pub(crate) fn op_ldc(&mut self, mem: &mut MemoryUnit) -> Result<OpcodeResult, Alarm> {
        let new_value = self.op_load_value(&mem.get_c_register(), mem, &UpdateE::Yes)?;
        mem.set_c_register(new_value);
        Ok(OpcodeResult::default())
    }

    /// Implements the LDD instruction (Opcode 027, User Handbook,
    /// page 3-6).
    pub(crate) fn op_ldd(&mut self, mem: &mut MemoryUnit) -> Result<OpcodeResult, Alarm> {
        let new_value = self.op_load_value(&mem.get_d_register(), mem, &UpdateE::Yes)?;
        mem.set_d_register(new_value);
        Ok(OpcodeResult::default())
    }

    /// Implements the LDE instruction (Opcode 020, User Handbook,
    /// page 3-6).
    pub(crate) fn op_lde(&mut self, mem: &mut MemoryUnit) -> Result<OpcodeResult, Alarm> {
        // LDE is a special case in that the the other instructions
        // jam the loaded memory word into E (see example 2 for LDA)
        // but LDE doesn't do this (you get the exchanged result in E
        // instead).  This is why we use UpdateE::No.
        let old_value = self.regs.e;
        let new_value = self.op_load_value(&old_value, mem, &UpdateE::No)?;
        self.regs.e = new_value;
        Ok(OpcodeResult::default())
    }

    /// Implements the STE instruction (Opcode 030, User Handbook,
    /// page 3-8).
    pub(crate) fn op_ste(&mut self, mem: &mut MemoryUnit) -> Result<OpcodeResult, Alarm> {
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
    ) -> Result<OpcodeResult, Alarm> {
        let target: Address = self.operand_address_with_optional_defer_and_index(mem)?;
        event!(
            Level::TRACE,
            "storing register value {register_value:o} at {target:o}"
        );
        self.memory_read_and_update_with_exchange(mem, &target, update_e, |_| register_value)
            .map(|()| OpcodeResult::default())
    }

    /// Implement loads as if for opcodes LD{A,B,C,D,E}.
    fn op_load_value(
        &mut self,
        existing: &Unsigned36Bit,
        mem: &mut MemoryUnit,
        update_e: &UpdateE,
    ) -> Result<Unsigned36Bit, Alarm> {
        let target: Address = self.operand_address_with_optional_defer_and_index(mem)?;
        let (memword, _extra) =
            self.fetch_operand_from_address_without_exchange(mem, &target, update_e)?;
        let exchanged = exchanged_value_for_load(&self.get_config(), &memword, existing);
        Ok(exchanged)
    }
}

#[cfg(test)]
mod tests {
    use super::super::{ControlUnit, PanicOnUnmaskedAlarm, UpdateE};
    use crate::exchanger::SystemConfiguration;
    use crate::memory::{MemoryMapped, MetaBitChange};
    use crate::{MemoryConfiguration, MemoryUnit};
    use base::prelude::*;
    use base::subword::right_half;

    #[derive(Debug)]
    enum ArithmeticUnitRegister {
        // A, B, C, D are physically in the Arithmetic Element
        A,
        B,
        C,
        D,
        // E is actually physically in the Exchange Element, but we
        // use the same test infrastructure for LDE anyway.
        E,
    }

    fn get_register_value(
        control: &ControlUnit,
        mem: &MemoryUnit,
        which: ArithmeticUnitRegister,
    ) -> Unsigned36Bit {
        use ArithmeticUnitRegister::*;
        match which {
            A => mem.get_a_register(),
            B => mem.get_b_register(),
            C => mem.get_c_register(),
            D => mem.get_d_register(),
            E => control.regs.e,
        }
    }

    fn set_up_load(
        a: Unsigned36Bit,
        b: Unsigned36Bit,
        c: Unsigned36Bit,
        d: Unsigned36Bit,
        e: Unsigned36Bit,
    ) -> (ControlUnit, MemoryUnit) {
        let mut control = ControlUnit::new(PanicOnUnmaskedAlarm::Yes);
        let mut mem = MemoryUnit::new(&MemoryConfiguration {
            with_u_memory: false,
        });
        mem.set_a_register(a);
        mem.set_b_register(b);
        mem.set_c_register(c);
        mem.set_d_register(d);
        control.regs.e = e;
        (control, mem)
    }

    /// Simulate a load instruction; return (target register, e register)
    fn simulate_load(
        final_operand_address: Unsigned18Bit,
        target_register: ArithmeticUnitRegister,
        configuration: SystemConfiguration,
        mem_word: Option<Unsigned36Bit>,
        a: Unsigned36Bit,
        b: Unsigned36Bit,
        c: Unsigned36Bit,
        d: Unsigned36Bit,
        e: Unsigned36Bit,
        j: Unsigned6Bit,
        xj: Signed18Bit,
        defer_index: Option<Signed18Bit>,
    ) -> (Unsigned36Bit, Unsigned36Bit) {
        let (mut control, mut mem) = set_up_load(a, b, c, d, e);
        if let Some(w) = mem_word {
            // Store the value to be loaded at final_operand_address.
            control
                .memory_store_without_exchange(
                    &mut mem,
                    &Address::from(final_operand_address),
                    &w,
                    &UpdateE::No,
                    &MetaBitChange::None,
                )
                .expect("simulate_load should be able to set up the final operand");
        }

        // For deferred loads, store the defer value at 0o200.  Where
        // the deferred load is indexed, compute the base address in
        // R(M) so that the final result is `final_operand_address`.
        //
        //               Address | L              | R
        // --------------------- | -              | -
        // final_operand_address | L(source)      | R(source)
        //                   200 | defer_index    | base
        //
        // base + index + Xⱼ = final_operand_address.
        // The caller specifies Xⱼ and defer_index.
        // So we set base to (final_operand_address - defer_index - Xⱼ).
        let base: Signed18Bit = final_operand_address
            .reinterpret_as_signed()
            .checked_sub(defer_index.unwrap_or(Signed18Bit::ZERO))
            .map(|x| x.checked_sub(xj))
            .flatten()
            .expect("test data caused arithmetic overflow");
        let defer: Unsigned36Bit = join_halves(
            defer_index.unwrap_or_default().reinterpret_as_unsigned(),
            base.reinterpret_as_unsigned(),
        );
        control
            .memory_store_without_exchange(
                &mut mem,
                &Address::from(u18!(0o200)),
                &defer,
                &UpdateE::No,
                &MetaBitChange::None,
            )
            .expect("simulate_load should be able to write to address 0o100");

        control.regs.f_memory[1] = configuration;

        let opcode = match target_register {
            ArithmeticUnitRegister::A => Opcode::Lda,
            ArithmeticUnitRegister::B => Opcode::Ldb,
            ArithmeticUnitRegister::C => Opcode::Ldc,
            ArithmeticUnitRegister::D => Opcode::Ldd,
            ArithmeticUnitRegister::E => Opcode::Lde,
        };
        let inst = SymbolicInstruction {
            held: false,
            configuration: Unsigned5Bit::ONE,
            opcode,
            index: j,
            operand_address: if defer_index.is_some() {
                OperandAddress::Deferred(Address::from(u18!(0o200)))
            } else {
                OperandAddress::Direct(Address::from(final_operand_address))
            },
        };
        control
            .update_n_register(Instruction::from(&inst).bits())
            .expect("should be able to set N register");

        let result = match target_register {
            ArithmeticUnitRegister::A => control.op_lda(&mut mem),
            ArithmeticUnitRegister::B => control.op_ldb(&mut mem),
            ArithmeticUnitRegister::C => control.op_ldc(&mut mem),
            ArithmeticUnitRegister::D => control.op_ldd(&mut mem),
            ArithmeticUnitRegister::E => control.op_lde(&mut mem),
        };
        dbg!(&result);
        if let Err(e) = result {
            panic!("{:?} instruction failed: {}", opcode, e);
        }
        (
            get_register_value(&control, &mem, target_register),
            control.regs.e,
        )
    }

    fn set_up_store<F>(
        mem_word: Unsigned36Bit,
        working_address: &Address,
        mut reg_init: F,
    ) -> (ControlUnit, MemoryUnit)
    where
        F: FnMut(&mut ControlUnit),
    {
        const COMPLAIN: &str = "failed to set up load/store test data";
        let mut control = ControlUnit::new(PanicOnUnmaskedAlarm::Yes);
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

    /// This test is taken from example 1 on page 3-6 of the Users Handbook.
    #[test]
    fn test_lde_example_1() {
        let input = u36!(0o444_333_222_111);
        let (output, e) = simulate_load(
            u18!(0o10000),
            ArithmeticUnitRegister::E,
            SystemConfiguration::zero(),
            Some(input),
            u36!(1),                           // a
            u36!(2),                           // b
            u36!(3),                           // c
            u36!(4),                           // d
            u36!(5),                           // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        assert_eq!(output, input);
        assert_eq!(e, input);
    }

    /// This test is taken from example 2 on page 3-6 of the Users
    /// Handbook, using register E.
    #[test]
    fn test_lde_example_2() {
        let input = u36!(0o404_303_202_101);
        let orig_e = u36!(0o545_535_525_515);
        let (new_e, e) = simulate_load(
            u18!(0o10000),
            ArithmeticUnitRegister::E,
            SystemConfiguration::from(u9!(0o340)), // 340 is standard configuration 1
            Some(input),
            u36!(0o141_131_121_111),           // a
            u36!(0o242_232_222_212),           // b
            u36!(0o343_333_323_313),           // c
            u36!(0o444_434_424_414),           // d
            orig_e,                            // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        // L(E) is unchanged, R(E) is loaded from the memory word.
        assert_eq!(new_e, u36!(0o545_535_202_101));
        assert_eq!(e, new_e);
    }

    /// This test is taken from example 2 on page 3-6 of the Users
    /// Handbook, using register A.
    #[test]
    fn test_lda_example_2() {
        let input = u36!(0o404_303_202_101);
        let orig_e = u36!(0o545_535_525_515);
        let (new_a, e) = simulate_load(
            u18!(0o10000),
            ArithmeticUnitRegister::A,
            SystemConfiguration::from(u9!(0o340)), // 340 is standard configuration 1
            Some(input),
            u36!(0o141_131_121_111),           // a
            u36!(0o242_232_222_212),           // b
            u36!(0o343_333_323_313),           // c
            u36!(0o444_434_424_414),           // d
            orig_e,                            // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        // L(A) is unchanged, R(A) is loaded from R(memory word).
        // E is set to the value of the memory word.
        assert_eq!(new_a, u36!(0o141_131_202_101));
        assert_eq!(e, input);
    }

    /// This test is taken from example 3 on page 3-6 of the Users
    /// Handbook, using register C.
    #[test]
    fn test_ldc_example_3() {
        // Notice that R(input) has the MSB set, i.e. it is negative.
        let input = u36!(0o404_303_402_101);
        let orig_e = u36!(0o545_535_525_515);
        let (new_c, e) = simulate_load(
            u18!(0o10000),
            ArithmeticUnitRegister::C,
            SystemConfiguration::from(u9!(0o140)), // 140 is standard configuration 11
            Some(input),
            u36!(0o141_131_121_111),           // a
            u36!(0o242_232_222_212),           // b
            u36!(0o343_333_323_313),           // c
            u36!(0o444_434_424_414),           // d
            orig_e,                            // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        // R(mem_word) ==> R(C)
        // sign_bit(R(mem_word)) ==> L(C)
        // mem_word ==> E
        assert_eq!(new_c, u36!(0o777_777_402_101));
        assert_eq!(e, input);
    }

    /// This test is taken from example 4 on page 3-6 of the Users
    /// Handbook, using register D.
    #[test]
    fn test_ldd_example_4() {
        let input = u36!(0o404_303_202_101);
        let orig_e = u36!(0o545_535_525_515);
        let orig_d = u36!(0o444_434_424_414);
        let (new_d, new_e) = simulate_load(
            u18!(0o10000),
            ArithmeticUnitRegister::D,
            SystemConfiguration::from(u9!(0o342)), // 342 is standard configuration 2
            Some(input),
            u36!(0o141_131_121_111),           // a
            u36!(0o242_232_222_212),           // b
            u36!(0o343_333_323_313),           // c
            orig_d,                            // d
            orig_e,                            // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        assert_eq!(new_d, u36!(0o444_434_404_303)); // D is set to L(orig_d)|L(input).
        assert_eq!(new_e, input); // E is set to input
    }

    /// This test is taken from example 5 on page 3-7 of the Users
    /// Handbook, using register B.
    ///
    /// The instruction is ²LDB₀ B, where B is the memory address of
    /// the B register itself.
    #[test]
    fn test_ldb_example_5() {
        // The input is actually register B.
        let b_register_address: Unsigned18Bit = u18!(0o0377605);
        let orig_b = u36!(0o242_232_222_212);
        let (new_b, new_e) = simulate_load(
            b_register_address,
            ArithmeticUnitRegister::B,
            SystemConfiguration::from(u9!(0o342)), // 342 is standard configuration 2
            None,
            u36!(0o141_131_121_111),           // a
            orig_b,                            // b
            u36!(0o343_333_323_313),           // c
            u36!(0o444_434_424_414),           // d
            u36!(0o545_535_525_515),           // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        // Register B ends up as L(orig_b)|R(orig_b).
        assert_eq!(new_b, u36!(0o242_232_242_232));
        assert_eq!(new_e, orig_b); // E is set to input
    }

    /// This test is taken from example 6 on page 3-7 of the Users
    /// Handbook, using register D.
    #[test]
    fn test_ldd_example_6() {
        // Note that the sign bit of Q4 of the input is set.
        let input = u36!(0o404_303_202_101);
        let orig_e = u36!(0o545_535_525_515);
        let orig_d = u36!(0o444_434_424_414);
        let (new_d, new_e) = simulate_load(
            u18!(0o10000),
            ArithmeticUnitRegister::D,
            SystemConfiguration::from(u9!(0o163)), // 163 is standard configuration 16
            Some(input),
            u36!(0o141_131_121_111),           // a
            u36!(0o242_232_222_212),           // b
            u36!(0o343_333_323_313),           // c
            orig_d,                            // d
            orig_e,                            // e
            u6!(1),                            // j
            u18!(0o4).reinterpret_as_signed(), // Xⱼ
            None,                              // No defer_index
        );
        // The result in D is that Q1 is set to Q4(input) and the
        // remaining quarters are filled with sign-extension from
        // Q4(input) (this sign bit is 1).
        assert_eq!(new_d, u36!(0o777_777_777_404), "new value for D is wrong");
        assert_eq!(new_e, input, "new value for E is wrong"); // E is set to input
    }

    #[test]
    fn test_ste_example_1() {
        let input = u36!(0o004_003_002_001);
        let working_address: Address = Address::from(u18!(0o100));
        let (mut control, mut mem) =
            set_up_store(u36!(0o444_333_222_111), &working_address, |control| {
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
        let (mut control, mut mem) =
            set_up_store(initial_value_at_100, &working_address, |control| {
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
