use base::prelude::*;
use base::subword;

use crate::alarm::{Alarm, BadMemOp};
use crate::control::{ControlUnit, OpcodeResult, ProgramCounterChange};
use crate::memory::{BitChange, MemoryMapped, MemoryOpFailure, MemoryUnit, WordChange};

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
    pub fn op_jmp(&mut self) -> OpcodeResult {
        // For JMP the configuration field in the instruction controls
        // the behaviour of the instruction, without involving
        // a load from F-memory.
        fn nonzero(value: Unsigned5Bit) -> bool {
            !value.is_zero()
        }
        let cf = self.regs.n.configuration();
        let save_q = nonzero(cf & 0b01000_u8);
        let savep_e = nonzero(cf & 0b00100_u8);
        let savep_ix = nonzero(cf & 0b00010_u8);
        let indexed = nonzero(cf & 0b00001_u8);
        let j = self.regs.n.index_address();
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

        let physical: Address = match self.regs.n.operand_address() {
            OperandAddress::Deferred(_) => {
                // TODO: I don't know whether this is allowed or
                // not, but if we disallow this for now, we can
                // use any resulting error to identify cases where
                // this is in fact used.
                self.alarm_unit.fire_if_not_masked(Alarm::PSAL(
                    u32::from(self.regs.n.operand_address_and_defer_bit()),
                    format!(
                        "JMP target has deferred address {:#o}",
                        self.regs.n.operand_address()
                    ),
                ))?;
                // If deferred addressing is allowed for JMP, we will
                // need to implement it.  It's not yet implemented.
                return Err(self.alarm_unit.always_fire(Alarm::ROUNDTUITAL(
                    "deferred JMP is not yet implemented".to_string(),
                )));
            }
            OperandAddress::Direct(phys) => phys,
        };
        let new_pc: Address = if indexed {
            physical.index_by(self.regs.get_index_register(j))
        } else {
            physical
        };

        // Now that we have used Xj, we can overwrite the original
        // value if we need to save P in it.
        if savep_ix && j != 0 {
            let p = self.regs.p;
            self.regs.set_index_register_from_address(j, &p);
        }

        if nonzero(cf & 0b10000_u8) {
            println!("dismissing current sequence");
            self.dismiss_unless_held("JMP has dismiss bit set in config syllable");
        } else {
            println!("not current sequence");
        }
        Ok(Some(ProgramCounterChange::Jump(new_pc)))
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
    pub fn op_skm(&mut self, mem: &mut MemoryUnit) -> OpcodeResult {
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
            Err(MemoryOpFailure::NotMapped(addr)) => {
                self.alarm_unit.fire_if_not_masked(Alarm::QSAL(
                    self.regs.n,
                    BadMemOp::Write(target.into()),
                    format!(
                        "SKM instruction attempted to access address {:o} but it is not mapped",
                        addr,
                    ),
                ))?;
                // The alarm is masked.  We turn the memory mutation into a no-op.
                return Ok(None);
            }
            Err(MemoryOpFailure::ReadOnly(_, _)) => {
                self.alarm_unit.fire_if_not_masked(
                    Alarm::QSAL(
			self.regs.n,
			BadMemOp::Write(target.into()),
			format!(
			    "SKM instruction attempted to modify (instruction configuration={:o}) a read-only location {:o}",
			    cf,
			    target,
                    ),
                    ))?;
                // The alarm is masked.  We turn the memory mutation into a no-op.
                return Ok(None);
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
        Ok(if skip {
            Some(ProgramCounterChange::CounterUpdate)
        } else {
            None
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::control::ProgramCounterChange;
    use crate::{ControlUnit, MemoryConfiguration, MemoryUnit};
    use base::instruction::{Opcode, SymbolicInstruction};
    use base::prelude::*;

    fn setup(
        j: Unsigned6Bit,
        initial: Signed18Bit,
        e: Unsigned36Bit,
        p: Address,
        q: Address,
    ) -> (ControlUnit, MemoryUnit) {
        let mut control = ControlUnit::new();
        let mem = MemoryUnit::new(&MemoryConfiguration {
            with_u_memory: false,
        });
        if j == 0 {
            assert_eq!(initial, 0, "Cannot set X₀ to a nonzero value");
        } else {
            control.regs.set_index_register(j, &initial);
        }
        control.regs.e = e;
        control.regs.p = p;
        control.regs.q = q;
        control.regs.k = Some(Unsigned6Bit::ZERO);
        control.regs.flags.lower_all();
        control.regs.flags.raise(&SequenceNumber::ZERO);
        (control, mem)
    }

    /// Simulate a JMP instruction; return (destination, Xj, E, dismissed).
    fn simulate_jmp(
        j: Unsigned6Bit,
        initial: Signed18Bit,
        e: Unsigned36Bit,
        p: Address,
        q: Address,
        inst: &SymbolicInstruction,
    ) -> (Address, Signed18Bit, Unsigned36Bit, bool) {
        const COMPLAIN: &str = "failed to set up JMP test data";
        let (mut control, _mem) = setup(j, initial, e, p, q);
        control
            .update_n_register(Instruction::from(inst).bits())
            .expect(COMPLAIN);
        match control.op_jmp() {
            Err(e) => {
                panic!("JMP instruction failed: {}", e);
            }
            Ok(Some(ProgramCounterChange::Jump(to))) => {
                let xj = control.regs.get_index_register(j);
                let dismissed =
                    !dbg!(dbg!(control.regs.flags).current_flag_state(&SequenceNumber::ZERO));
                (to, xj, control.regs.e, dismissed)
            }
            Ok(other) => {
                panic!("JMP didn't jump: {:?}", other);
            }
        }
    }

    /// This test is based on example 1 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_1_jmp() {
        let expected_target = Address::from(u18!(0o3733));
        let orig_xj = Signed18Bit::from(20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),
            orig_xj,
            orig_e,
            Address::from(u18!(0o1000)),
            Address::from(u18!(0o2777)),
            &SymbolicInstruction {
                held: false,
                configuration: Unsigned5Bit::ZERO, // plain JMP
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(expected_target),
            },
        );
        // ⁰JMP₁ ignores the index bits (as the least significant bit
        // of the configuration syllable is unset).
        assert_eq!(target, expected_target);
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, orig_e); // unaffected
        assert!(!dismissed);
    }

    /// This test is based on example 2 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_2_brc() {
        let target_base = Address::from(u18!(0o3702));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),
            orig_xj,
            orig_e,
            Address::from(u18!(0o1000)), // p
            Address::from(u18!(0o2777)), // q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(1), // BRC
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ¹JMP₁ is an indexed jump.
        assert_eq!(target, Address::from(u18!(0o3722)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, orig_e); // unaffected
        assert!(!dismissed);
    }

    /// This test is based on example 3 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_3_jps() {
        let target_base = Address::from(u18!(0o3702));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),
            orig_xj,
            orig_e,
            Address::from(u18!(0o1000)), // p
            Address::from(u18!(0o2777)), // q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(2), // JPS ("jump and save")
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ²JMP₁ saves #+1 in X₁.
        assert_eq!(target, target_base);
        assert_eq!(xj, u18!(0o1000).reinterpret_as_signed()); // changed
        assert_eq!(e, orig_e); // unaffected
        assert!(!dismissed);
    }

    /// This test is based on example 4 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_4_brs() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                      // j
            orig_xj,                     // Xj
            orig_e,                      // E
            Address::from(u18!(0o200)),  // P
            Address::from(u18!(0o2777)), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(3), // BRS ("branch and save")
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ³JMP₁ saves #+1 in X₁ and is an indexed (by X₁) jump.
        let expected_target = target_base.index_by(orig_xj);
        assert_eq!(target, expected_target);
        assert_eq!(xj, u18!(0o200).reinterpret_as_signed()); // changed (saved P)
        assert_eq!(e, orig_e); // unaffected
        assert!(!dismissed);
    }

    /// This test is based on example 5 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_5() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                      // j
            orig_xj,                     // Xj
            orig_e,                      // E
            Address::from(u18!(0o200)),  // P
            Address::from(u18!(0o2777)), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(4),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ⁴JMP₁ saves P in R(E).
        assert_eq!(target, target_base);
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, join_halves(left_half(orig_e), u18!(0o200))); // saved #+1
        assert!(!dismissed);
    }

    /// This test is based on example 6 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_6_brc() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                      // j
            orig_xj,                     // Xj
            orig_e,                      // E
            Address::from(u18!(0o200)),  // P
            Address::from(u18!(0o2777)), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(5), // BRC
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ⁵JMP₁ saves P in R(E) and is an indexed jump
        assert_eq!(target, Address::from(u18!(0o3322)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, join_halves(left_half(orig_e), u18!(0o200))); // saved #+1
        assert!(!dismissed);
    }

    /// This test is based on example 7 for JMP on page 3-30 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_7_jps() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                      // j
            orig_xj,                     // Xj
            orig_e,                      // E
            Address::from(u18!(0o200)),  // P
            Address::from(u18!(0o2777)), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(6), // JPS ("jump and save")
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ⁶JMP₁ saves P (=#+1) in both R(E) and in X₁.
        assert_eq!(target, Address::from(u18!(0o3302)));
        assert_eq!(xj, u18!(0o200).reinterpret_as_signed()); // saved P
        assert_eq!(e, join_halves(left_half(orig_e), u18!(0o200))); // saved P
        assert!(!dismissed);
    }

    /// This test is based on example 8 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_8_brs() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                      // j
            orig_xj,                     // Xj
            orig_e,                      // E
            Address::from(u18!(0o200)),  // P
            Address::from(u18!(0o2777)), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(7), // BRS ("branch and save")
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ⁷JMP₁ is an indexed jump and saves P (=#+1) in both R(E)
        // and in X₁.
        assert_eq!(target, Address::from(u18!(0o3322)));
        assert_eq!(xj, u18!(0o200).reinterpret_as_signed()); // saved P
        assert_eq!(e, join_halves(left_half(orig_e), u18!(0o200))); // saved P
        assert!(!dismissed);
    }

    /// This test is based on example 9 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_9() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);

        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                     // j
            orig_xj,                    // Xj
            orig_e,                     // E
            Address::from(u18!(0o200)), // P
            Address::from(orig_q),      // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o10),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ¹⁰JMP₁ saves the location of the last memory reference
        // (that is, the value of the Q register) in L(E).
        assert_eq!(target, Address::from(u18!(0o3302)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, join_halves(orig_q, right_half(orig_e))); // saved Q
        assert!(!dismissed);
    }

    /// This test is based on example 10 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_10_jpq() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o14), // JPQ
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ¹⁴JMP₁ saves the location of the last memory reference
        // (that is, the value of the Q register) in L(E), the value
        // of P in R(E).
        assert_eq!(target, Address::from(u18!(0o3302)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, join_halves(orig_q, orig_p)); // saved Q, P
        assert!(!dismissed);
    }

    /// This test is based on example 11 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_11_bpq() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o15), // BPQ
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ¹⁵JMP₁ saves the location of the last memory reference
        // (that is, the value of the Q register) in L(E), the value
        // of P in R(E), and it is an indexed jump.
        assert_eq!(target, Address::from(u18!(0o3322)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, join_halves(orig_q, orig_p)); // saved Q, P
        assert!(!dismissed);
    }

    /// This test is based on example 12 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_12_jes() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o16),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ¹⁶JMP₁ saves P in R(E) and Xj, and saves Q in L(E).
        assert_eq!(target, Address::from(u18!(0o3302)));
        assert_eq!(xj, orig_p.reinterpret_as_signed()); // saved P
        assert_eq!(e, join_halves(orig_q, orig_p)); // saved P, Q
        assert!(!dismissed);
    }

    /// This test is based on example 13 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_13() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o20),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ²⁰JMP₁ is jump, dismiss (no saves, not indexed).
        assert_eq!(target, Address::from(u18!(0o3302)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, orig_e); // unaffected
        assert!(dismissed); // dismiss current sequence
    }

    /// This test is based on example 14 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_14() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o21),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ²¹JMP₁ is indexed jump, dismiss (no saves).
        assert_eq!(target, Address::from(u18!(0o3322)));
        assert_eq!(xj, orig_xj); // unaffected
        assert_eq!(e, orig_e); // unaffected
        assert!(dismissed); // dismiss current sequence
    }

    /// This test is based on example 15 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_15() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o22),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ²²JMP₁ is jump, save P in Xⱼ, dismiss (not indexed).
        assert_eq!(target, Address::from(u18!(0o3302)));
        assert_eq!(xj, orig_p.reinterpret_as_signed()); // P is saved in Xⱼ.
        assert_eq!(e, orig_e); // unaffected
        assert!(dismissed); // dismiss current sequence
    }

    /// This test is based on example 16 for JMP on page 3-31 of the
    /// Users Handbook.
    #[test]
    fn test_jmp_example_16() {
        let target_base = Address::from(u18!(0o3302));
        let orig_xj = Signed18Bit::from(0o20_i8);
        let orig_e = u36!(0o606_202_333_123);
        let orig_q = u18!(0o2777);
        let orig_p = u18!(0o200);
        let (target, xj, e, dismissed) = simulate_jmp(
            u6!(1),                // j
            orig_xj,               // Xj
            orig_e,                // E
            Address::from(orig_p), // P
            Address::from(orig_q), // Q
            &SymbolicInstruction {
                held: false,
                configuration: u5!(0o23),
                opcode: Opcode::Jmp,
                index: u6!(1),
                operand_address: OperandAddress::Direct(target_base),
            },
        );
        // ²³JMP₁ is indexed jump, save P in Xⱼ, dismiss.
        assert_eq!(target, Address::from(u18!(0o3322)));
        assert_eq!(xj, orig_p.reinterpret_as_signed()); // P is saved in Xⱼ.
        assert_eq!(e, orig_e); // unaffected
        assert!(dismissed); // dismiss current sequence
    }
}
