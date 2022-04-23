//! Implementations of "Configuration Memory Class" opcodes
//!
//! - SPF (unimplemented)
//! - SPG: [`ControlUnit::op_spg`]
//! - FLF (unimplemented)
//! - FLG (unimplemented)

use base::prelude::*;
use base::subword;

use crate::alarm::Alarm;
use crate::control::ControlUnit;
use crate::exchanger::SystemConfiguration;
use crate::memory::MemoryUnit;

use tracing::{event, Level};

/// ## "Configuration Memory Class" opcodes
///
/// - SPF (unimplemented)
/// - SPG: [`ControlUnit::op_spg`]
/// - FLF (unimplemented)
/// - FLG (unimplemented)
///
impl ControlUnit {
    /// Implements the SPG instruction.
    pub fn op_spg(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
        let c = usize::from(self.regs.n.configuration());
        let target = self.operand_address_with_optional_defer_and_index(mem)?;
        let (word, _meta) = self.fetch_operand_from_address(mem, &target)?;
        for (quarter_number, cfg_value) in subword::quarters(word).iter().rev().enumerate() {
            let pos = c + quarter_number;
            let newvalue = (*cfg_value).into();
            if pos != 0 {
                self.regs.f_memory[pos] = newvalue;
            } else if newvalue != SystemConfiguration::zero() {
                event!(
                    Level::WARN,
                    "Ignoring attempt to set system configuration 0 to {:?}",
                    newvalue
                );
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

    fn cfg_loc(n: u8) -> Unsigned5Bit {
        Unsigned5Bit::try_from(n).expect("bad test data; config location out of range")
    }

    fn cfg_val(n: u16) -> SystemConfiguration {
        SystemConfiguration::from(Unsigned9Bit::try_from(n).expect("bad system config number"))
    }

    /// Simulate an SPG instruction and return the configuration
    /// values that got loaded, and the value held in the E register.
    fn simulate_spg(
        cfg: u8,
        configdata: Unsigned36Bit,
    ) -> ([SystemConfiguration; 4], Unsigned36Bit) {
        const COMPLAIN: &str = "failed to set up test data";

        // Given... values for f-memory data loaded into memory
        let mut control = ControlUnit::new();
        let mut mem = MemoryUnit::new(&MemoryConfiguration {
            with_u_memory: false,
        });
        let configdata_address = Address::from(u18!(0o100));
        control
            .memory_store_without_exchange(
                &mut mem,
                &configdata_address,
                &configdata,
                &MetaBitChange::None,
            )
            .expect(COMPLAIN);

        // When... we perform an SPG instruction
        // inst encodes the instruction ⁰⁴SPG configdata_address.
        let inst = SymbolicInstruction {
            held: false,
            configuration: Unsigned5Bit::try_from(cfg).expect(COMPLAIN),
            opcode: Opcode::Spg,
            index: Unsigned6Bit::ZERO,
            operand_address: OperandAddress::Direct(configdata_address),
        };
        control
            .update_n_register(Instruction::from(&inst).bits())
            .expect(COMPLAIN);
        if let Err(e) = control.op_spg(&mut mem) {
            panic!("SPG instruction failed: {}", e);
        }

        (
            [
                control.regs.get_f_mem(cfg_loc(cfg)),
                control.regs.get_f_mem(cfg_loc(cfg + 1)),
                control.regs.get_f_mem(cfg_loc(cfg + 2)),
                control.regs.get_f_mem(cfg_loc(cfg + 3)),
            ],
            control.regs.e,
        )
    }

    /// Verify that the SPG instruction loads the data into F-memory
    /// in the correct order.
    #[test]
    fn op_spg_ordering() {
        // The value 0o_410763_762761 is taken from Plugboard B,
        // address 0o3777741.  This is what actually gets loaded into
        // these system configuration slots by the boot code.
        let word = u36!(0o_410763_762761);
        let (values, e) = simulate_spg(4, word);

        // For a word DDD_CCC_BBB_AAA loaded with ⁿSPG,
        // F-memory location n should be loaded with AAA.
        assert_eq!(values[0], cfg_val(0o761));
        // F-memory location n+1 should be loaded with BBB.
        assert_eq!(values[1], cfg_val(0o762));
        // F-memory location n+2 should be loaded with CCC.
        assert_eq!(values[2], cfg_val(0o763));
        // F-memory location n+3 should be loaded with DDD.
        assert_eq!(values[3], cfg_val(0o410));

        assert_eq!(e, word, "E register was unaffected");
    }

    /// Verify that the SPG instruction will not modify system
    /// configuration value 0.  I don't recall any mention in the
    /// documentation of any alarm when an attempt is made to set slot
    /// 0, so I assume this is just ignored.
    #[test]
    fn op_spg_zero_invariant() {
        // The value 0o_410763_762761 happens to be taken from
        // Plugboard B, address 0o3777741.  But the key point is that
        // none of the quarters of the word are zero.
        let word = u36!(0o_410763_762761);
        let (values, e) = simulate_spg(0, word);

        // For a word DDD_CCC_BBB_AAA loaded with ⁿSPG,
        // F-memory location 0 should be unchanged
        assert_eq!(values[0], cfg_val(0o0));
        // F-memory location 1 should be loaded with BBB.
        assert_eq!(values[1], cfg_val(0o762));
        // F-memory location 2 should be loaded with CCC.
        assert_eq!(values[2], cfg_val(0o763));
        // F-memory location 3 should be loaded with DDD.
        assert_eq!(values[3], cfg_val(0o410));

        // SPG should set the E register.
        assert_eq!(e, word, "E register was unaffected");
    }
}
