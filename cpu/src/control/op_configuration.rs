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
use crate::memory::MemoryUnit;

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
        for (quarter_number, cfg_value) in subword::quarters(word).iter().enumerate() {
            self.regs.f_memory[c + quarter_number] = (*cfg_value).into();
        }
        Ok(())
    }
}
