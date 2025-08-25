/// Diagnostic information for log messages and alarms.
///
/// The real TX-2 did not have any accompanying message to go along
/// with alarms, but the emulator does.
use std::fmt::{Display, Formatter};

use base::instruction::Instruction;
use base::prelude::{Address, SymbolicInstruction};

/// CurrentInstructionDiagnostics is only for generating debug
/// information.  They must not be used for control/execution
/// purposes.
///
/// We sometimes clone this struct in cases where we are unlikely to
/// use the cloned value (e.g. where an alarm is possible but
/// unlikely) and so a clone of this struct needs to remain cheap.
#[derive(Debug, Clone)]
pub struct CurrentInstructionDiagnostics {
    pub current_instruction: Instruction,
    pub instruction_address: Address,
}

impl Display for &CurrentInstructionDiagnostics {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        if let Ok(symbolic) = SymbolicInstruction::try_from(&self.current_instruction) {
            write!(f, "instruction {symbolic}")?;
        } else {
            write!(f, "instruction {:>012o}", self.current_instruction.bits(),)?;
        };
        write!(f, " at address {:>06o}", self.instruction_address)
    }
}

pub trait DiagnosticFetcher {
    fn diagnostics(self) -> CurrentInstructionDiagnostics;
}

impl DiagnosticFetcher for CurrentInstructionDiagnostics {
    fn diagnostics(self) -> CurrentInstructionDiagnostics {
        self
    }
}

impl DiagnosticFetcher for &CurrentInstructionDiagnostics {
    fn diagnostics(self) -> CurrentInstructionDiagnostics {
        self.clone()
    }
}
