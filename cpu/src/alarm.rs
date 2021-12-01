use std::error::Error;
use std::fmt::{self, Display, Formatter};

use base::instruction::Instruction;
use base::prelude::*;

// Alarms from User's Handbook section 5-2.2
#[derive(Debug)]
pub enum Alarm {
    PSAL(u32, String),                        // Program counter set to illegal address
    OCSAL(Instruction, String),               // Illegal instruction was read into N register
    QSAL(Instruction, Unsigned36Bit, String), // Q register (i.e. data fetch address) is set to illegal address
    ROUNDTUITAL(String),                      // Something is not implemented
    // I/O Alarm in IOS instruction; device broken/maintenance/nonexistent.
    IOSAL {
        unit: Unsigned6Bit,
        operand: Option<Unsigned18Bit>,
        message: String,
    },

    // Missed-data alarm.
    MISAL {
        unit: Unsigned6Bit,
    }, // Program too slow for I/O device.
}

impl Display for Alarm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Alarm::*;
        f.write_str("ALARM: ")?;
        match self {
            QSAL(instruction, address, msg) => {
                write!(
		    f,
		    "QSAL: during execution of instruction {:?}, memory access to {:>013o} failed: {}",
		    instruction,
		    address,
		    msg,
		)
            }
            PSAL(address, msg) => {
                write!(
                    f,
                    "PSAL: P register set to illegal address {:>013o}: {}",
                    address, msg
                )
            }
            OCSAL(inst, msg) => {
                write!(
                    f,
                    "OCSAL: N register set to invalid instruction {:?}: {}",
                    inst, msg
                )
            }
            ROUNDTUITAL(msg) => {
                write!(
                    f,
                    "ROUNDTUITAL: the program used a feature not supported in the emulator: {}",
                    msg
                )
            }

            IOSAL {
                unit,
                operand,
                message,
            } => {
                write!(f, "IOSAL: I/O alarm during operation on unit {}", unit,)?;
                if let Some(oper) = operand {
                    write!(f, " with operand {}", oper)?;
                }
                write!(f, ": {}", message)
            }
            MISAL { unit } => {
                write!(f, "MISAL: program too slow; missed data on unit {}", unit,)
            }
        }
    }
}

impl Error for Alarm {}

// Alarm conditions we expect to use in the emulator but
// which are not in use yet:
// SYAL1,                       // Sync alarm 1 (see User Handbook page 5-21)
// SYAL2,                       // Sync alarm 2 (see User Handbook page 5-21)

// Alarm enumerators we don't expect to use:
//
// MPAL,		     // data parity error (in STUV)
// NPAL,		     // instruction parity error (in STUV)
// XPAL,		     // parity error in X-memory
// FPAL,		     // parity error in F-memory
// TSAL,		     // voltage issue; can't happen in an emulator.
// USAL,                     // voltage issue; can't happen in an emulator.
// Mouse-trap
