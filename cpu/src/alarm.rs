use std::error::Error;
use std::fmt::{self, Display, Formatter};

use base::instruction::Instruction;
use base::prelude::*;

#[derive(Debug)]
pub enum BadMemOp {
    Read(Unsigned36Bit),
    Write(Unsigned36Bit),
}

impl Display for BadMemOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BadMemOp::Read(addr) => write!(f, "memory read from {:>013o} failed", addr),
            BadMemOp::Write(addr) => write!(f, "memory write to {:>013o} failed", addr),
        }
    }
}

// Alarms from User's Handbook section 5-2.2
#[derive(Debug)]
pub enum Alarm {
    PSAL(u32, String),                   // Program counter set to illegal address
    OCSAL(Instruction, String),          // Illegal instruction was read into N register
    QSAL(Instruction, BadMemOp, String), // Q register (i.e. data fetch address) is set to illegal address
    ROUNDTUITAL(String),                 // Something is not implemented
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

    // There is a bug in the simulator.
    BUGAL {
        instr: Option<Instruction>,
        message: String,
    },

    // Loop in deferred addressing (detection of this is not a feature
    // of the TX-2).
    DEFERLOOPAL {
        /// address is some address within the loop.
        address: Unsigned18Bit,
    },
}

impl Display for Alarm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Alarm::*;
        f.write_str("ALARM: ")?;
        match self {
            QSAL(instruction, op, msg) => {
                write!(
                    f,
                    "QSAL: during execution of instruction {:?}, {}: {}",
                    instruction, op, msg,
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

            BUGAL { instr, message } => {
                write!(
                    f,
                    "BUGAL: encountered simulator bug during execution of instruction {:?}: {}",
                    instr, message,
                )
            }
            DEFERLOOPAL { address } => {
                write!(
                    f,
                    "DEFERLOOPAL: infinite loop in deferred address at {}",
                    address,
                )
            }
        }
    }
}

impl Error for Alarm {}

/// The TX-2 can "mask" some alarms, and whether or not this is
/// happening is controlled by the AlarmUnit.
#[derive(Debug, Default)]
pub struct AlarmUnit {
    mask_psal: bool,
    mask_ocsal: bool,
    mask_qsal: bool,
    mask_iosal: bool,
    mask_misal: bool,
    // BUGAL cannot be masked
    // DEFERLOOPAL cannot be masked.
}

impl AlarmUnit {
    pub fn new() -> AlarmUnit {
        AlarmUnit::default()
    }

    fn is_never_masked(alarm_instance: &Alarm) -> bool {
        matches!(
            alarm_instance,
            Alarm::BUGAL { .. } | Alarm::DEFERLOOPAL { .. } | Alarm::ROUNDTUITAL(_)
        )
    }

    fn is_masked(&self, alarm_instance: &Alarm) -> bool {
        let masked = match &alarm_instance {
            Alarm::PSAL(_, _) => self.mask_psal,
            Alarm::OCSAL(_, _) => self.mask_ocsal,
            Alarm::QSAL(_, BadMemOp::Read(_), _) => self.mask_qsal,
            Alarm::QSAL(_, BadMemOp::Write(_), _) => {
                // In one of the start-up routines run as a result of
                // CODABO, memory is wiped by over-writing it with a
                // repeating pattern, Starting from the top down.
                // This causes writes to plugboard memory which we
                // discard and to the unmapped gap below them.  We
                // have to be able to completer this routine to start
                // the computer.  So the TX-2 must have either started
                // up with QSAL masked, or it must ignore writes to
                // unmapped locations.  I don't know which of these
                // was the case yet.  For now, we just behave as if
                // QSAL was masked when the operation is a write.
                //
                // TODO: is this correct for writes to un-mapped
                // memory?
                true
            }
            Alarm::IOSAL { .. } => self.mask_iosal,
            Alarm::MISAL { .. } => self.mask_misal,
            Alarm::BUGAL { .. } | Alarm::DEFERLOOPAL { .. } | Alarm::ROUNDTUITAL(_) => {
                assert!(AlarmUnit::is_never_masked(alarm_instance));
                return false;
            }
        };
        assert!(!AlarmUnit::is_never_masked(alarm_instance));
        masked
    }

    pub fn always_fire(&self, alarm_instance: Alarm) -> Alarm {
        if AlarmUnit::is_never_masked(&alarm_instance) {
            alarm_instance
        } else {
            panic!(
                "always_fire was called for alarm {:?} but that alarm can be masked",
                &alarm_instance,
            );
        }
    }

    pub fn fire_if_not_masked(&self, alarm_instance: Alarm) -> Result<(), Alarm> {
        if self.is_masked(&alarm_instance) {
            Ok(())
        } else {
            Err(alarm_instance)
        }
    }
}

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
