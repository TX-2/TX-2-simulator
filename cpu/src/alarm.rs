use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::time::Duration;

use serde::Serialize;

use base::instruction::Instruction;
use base::prelude::*;

#[derive(Debug, Clone)]
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

#[derive(Debug, PartialEq, Eq)]
pub enum AlarmMaskability {
    Maskable,
    Unmaskable,
}

// These acrronyms are upper case to follow the names in the TX-2 documentation.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Serialize)]
pub enum AlarmKind {
    PSAL,
    OCSAL,
    QSAL,
    IOSAL,
    MISAL,
    ROUNDTUITAL,
    DEFERLOOPAL,
    BUGAL,
}

impl Display for AlarmKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            AlarmKind::PSAL => "PSAL",
            AlarmKind::OCSAL => "OCSAL",
            AlarmKind::QSAL => "QSAL",
            AlarmKind::IOSAL => "IOSAL",
            AlarmKind::MISAL => "MISAL",
            AlarmKind::ROUNDTUITAL => "ROUNDTUITAL",
            AlarmKind::DEFERLOOPAL => "DEFERLOOPAL",
            AlarmKind::BUGAL => "BUGAL",
        })
    }
}

impl AlarmKind {
    pub fn maskable(&self) -> AlarmMaskability {
        match self {
            AlarmKind::BUGAL | AlarmKind::DEFERLOOPAL | AlarmKind::ROUNDTUITAL => {
                AlarmMaskability::Unmaskable
            }
            _ => AlarmMaskability::Maskable,
        }
    }

    pub const fn all_alarm_kinds() -> [AlarmKind; 8] {
        [
            AlarmKind::PSAL,
            AlarmKind::OCSAL,
            AlarmKind::QSAL,
            AlarmKind::IOSAL,
            AlarmKind::MISAL,
            AlarmKind::ROUNDTUITAL,
            AlarmKind::DEFERLOOPAL,
            AlarmKind::BUGAL,
        ]
    }
}

#[derive(Debug)]
pub struct UnknownAlarmName(String);

impl Display for UnknownAlarmName {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "unknown alarm name '{}'", self.0)
    }
}

impl Error for UnknownAlarmName {}

impl TryFrom<&str> for AlarmKind {
    type Error = UnknownAlarmName;
    fn try_from(s: &str) -> Result<AlarmKind, UnknownAlarmName> {
        match s {
            "PSAL" => Ok(AlarmKind::PSAL),
            "OCSAL" => Ok(AlarmKind::OCSAL),
            "QSAL" => Ok(AlarmKind::QSAL),
            "IOSAL" => Ok(AlarmKind::IOSAL),
            "MISAL" => Ok(AlarmKind::MISAL),
            "ROUNDTUITAL" => Ok(AlarmKind::ROUNDTUITAL),
            "DEFERLOOPAL" => Ok(AlarmKind::DEFERLOOPAL),
            "BUGAL" => Ok(AlarmKind::BUGAL),
            _ => Err(UnknownAlarmName(s.to_owned())),
        }
    }
}

#[test]
fn test_alarm_kind_round_trip() {
    for orig_kind in AlarmKind::all_alarm_kinds() {
        let name = orig_kind.to_string();
        match AlarmKind::try_from(name.as_str()) {
            Ok(k) => {
                assert_eq!(k, orig_kind);
            }
            Err(_) => {
                panic!("unable to round-trip alarm kind {orig_kind:?}");
            }
        }
    }
    assert!(AlarmKind::try_from("this is not an alarm name").is_err());
}

// Alarms from User's Handbook section 5-2.2; full names are taken
// from section 10-2.5.1 (vol 2) of the Technical Manual.
// These acrronyms are upper case to follow the names in the TX-2 documentation.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub enum Alarm {
    /// P Memory Cycle Selecttion Alarm.  This fires when we attempt
    /// to fetch an instruction from an invalid address.
    PSAL(u32, String),

    /// Operation Code Alarm.  This fires when an instruction word
    /// containing an undefined operation code is read out of memory.
    /// Section 10-2.5.3 states that this can also happen when an AOP
    /// instruction specifies an undefined op code in bits N???.???-N???.???.
    /// But I don't know what an AOP instruction is, yet.
    OCSAL(Instruction, String),

    /// Q Memory Cycle Selecttion Alarm.  Q register (i.e. data fetch
    /// address) is set to an invalid address.
    QSAL(Instruction, BadMemOp, String),

    /// In-Out Selection Alarm. I/O Alarm in IOS instruction; device
    /// broken/maintenance/nonexistent.
    IOSAL {
        unit: Unsigned6Bit,
        operand: Option<Unsigned18Bit>,
        message: String,
    },

    /// In-Out Miss Indication Alarm.  Fires when some I/O unit has
    /// missed a data item.  This generally indicates that the program
    /// is too slow for an I/O device.  For example because it uses
    /// too many hold bits.
    MISAL { unit: Unsigned6Bit },

    // Alarms we probably should implement but have not:
    //
    // SYAL: Sync System Alarm

    // Not included here because the simulator pretends that parity
    // checks always succeed:
    //
    // MPAL: M Parity Alarm
    // NPAL: N Parity Alarm
    // FPAL: F Parity Alarm
    // XPAL: X Parity Alarm
    //
    // Not included here for other reasons:
    //
    // TSAL: T Memory Selection Alarm; indicates overcurrent in the T
    // Memory.  We have no hardware, so no overcurrent.
    //
    // Mousetrap Alarm: stops the computer when there is a malfunction
    // in the setting of the S-memory flip-flops.  We don't have those
    // in the simulator.

    // The following alarms didn't exist in the real TX-2:
    /// Something is not implemented
    ROUNDTUITAL(String),

    /// Loop in deferred addressing (detection of this is not a feature
    /// of the TX-2).
    DEFERLOOPAL {
        /// address is some address within the loop.
        address: Unsigned18Bit,
    },

    /// There is a bug in the simulator.
    BUGAL {
        instr: Option<Instruction>,
        message: String,
    },
}

impl Alarm {
    pub fn kind(&self) -> AlarmKind {
        match self {
            Alarm::PSAL(_, _) => AlarmKind::PSAL,
            Alarm::OCSAL(_, _) => AlarmKind::OCSAL,
            Alarm::QSAL(_, _, _) => AlarmKind::QSAL,
            Alarm::IOSAL {
                unit: _,
                operand: _,
                message: _,
            } => AlarmKind::IOSAL,
            Alarm::MISAL { unit: _ } => AlarmKind::MISAL,
            Alarm::ROUNDTUITAL(_) => AlarmKind::ROUNDTUITAL,
            Alarm::DEFERLOOPAL { address: _ } => AlarmKind::DEFERLOOPAL,
            Alarm::BUGAL {
                instr: _,
                message: _,
            } => AlarmKind::BUGAL,
        }
    }
}

impl Display for Alarm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Alarm::*;
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
                    "PSAL: P register set to illegal address {:>06o}: {}",
                    address, msg
                )
            }
            OCSAL(inst, msg) => {
                write!(
                    f,
                    "OCSAL: N register set to invalid instruction {:>012o}: {}",
                    inst.bits(),
                    msg
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
                if let Some(instruction) = instr.as_ref() {
                    if let Ok(symbolic) = SymbolicInstruction::try_from(instruction) {
                        write!(
			    f,
			    "BUGAL: encountered simulator bug during execution of instruction {symbolic}: {message}"
			)
                    } else {
                        write!(
			    f,
			    "BUGAL: encountered simulator bug during execution of instruction {:o}: {}",
			    instruction.bits(), message,
			)
                    }
                } else {
                    write!(f, "BUGAL: encountered simulator bug: {message}")
                }
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

#[derive(Debug)]
pub struct UnmaskedAlarm {
    pub alarm: Alarm,
    pub address: Option<Address>,
    pub when: Duration,
}

pub trait Alarmer {
    fn fire_if_not_masked(&mut self, alarm_instance: Alarm) -> Result<(), Alarm>;
    fn always_fire(&mut self, alarm_instance: Alarm) -> Alarm;
}
