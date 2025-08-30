use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::time::Duration;

use serde::Serialize;

use base::instruction::Instruction;
use base::prelude::*;

use super::bugreport::{IssueType, bug_report_url};
use super::diagnostics::{CurrentInstructionDiagnostics, DiagnosticFetcher};

#[derive(Debug, Clone)]
pub enum BadMemOp {
    Read(Unsigned36Bit),
    Write(Unsigned36Bit),
}

impl Display for BadMemOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BadMemOp::Read(addr) => write!(f, "memory read from {addr:>013o} failed"),
            BadMemOp::Write(addr) => write!(f, "memory write to {addr:>013o} failed"),
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

/// Indicates what the emulator was doing when a bug was discovered.
#[derive(Debug, Clone)]
pub enum BugActivity {
    Io,
    Opcode,
    AlarmHandling,
}

// Alarms from User's Handbook section 5-2.2; full names are taken
// from section 10-2.5.1 (vol 2) of the Technical Manual.
// These acrronyms are upper case to follow the names in the TX-2 documentation.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub enum AlarmDetails {
    /// P Memory Cycle Selecttion Alarm.  This fires when we attempt
    /// to fetch an instruction from an invalid address.
    PSAL(u32, String),

    /// Operation Code Alarm.  This fires when an instruction word
    /// containing an undefined operation code is read out of memory.
    ///
    /// Section 10-2.5.3 of the TX-2 Technical Manual (Volume 2)
    /// states that this can also happen when an AOP instruction
    /// specifies an undefined op code in bits N₂.₆-N₂.₁.  An AOP
    /// instruction is has opcode number 4, but with bits N₂.₈=0 and
    /// N₂.₇=1 (instead of 00 which is the case for an IOS
    /// instruction).
    OCSAL(Instruction, String),

    /// Q Memory Cycle Selecttion Alarm.  Q register (i.e. data fetch
    /// address) is set to an invalid address.
    QSAL(Instruction, BadMemOp, String),

    /// In-Out Selection Alarm. I/O Alarm in IOS instruction; device
    /// broken/maintenance/nonexistent.
    IOSAL {
        /// The affected unit (as opposed to the sequence number currently executing).
        unit: Unsigned6Bit,
        operand: Option<Unsigned18Bit>,
        message: String,
    },

    /// In-Out Miss Indication Alarm.  Fires when some I/O unit has
    /// missed a data item.  This generally indicates that the program
    /// is too slow for an I/O device.  For example because it uses
    /// too many hold bits.
    MISAL { affected_unit: Unsigned6Bit },

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
    ROUNDTUITAL {
        explanation: String,
        bug_report_url: &'static str,
    },

    /// Loop in deferred addressing (detection of this is not a feature
    /// of the TX-2).
    DEFERLOOPAL {
        /// address is some address within the loop.
        address: Unsigned18Bit,
    },

    /// There is a bug in the simulator.
    BUGAL {
        /// What were we doing?
        activity: BugActivity,
        /// What instruction was executing?
        diagnostics: CurrentInstructionDiagnostics,
        /// What went wrong?
        message: String,
    },
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub struct Alarm {
    pub sequence: Option<SequenceNumber>,
    pub details: AlarmDetails,
}

impl Alarm {
    pub fn kind(&self) -> AlarmKind {
        self.details.kind()
    }
}

impl AlarmDetails {
    pub fn kind(&self) -> AlarmKind {
        match self {
            AlarmDetails::PSAL(_, _) => AlarmKind::PSAL,
            AlarmDetails::OCSAL(_, _) => AlarmKind::OCSAL,
            AlarmDetails::QSAL(_, _, _) => AlarmKind::QSAL,
            AlarmDetails::IOSAL { .. } => AlarmKind::IOSAL,
            AlarmDetails::MISAL { .. } => AlarmKind::MISAL,
            AlarmDetails::ROUNDTUITAL { .. } => AlarmKind::ROUNDTUITAL,
            AlarmDetails::DEFERLOOPAL { .. } => AlarmKind::DEFERLOOPAL,
            AlarmDetails::BUGAL { .. } => AlarmKind::BUGAL,
        }
    }
}

impl Display for Alarm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        if let Some(seq) = self.sequence {
            write!(f, "in sequence {seq:o}, {}", self.details)
        } else {
            write!(f, "{}", self.details)
        }
    }
}

impl Display for AlarmDetails {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use AlarmDetails::*;
        match self {
            QSAL(instruction, op, msg) => {
                write!(
                    f,
                    "QSAL: during execution of instruction {instruction:?}, {op}: {msg}",
                )
            }
            PSAL(address, msg) => {
                write!(
                    f,
                    "PSAL: P register set to illegal address {address:>06o}: {msg}",
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
            ROUNDTUITAL {
                explanation,
                bug_report_url,
            } => {
                write!(
                    f,
                    "ROUNDTUITAL: the program used a feature not supported in the emulator: {explanation}. See feature request at {bug_report_url}",
                )
            }

            IOSAL {
                unit,
                operand,
                message,
            } => {
                write!(f, "IOSAL: I/O alarm during operation on unit {unit:o}")?;
                if let Some(oper) = operand {
                    write!(f, " with operand {oper}")?;
                }
                write!(f, ": {message}")
            }

            MISAL { affected_unit } => write!(
                f,
                "MISAL: program too slow; missed data for unit {affected_unit:o}"
            ),

            BUGAL {
                diagnostics,
                message,
                activity,
            } => {
                let (issue_type, activity_desc): (Option<IssueType>, &'static str) = match activity
                {
                    BugActivity::AlarmHandling => (None, "alarm handling"),
                    BugActivity::Io => (Some(IssueType::Io), "I/O"),
                    BugActivity::Opcode => (Some(IssueType::Opcode), "instruction execution"),
                };
                let report_url = bug_report_url(message, issue_type);
                write!(
                    f,
                    "BUGAL: encountered a bug in enumator {activity_desc} during execution of {diagnostics}: {message}; please report this as a bug at {report_url}",
                )
            }
            DEFERLOOPAL { address } => {
                write!(
                    f,
                    "DEFERLOOPAL: infinite loop in deferred address at {address:>012o}",
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

impl Display for UnmaskedAlarm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "unmasked alarm {}", self.alarm)?;
        if let Some(address) = self.address {
            write!(f, "at address {address}")
        } else {
            Ok(())
        }
    }
}

pub trait Alarmer {
    fn fire_if_not_masked<F: DiagnosticFetcher>(
        &mut self,
        alarm_instance: Alarm,
        get_diags: F,
    ) -> Result<(), Alarm>;
    fn always_fire<F: DiagnosticFetcher>(&mut self, alarm_instance: Alarm, get_diags: F) -> Alarm;
}
