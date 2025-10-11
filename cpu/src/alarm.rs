//! TX-2 alarms.
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::time::Duration;

use serde::Serialize;

use base::instruction::Instruction;
use base::prelude::*;

use super::bugreport::{IssueType, bug_report_url};
use super::diagnostics::{CurrentInstructionDiagnostics, DiagnosticFetcher};

/// A memory read or write failure.
#[derive(Debug, Clone)]
pub enum BadMemOp {
    /// Describes a failure to read from an address.
    Read(Unsigned36Bit),
    /// Describes a failure to write to an address.
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

/// Describes whether a particular kind of alarm can be masked.
#[derive(Debug, PartialEq, Eq)]
pub enum AlarmMaskability {
    Maskable,
    Unmaskable,
}

/// Describes the kinds of alarm that exist in the TX-2.
///
/// Some alarms which cannot occur in the emulator (such as partity
/// alarms in the X-memory or the STUV-memory) don't have an
/// enumerator.
///
/// These acrronyms are upper case to follow the names in the TX-2
/// documentation.  The meanings of the values are described in
/// [`AlarmDetails`].
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
    /// Indicates whether an alarm can be masked.
    #[must_use]
    pub fn maskable(&self) -> AlarmMaskability {
        match self {
            AlarmKind::BUGAL | AlarmKind::DEFERLOOPAL | AlarmKind::ROUNDTUITAL => {
                AlarmMaskability::Unmaskable
            }
            _ => AlarmMaskability::Maskable,
        }
    }

    #[must_use]
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
    /// Indicates that the emulator was performing I/O at the point a
    /// bug was discovered.
    Io,
    /// Indicates that the emulator was executing an instruction at
    /// the point a bug was discovered.
    Opcode,
    /// Indicates that the emulator was performing an alarm
    /// manipulation at the point a bug was discovered.
    AlarmHandling,
}

/// `AlarmsDetails` variant names are from User's Handbook section
/// 5-2.2; full names are taken from section 10-2.5.1 (vol 2) of the
/// Technical Manual.
///
/// These acrronyms are upper case to follow the names in the TX-2 documentation.
///
/// # Unimplemented Alarms
///
/// Alarms we have not implemented:
///
/// | Mnemonic | Description | Reason why It's not Included |
/// | -------- | ----------- | ---------------------------- |
/// | SYAL1    | Sync System Alarm (see User Handbook page 5-21). | Not yet implemented. |
/// | SYAL2    | Sync System Alarm (see User Handbook page 5-21). | Not yet implemented. |
/// | MPAL     | M memory Parity Alarm | Parity errors are not emulated. |
/// | NPAL     | N memory Parity Alarm | Parity errors are not emulated. |
/// | FPAL     | F memory Parity Alarm | Parity errors are not emulated. |
/// | XPAL     | X memory Parity Alarm | Parity errors are not emulated. |
/// | TSAL     | T memory selection alarm | Indicates overcurrent in the T Memory.  We have no hardware, so no overcurrent. |
/// | USAL     | U memory selection alarm | Indicates overcurrent in the T Memory.  We have no hardware, so no overcurrent. |
/// | Mousetrap | Stops the computer when there is a malfunction in the setting of the S-memory flip-flops (or perhaps other reasons chosen by the system maintainers). |  Not required. |
///
/// L. G. Roberts memo of 1965-01-07 seems to indicate that another
/// alarm, SPAL, was introduced later; see
/// <http://www.bitsavers.org/pdf/mit/tx-2/rcsri.org_library_tx2/TX2-Memos-General_196407.pdf>.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub enum AlarmDetails {
    /// P Memory Cycle Selection Alarm.  This fires when we attempt to
    /// fetch an instruction (but not an operand) from an invalid
    /// address.
    PSAL(u32, String),

    /// Operation Code Alarm.  This fires when an instruction word
    /// containing an undefined operation code is read out of memory.
    ///
    /// Section 10-2.5.3 of the TX-2 Technical Manual (Volume 2)
    /// states that this can also happen when an `AOP` instruction
    /// specifies an undefined op code in bits N₂.₆-N₂.₁.  An `AOP`
    /// instruction is has opcode number 4, but with bits N₂.₈=0 and
    /// N₂.₇=1 (instead of 00 which is the case for an IOS
    /// instruction).  So far however, we have not found any further
    /// information about the interpretation of bits N₂.₆-N₂.₁ for
    /// `AOP`.
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

    /// Indicates that something is not implemented in the emulator.
    /// This alarm didn't exist in the real TX-2.
    ROUNDTUITAL {
        explanation: String,
        bug_report_url: &'static str,
    },

    /// Loop in deferred addressing (detection of this is not a
    /// feature of the TX-2, this occurs only in the emulator).
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

/// Describes an alarm which is active.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub struct Alarm {
    pub sequence: Option<SequenceNumber>,
    pub details: AlarmDetails,
}

impl Alarm {
    #[must_use]
    pub fn kind(&self) -> AlarmKind {
        self.details.kind()
    }
}

impl AlarmDetails {
    #[must_use]
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

/// Describes an alarm which is active and is not masked (meaning that
/// it is actually firing).
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

/// A trait for objects which implement the firing of alarms.
pub trait Alarmer {
    /// Fire the indicated alarm if it is not masked.
    fn fire_if_not_masked<F: DiagnosticFetcher>(
        &mut self,
        alarm_instance: Alarm,
        get_diags: F,
    ) -> Result<(), Alarm>;
    /// Unconditionally fire the indicated alarm.
    fn always_fire<F: DiagnosticFetcher>(&mut self, alarm_instance: Alarm, get_diags: F) -> Alarm;
}
