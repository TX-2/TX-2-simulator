//! Emulates the control unit of the TX-2.
//!
//! The control unit is conceptually similar to the CPU of a modern
//! computer, except that the arithmetic unit and registers are
//! separate.  Within this emulator, the control unit performs the
//! following functions:
//!
//! - Instruction decoding
//! - Handle CODABO and STARTOVER
//! - Keep track of the flags of each sequence
//! - Keep track of the placeholder of each sequence
//! - Manage switching between sequences
//! - Remember the setting of the TSP (Toggle Start Point) register
use std::collections::HashSet;
use std::ops::BitAnd;
use std::time::Duration;

use tracing::{event, span, Level};

mod op_configuration;
mod op_index;
mod op_io;
mod op_jump;
mod op_loadstore;
pub mod timing;
mod trap;

use base::instruction::{Inst, Instruction, Opcode, OperandAddress, SymbolicInstruction};
use base::prelude::*;
use base::subword;

use crate::alarm::{Alarm, AlarmUnit, BadMemOp};
use crate::exchanger::{exchanged_value_for_load, exchanged_value_for_store, SystemConfiguration};
use crate::io::{DeviceManager, Unit};
use crate::memory::{self, ExtraBits, MemoryMapped, MemoryOpFailure, MemoryUnit, MetaBitChange};

use trap::TrapCircuit;

#[derive(Debug, PartialEq, Eq)]
pub enum RunMode {
    Running,
    InLimbo,
}

#[derive(Debug, Eq, PartialEq)]
pub enum ProgramCounterChange {
    /// Change of current sequence.
    SequenceChange(Unsigned6Bit),

    // A TSD instruction ends in dismiss-and-wait.  That is, the
    // sequence is dismissed without its sequence number changing.
    DismissAndWait(Address),

    /// Immediate stop of execution, such as when an unmasked alarm is raised.
    Stop(Address),

    // Normal increment of the program counter.
    CounterUpdate,

    // Transfer control to another address (but without changing
    // sequence).
    Jump(Address),
}

/// Flags represent requests to run for instruction sequences (today
/// one might describe these as threads).  Some sequences are special:
///
/// | Sequence Number | Description |
/// | --------------- | ----------- |
/// | 0   | Sequence which is run to start the computer (e.g. when "CODABO" or "START OVER" is pressed).                             |
/// |41-75| hardware devices          |
/// | 76  | Not for physical devices. |
/// | 77  | Not for physical devices. |
///
/// The flag for sequences 76 and 77 may only be raised/lowered by
/// program control.
///
#[derive(Debug)]
struct SequenceFlags {
    flag_values: u64,
}

impl SequenceFlags {
    fn new() -> SequenceFlags {
        // New instances start with no flags raised (i.e. in "Limbo",
        // STARTOVER not running).
        SequenceFlags { flag_values: 0 }
    }

    fn lower_all(&mut self) {
        self.flag_values = 0;
    }

    fn flagbit(flag: &SequenceNumber) -> u64 {
        1_u64 << u64::from(*flag)
    }

    fn lower(&mut self, flag: &SequenceNumber) {
        // We create a u16 from *flag in order to perform the
        // comparison.  Otherwise we get the compilation error
        // "error[E0277]: can't compare `base::prelude::Unsigned6Bit`
        // with `u16`".
        #![allow(clippy::cmp_owned)]
        assert!(u16::from(*flag) < 0o100_u16);
        event!(Level::DEBUG, "Lowering flag {}", flag,);
        self.flag_values &= !SequenceFlags::flagbit(flag);
    }

    fn raise(&mut self, flag: &SequenceNumber) {
        // We create a u16 from *flag in order to perform the
        // comparison.  Otherwise we get the compilation error
        // "error[E0277]: can't compare `base::prelude::Unsigned6Bit`
        // with `u16`".
        #![allow(clippy::cmp_owned)]
        assert!(u16::from(*flag) < 0o100_u16);
        event!(Level::DEBUG, "Raising flag {}", flag,);
        self.flag_values |= SequenceFlags::flagbit(flag);
    }

    fn current_flag_state(&self, flag: &SequenceNumber) -> bool {
        // We create a u16 from *flag in order to perform the
        // comparison.  Otherwise we get the compilation error
        // "error[E0277]: can't compare `base::prelude::Unsigned6Bit`
        // with `u16`".
        #![allow(clippy::cmp_owned)]
        assert!(u16::from(*flag) < 0o100_u16);
        self.flag_values & SequenceFlags::flagbit(flag) != 0
    }

    /// Return the index of the highest-priority (lowest-numbered)
    /// flag.  If no flag is raised (the machine is in "Limbo"),
    /// return None.
    fn highest_priority_raised_flag(&self) -> Option<SequenceNumber> {
        let n = self.flag_values.trailing_zeros();
        if n == 64 {
            None
        } else {
            Some(n.try_into().unwrap())
        }
    }
}

#[test]
fn test_sequence_flags() {
    let mut flags = SequenceFlags::new();

    flags.lower_all();
    assert_eq!(flags.highest_priority_raised_flag(), None);

    flags.raise(&Unsigned6Bit::ZERO);
    assert_eq!(
        flags.highest_priority_raised_flag().map(i8::from),
        Some(0_i8)
    );
    flags.raise(&Unsigned6Bit::ONE);
    // 0 is still raised, so it still has the highest priority.
    assert_eq!(
        flags.highest_priority_raised_flag(),
        Some(Unsigned6Bit::ZERO)
    );

    flags.lower(&SequenceNumber::ZERO);
    assert_eq!(
        flags.highest_priority_raised_flag(),
        Some(Unsigned6Bit::ONE)
    );
    flags.lower(&SequenceNumber::ONE);
    assert_eq!(flags.highest_priority_raised_flag(), None);

    let four = SequenceNumber::try_from(4_i8).expect("valid test data");
    let six = SequenceNumber::try_from(6_i8).expect("valid test data");
    flags.raise(&four);
    flags.raise(&six);
    assert_eq!(flags.highest_priority_raised_flag(), Some(four));
    flags.lower(&four);
    assert_eq!(flags.highest_priority_raised_flag(), Some(six));
}

#[test]
fn test_sequence_flags_current_flag_state() {
    let mut flags = SequenceFlags::new();
    let s52: SequenceNumber = u6!(0o52);
    flags.lower_all();
    assert!(!flags.current_flag_state(&s52), "flag 52 should be lowered");
    flags.raise(&s52);
    assert!(flags.current_flag_state(&s52), "flag 52 should be raised");
}

#[derive(Debug)]
struct ControlRegisters {
    pub e: Unsigned36Bit,
    pub n: Instruction,
    pub n_sym: Option<SymbolicInstruction>,
    pub p: Address,
    pub q: Address,

    // The k register (User guide 4-3.1) holds the current sequence
    // number (User guide 5-24).  k is Option<SequenceNumber> in order
    // to allow the (emulated) control unit to recognise a CODABO
    // button as indicating a need to change sequence from the control
    // unit's initial state to sequence 0.
    //
    // This likely doesn't reflect the actual operation of the TX-2
    // very well, and better understanding of the real operation of
    // the machine will likely change this.
    //
    // I think that perhaps section 12-2.6.2 of Volume 2 of the
    // technical manual may explain how the real TX-2 avoided this
    // problem, but I don't think I understand what that section says.
    // The text is:
    //
    // """12-2.6.2 XPS FLIP-FLOP LOGIC.  This flip-floop inhibits the
    // X Memory strobe pulse into X when the register selected has the
    // same address or the current program counter, is not register 0,
    // and this is the first reference to this register since the last
    // sequence change.  In this case all the cores of the register
    // are clearered and only "junk" (with a 50-50 chance of a bad
    // parity) would be strobed into X.  If XPS¹, then a clear pulse
    // is substituted for the strobe pulse.
    //
    // The flip-flop is set whenever a sequence change occurs, and is
    // cleared the first time thereafter that the program counter
    // register is referenced during a PK cycle (if ever).  See Fig
    // 12-8."""
    pub k: Option<SequenceNumber>,

    spr: Address, // Start Point Register

    /// Index register 0 is the Toggle Start point.
    /// Index registers 40-77 are program counters for the sequences.
    ///
    /// The index registers form an 18-bit ring (as stated in the
    /// description of the AUX instruction) and are described on page
    /// 3-68 of the User Handbook (section 3-3.1) as being signed
    /// integers.
    index_regs: [Signed18Bit; 0o100], // AKA the X memory
    f_memory: [SystemConfiguration; 32], // the F memory
    flags: SequenceFlags,
    current_sequence_is_runnable: bool,
    // TODO: we may be able to eliminate prev_hold by moving the logic
    // that's currently at the beginning of fetch_instruction() so
    // that it occurs at the end of execute_instruction() instead.
    // See the comment at the top of fetch_instruction().
    prev_hold: bool,
}

impl ControlRegisters {
    fn new() -> ControlRegisters {
        let fmem = {
            let default_val = SystemConfiguration::try_from(0).unwrap();
            [default_val; 32]
        };
        let mut result = ControlRegisters {
            e: Unsigned36Bit::ZERO,
            n: Instruction::invalid(), // not a valid instruction
            n_sym: None,
            p: Address::default(),
            q: Address::default(),
            k: None, // not 0, so that we can recognise CODABO.
            index_regs: [Signed18Bit::default(); 0o100],
            f_memory: fmem,
            flags: SequenceFlags::new(),
            current_sequence_is_runnable: false,
            prev_hold: false,
            spr: Address::default(),
        };
        // Index register 0 always contains 0.  This should still be
        // true if we modify the behaviour of Address::default(),
        // which is why we override it here.
        result.index_regs[0] = Signed18Bit::ZERO;
        result
    }

    fn previous_instruction_hold(&self) -> bool {
        // We cannot just check the N register for this, because when
        // a TSD instruction ends in "dismiss and wait", the N
        // register contains the (possibly held) TSD instruction, but
        // it's the hold bit of the _previous_ instruction that
        // matters.
        self.prev_hold
    }

    fn set_spr(&mut self, addr: &Address) {
        self.spr = *addr;
    }

    fn get_index_register(&self, n: Unsigned6Bit) -> Signed18Bit {
        let n = usize::from(n);
        assert_eq!(self.index_regs[0], 0);
        assert!(n < 0o100);
        self.index_regs[n]
    }

    fn get_index_register_as_address(&mut self, n: Unsigned6Bit) -> Address {
        let value: Signed18Bit = self.get_index_register(n);
        Address::from(value.reinterpret_as_unsigned())
    }

    fn set_index_register(&mut self, n: Unsigned6Bit, value: &Signed18Bit) {
        let n = usize::from(n);
        assert_eq!(self.index_regs[0], 0);
        assert_ne!(n, 0, "Index register 0 should be fixed at 0");
        assert!(n < 0o100);
        self.index_regs[n] = *value;
    }

    fn set_index_register_from_address(&mut self, n: Unsigned6Bit, addr: &Address) {
        let value: Unsigned18Bit = Unsigned18Bit::from(*addr);
        self.set_index_register(n, &value.reinterpret_as_signed());
    }

    fn get_f_mem(&self, n: Unsigned5Bit) -> SystemConfiguration {
        // Use u8::from in order to be able to compare an Unsigned5Bit.
        #![allow(clippy::cmp_owned)]
        assert!(u8::from(n) < 0o37_u8);
        assert_eq!(self.f_memory[0], SystemConfiguration::zero());
        let pos: usize = n.into();
        self.f_memory[pos]
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ResetMode {
    ResetTSP = 0,
    Reset0 = 0o0377710,
    Reset1 = 0o0377711,
    Reset2 = 0o0377712,
    Reset3 = 0o0377713,
    Reset4 = 0o0377714,
    Reset5 = 0o0377715,
    Reset6 = 0o0377716,
    Reset7 = 0o0377717,
}

impl ResetMode {
    fn address(&self, mem: &mut MemoryUnit) -> Option<Address> {
        use ResetMode::*;
        match self {
            Reset0 | Reset1 | Reset2 | Reset3 | Reset4 | Reset5 | Reset6 | Reset7 => {
                let loc: Address = Address::from(Unsigned18Bit::try_from(*self as u32).unwrap());
                match mem.fetch(&loc, &MetaBitChange::None) {
                    Ok((word, _)) => {
                        // word is 36 bits wide but we only want the bottom 17 bits.
                        let (left, right) = subword::split_halves(word);
                        if left != 0 {
                            // issue warning but otherwise ignore
                            event!(Level::WARN, "Ignoring non-zero left subword of reset register {:o}, containing {:o} (left side is {:o})",
				   loc, word, left);
                        }
                        // We assume that reset operations don't implement deferred addressing.
                        const PHYSICAL_ADDRESS_BITS: u32 = 0o377_777;
                        let defer_bit = Unsigned18Bit::try_from(0o400_000).unwrap();
                        if right & defer_bit != 0 {
                            // issue warning but otherwise ignore
                            event!(Level::WARN, "Ignoring non-zero defer bit of reset register {:o}, containing {:o}",
				   loc, word);
                        }

                        let physical_address = Address::from(right & PHYSICAL_ADDRESS_BITS);
                        Some(physical_address)
                    }
                    Err(e) => {
                        panic!("failed to fetch reset {:?}: {}", self, e);
                    }
                }
            }
            ResetTSP => None, // need to read the TSP toggle switch.
        }
    }
}

/// ControlUnit simulates the operation of the Control Element of the TX-2 computer.
///
#[derive(Debug)]
pub struct ControlUnit {
    regs: ControlRegisters,
    trap: TrapCircuit,
    devices: DeviceManager,
    alarm_unit: AlarmUnit,
}

fn sign_extend_index_value(index_val: &Signed18Bit) -> Unsigned36Bit {
    let left = if index_val.is_negative() {
        Unsigned18Bit::MAX
    } else {
        Unsigned18Bit::ZERO
    };
    subword::join_halves(left, index_val.reinterpret_as_unsigned())
}

/// Determines whether a memory operation updates the E register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UpdateE {
    No,
    Yes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SequenceSelection {
    Continue,
    Change(SequenceNumber),
    InLimbo,
}

pub type OpcodeResult = Result<Option<ProgramCounterChange>, Alarm>;

impl ControlUnit {
    pub fn new() -> ControlUnit {
        ControlUnit {
            regs: ControlRegisters::new(),
            trap: TrapCircuit::new(),
            devices: DeviceManager::new(),
            alarm_unit: AlarmUnit::new_with_panic(),
        }
    }

    pub fn attach(
        &mut self,
        system_time: &Duration,
        unit_number: Unsigned6Bit,
        in_maintenance: bool,
        unit: Box<dyn Unit>,
    ) {
        self.devices
            .attach(system_time, unit_number, in_maintenance, unit)
    }

    pub fn set_metabits_disabled(&mut self, disable: bool) {
        self.trap.set_metabits_disabled(disable);
    }

    pub fn disconnect_io_devices(&mut self) {
        self.devices.disconnect_all();
    }

    /// There are actually 9 different CODABO buttons (see page 5-18
    /// of the User Guide).  There are also 9 corresponding RESET
    /// buttons.  Each RESET button has a corresponding CODABO button.
    /// See the `reset` method for address assignments.
    ///
    /// The CODABO operation leaves the Start Point Register set to
    /// the selected start point.  There are also 9 reset buttons
    /// which perform a similar task.
    ///
    /// Pressing the main CODABO button (the one which uses the Toggle
    /// Start Point register) will result in memory being cleared,
    /// F-memory being set up in a standard way, and then a program
    /// being read from the paper tape reader using the standard
    /// readin program set up on the plugboard.
    ///
    /// The standard readin program executes the program it read in
    /// from the address specified by the program.  The program
    /// executes as sequence 52 (PETR) with the PETR unit initially
    /// turned off.
    ///
    /// The Users Handbook (page 5-18) states that flags are cleared
    /// but it doesn't state anywhere that any registers are reset.
    /// So we don't do that.  But there's no unit test for that, since
    /// I haven't found (or cannot recall) a piece of documentation
    /// which states that this is so.
    pub fn codabo(&mut self, reset_mode: &ResetMode, mem: &mut MemoryUnit) {
        // TODO: clear alarms.
        // We probably don't need an equivalent of resetting the
        // control flip-flops in an emulator.  But if we did, that
        // would happen here.
        //
        // On the other hand, the P register is described as an
        // "18-bit flip-flop" in section 4-2.2 of the User Handbook,
        // so perhaps all the registers in V memory are cleared by
        // CODABO.
        //
        let span = span!(Level::ERROR,
			 "codabo",
			 reset_mode=?reset_mode);
        let _enter = span.enter();
        event!(Level::INFO, "Starting CODABO {:?}", &reset_mode);
        self.disconnect_io_devices();
        self.regs.flags.lower_all();
        self.startover(reset_mode, mem);
        event!(
            Level::DEBUG,
            "After CODABO, control unit contains {:#?}",
            &self
        );
    }

    /// There are 9 separate RESET buttons, for 8 fixed addresses and
    /// another which uses the Toggle Start Point register.  There
    /// appear to be two Toggle Start Point switches, one on the front
    /// panel and a second on a remote control unit.  The
    /// fixed-address RESET buttons correspond to the fixed
    /// addresses 3777710 through 3777717, inclusive.
    ///
    /// RESET *only* loads the Start Point Register, nothing else.
    pub fn reset(&mut self, reset_mode: &ResetMode, mem: &mut MemoryUnit) {
        self.regs.set_spr(&match reset_mode.address(mem) {
            Some(address) => address,
            None => self.tsp(),
        });
    }

    /// Handle press of STARTOVER (or part of the operation of
    /// CODABO).  STARTOVER does RESET and then raises flag zero.
    pub fn startover(&mut self, reset_mode: &ResetMode, mem: &mut MemoryUnit) {
        self.reset(reset_mode, mem);
        self.regs.current_sequence_is_runnable = false;
        self.regs.flags.raise(&SequenceNumber::ZERO);
        self.change_sequence(None, SequenceNumber::ZERO);
    }

    /// Return the value in the Toggle Start Register.  It is possible
    /// that this was memory-mapped in the real machine, but if that's
    /// the case the user guide doesn't specify where.  For now, we
    /// haven't made it configurable (i.e. have not emulated the
    /// hardware) yet, either.
    ///
    /// We just hard-code it to point at the F-memory confgiguration
    /// routine (which does its job and then invokes the standard tape
    /// reader).
    ///
    /// We used to set this to point at the "Memory Clear / Memory
    /// Smear" program in the plugboard, but that accesses addresses
    /// which are not mapped (e.g. the gap between U-memory and
    /// V-memory) and so should only be run qith QSAL disabled, which
    /// is not our default config.
    fn tsp(&self) -> Address {
        // The operation of RESET (or CODABO) will copy this value
        // into the zeroth index register (which the program counter
        // placeholder for sequence 0).
        memory::STANDARD_PROGRAM_INIT_CONFIG
    }

    fn trap_seq() -> Unsigned6Bit {
        Unsigned6Bit::try_from(0o42).unwrap()
    }

    fn raise_trap(&mut self) {
        self.regs.flags.raise(&Self::trap_seq());
    }

    fn change_sequence(&mut self, prev_seq: Option<SequenceNumber>, mut next_seq: SequenceNumber) {
        // If the "Trap on Change Sequence" is enabled and the new
        // sequence is marked (bit 2.9 of its index register is set).
        // Activate unit 0o42, unless that's the unit which is giving
        // up control.
        //
        // I'm not sure what should happen for the alternative case,
        // where a unit of higher priority than 0o42 is marked for
        // trap-on-sequence-change.
        if prev_seq == Some(next_seq) {
            event!(
                Level::WARN,
                "change_sequence: old and new sequences are the same: {:>02o}",
                u8::from(next_seq),
            );
            return;
        }

        event!(
            Level::INFO,
            "Changing sequence to {:>02o}",
            u8::from(next_seq),
        );

        fn is_marked_placeholder(index_val: &Signed18Bit) -> bool {
            index_val < &0
        }

        let trap_seq = Self::trap_seq();
        let sequence_change_trap = self.trap.trap_on_changed_sequence()
            && is_marked_placeholder(&self.regs.get_index_register(next_seq))
            && self.regs.k != Some(trap_seq)
            && next_seq > trap_seq;

        let previous_sequence: Unsigned6Bit = match prev_seq {
            None => Unsigned6Bit::ZERO,
            Some(n) => n,
        };
        self.regs.e = join_halves(
            join_quarters(
                Unsigned9Bit::from(previous_sequence),
                Unsigned9Bit::from(next_seq),
            ),
            Unsigned18Bit::from(self.regs.p),
        );

        if sequence_change_trap {
            self.regs.flags.raise(&trap_seq);
            next_seq = trap_seq;
        }
        self.regs.k = Some(next_seq);
        if let Some(prev) = prev_seq {
            // Index register 0 never changes, it's always 0.
            if prev_seq != Some(Unsigned6Bit::ZERO) {
                let p = self.regs.p;
                self.regs.set_index_register_from_address(prev, &p);
            }
        }
        self.set_program_counter(ProgramCounterChange::SequenceChange(next_seq));
    }

    fn set_program_counter(&mut self, change: ProgramCounterChange) {
        match change {
            ProgramCounterChange::Stop(p) => {
                let old_mark = self.regs.p.split().1;
                let new_mark: bool = p.split().1;
                assert_eq!(old_mark, new_mark);
                self.regs.p = p;
            }
            ProgramCounterChange::SequenceChange(next_seq) => {
                // According to the Technical Manual, page 12-6,
                // change of seqeuence is the only time in which P₂.₉
                // is altered.
                if next_seq != 0 {
                    self.regs.p = self.regs.get_index_register_as_address(next_seq);
                } else {
                    // Index register 0 is always 0, but by setting
                    // the Toggle Status Register, the user can run
                    // sequence 0 from an arbitrary address. That
                    // address can't be stored in index register 0
                    // since that's always 0, so we use an internal
                    // "spr" register which is updated by the
                    // RESET/CODABO buttons.  Here, we copy that saved
                    // value into P.
                    self.regs.p = self.regs.spr;
                }
            }
            ProgramCounterChange::CounterUpdate => {
                // Volume 2 of the Technical Manual (section 12-2.3 "P
                // REGISTER DRIVER LOGIC") states, """Information can
                // be transferred into the P register only from the X
                // Adder.  In addition to this single transfer path,
                // ther P register has a counter which can index the
                // contents of the P register by one.  Note that count
                // circuit does not alter the contents of P₂.₉"""
                //
                // Since P₂.₉ is the sign bit, this means that the P
                // register wraps rather than overflows.
                //
                // As a practical matter, this wrap-around case means
                // that self.regs.p previously contained 377,777.
                // That is the last instruction in V Memory.  This is
                // normally an unconditional JMP.  So in the standard
                // plugboard configuration, we're going to take the
                // jmp, meaning that we're never going to fetch an
                // instruction from the address we just computed.
                // But, this case may be needed to cover non-standard
                // plugboard configurations.  According to the
                // Technical Manual, page 12-6, change of seqeuence is
                // the only time in which P₂.₉ is altered.
                let (_old_physical, old_mark) = self.regs.p.split();
                let new_p = self.regs.p.successor(); // p now points at the next instruction.
                let (_new_physical, new_mark) = new_p.split();
                assert_eq!(old_mark, new_mark);
                self.regs.p = new_p;
            }
            ProgramCounterChange::DismissAndWait(new_p) | ProgramCounterChange::Jump(new_p) => {
                // Copy the value of P₂.₉ into `old_mark`.
                let (_old_physical, old_mark) = self.regs.p.split();
                // Update P, keeping the old value of P₂.₉.
                self.regs.p = Address::join(new_p.into(), old_mark);
            }
        }
    }

    /// Consider whether a change of sequence is needed.  Return true
    /// if some sequence is runnable, or false if we are in the LIMBO
    /// state.
    fn select_sequence(&mut self) -> SequenceSelection {
        if self.regs.previous_instruction_hold() {
            event!(
                Level::DEBUG,
                concat!(
                    "Hold bit of previous instruction was set, ",
                    "so we will not consider a sequence change"
                )
            );
            SequenceSelection::Continue
        } else {
            // Handle any possible change of sequence.
            match self.regs.flags.highest_priority_raised_flag() {
                None => {
                    // The current sequence's flag is no longer raised.
                    //
                    // This happens either because the sequence was
                    // dismissed (permanent or temporary drop-out) or IOSj
                    // 40000 ("LOWER FLAG J") had been issued.  In the
                    // latter case, the current sequence should continue
                    // to run until another sequence's flag is raised.
                    if !self.regs.current_sequence_is_runnable {
                        event!(
                            Level::DEBUG,
                            "No flags raised and current sequence is not runnable: in LIMBO"
                        );
                        SequenceSelection::InLimbo
                    } else {
                        event!(
                            Level::DEBUG,
                            "No flag is raised, but the current sequence is still runnable"
                        );
                        SequenceSelection::Continue
                    }
                }
                Some(seq) => {
                    event!(Level::TRACE, "Highest-priority sequence is {}", seq);
                    if Some(seq) > self.regs.k
                        || (!self.regs.current_sequence_is_runnable && Some(seq) < self.regs.k)
                    {
                        SequenceSelection::Change(seq)
                    } else {
                        // No sequence change, just carry on.
                        SequenceSelection::Continue
                    }
                }
            }
        }
    }

    fn fetch_instruction(&mut self, mem: &mut MemoryUnit) -> Result<(), Alarm> {
        // TODO: This implementation begins the instruction fetch
        // operation by considering a possible change of sequence.
        // The TX-2 itself considers a sequence change as the PK cycle
        // is completed, in the resting state PK⁰⁰.  So it might make
        // more sense to move the sequence-change logig to the end of
        // the instructino-execution implementation. That will likely
        // make it simpler to implement the "hold" bit and
        // dismiss-and-wait (i.e. cases where we don't increment the
        // sequence's program counter).  When considering this option,
        // it's a good idea to re-read section 9-4 of Volume 2 of the
        // Technical Manual.

        // If the previous instruction was held, we don't even scan
        // the flags.  This follows the description of how control
        // handles flags in section 4-3.5 of the User Handbook (page
        // 4-8).
        // Calculate the address from which we will fetch the
        // instruction, and the increment the program counter.
        let p_physical_address = Address::from(self.regs.p.split().0);
        event!(
            Level::TRACE,
            "Fetching instruction from physical address {}",
            p_physical_address
        );

        // Actually fetch the instruction.
        let meta_op = if self.trap.set_metabits_of_instructions() {
            MetaBitChange::Set
        } else {
            MetaBitChange::None
        };
        let instruction_word = match mem.fetch(&p_physical_address, &meta_op) {
            Ok((inst, extra_bits)) => {
                if extra_bits.meta && self.trap.trap_on_marked_instruction() {
                    self.raise_trap();
                }
                inst
            }
            Err(e) => match e {
                MemoryOpFailure::NotMapped(addr) => {
                    self.alarm_unit.fire_if_not_masked(Alarm::PSAL(
                        u32::from(addr),
                        "memory unit indicated physical address is not mapped".to_string(),
                    ))?;
                    // PSAL is masked, but we don't know what
                    // instruction to execute, since we couldn't fetch
                    // one.  The program counter will not be updated
                    // until we call execute_instruction(), so we
                    // shouldn't increment it here.  So we just return
                    // a held instruction which is not otherwise
                    // valid.
                    Unsigned36Bit::from(Instruction::invalid())
                }
                MemoryOpFailure::ReadOnly(_, _) => unreachable!(),
            },
        };
        event!(
            Level::TRACE,
            "Fetched instruction {:?} from physical address {:?}",
            instruction_word,
            p_physical_address
        );
        self.update_n_register(instruction_word)?;
        Ok(())
    }

    pub fn poll_hardware(
        &mut self,
        mut run_mode: RunMode,
        system_time: &Duration,
    ) -> Result<(RunMode, Option<Duration>), Alarm> {
        let (mut raised_flags, alarm, next_poll) = self.devices.poll(system_time);
        // If there are no hardware flags being raised, we may still
        // not be in limbo if there were already runnable sequences.
        // That is, if some sequence's flag was raised.  The hardware
        // devices can raise flags but not lower them.  Therefore if
        // run_mode was RunMode::Running on entry to this function, we
        // must return RunMode::Running.
        if raised_flags != 0 {
            run_mode = RunMode::Running;
        }

        // For each newly-raised flag, raise the flag in self.flags.
        event!(
            Level::TRACE,
            "poll_hardware: there are {} new flag raises",
            raised_flags.count_ones(),
        );
        for bitpos in 0.. {
            if raised_flags == 0 {
                break;
            }
            let mask = 1_u64 << bitpos;
            if raised_flags & mask != 0 {
                match SequenceNumber::try_from(bitpos) {
                    Ok(unit) => {
                        self.regs.flags.raise(&unit);
                    }
                    Err(_) => {
                        break;
                    }
                }
            }
            raised_flags &= !mask;
        }

        // If a device raised an alarm, generate that alarm now.  This
        // alarm was not an error return from the poll() method,
        // because we needed to ensure that all flag raised were
        // processed.
        if let Some(active) = alarm {
            event!(
                Level::INFO,
                "poll_hardware: an alarm is active: {:?}",
                active
            );
            Err(active)
        } else {
            Ok((run_mode, next_poll))
        }
    }

    fn update_n_register(&mut self, instruction_word: Unsigned36Bit) -> Result<(), Alarm> {
        self.regs.n = Instruction::from(instruction_word);
        if let Ok(symbolic) = SymbolicInstruction::try_from(&self.regs.n) {
            self.regs.n_sym = Some(symbolic);
            Ok(()) // valid instruction
        } else {
            self.alarm_unit
                .fire_if_not_masked(self.invalid_opcode_alarm())?;
            self.regs.n_sym = None;
            Ok(()) // invalid instruction, but OCSAL is masked.
        }
    }

    fn invalid_opcode_alarm(&self) -> Alarm {
        Alarm::OCSAL(
            self.regs.n,
            format!("invalid opcode {:#o}", self.regs.n.opcode_number()),
        )
    }

    fn estimate_execute_time_ns(&self, orig_inst: &Instruction) -> u64 {
        let inst_from: Address = self.regs.p; // this is now P+1 but likely in the same memory type.
        let defer_from: Option<Address> = match orig_inst.operand_address() {
            OperandAddress::Deferred(phys) => Some(phys),
            OperandAddress::Direct(_) => None,
        };
        let operand_from = match self.regs.n.operand_address() {
            // TODO: handle chains of deferred loads
            OperandAddress::Deferred(phys) => Some(phys),
            OperandAddress::Direct(_) => None,
        };
        timing::estimate_instruction_ns(
            inst_from,
            orig_inst.opcode_number(),
            defer_from,
            operand_from,
        )
    }

    /// Fetch and execute the next instruction pointed to by the P
    /// register.  Returns the estimated number of nanoseconds needed
    /// to execute the instruction.
    pub fn execute_instruction(
        &mut self,
        system_time: &Duration,
        mem: &mut MemoryUnit,
    ) -> Result<(u64, RunMode), (Alarm, Address)> {
        fn execute(
            prev_program_counter: Address,
            opcode: &Opcode,
            control: &mut ControlUnit,
            system_time: &Duration,
            mem: &mut MemoryUnit,
        ) -> OpcodeResult {
            match opcode {
                Opcode::Aux => control.op_aux(mem),
                Opcode::Ste => control.op_ste(mem),
                Opcode::Rsx => control.op_rsx(mem),
                Opcode::Skx => control.op_skx(),
                Opcode::Dpx => control.op_dpx(mem),
                Opcode::Jmp => control.op_jmp(),
                Opcode::Jpx => control.op_jpx(mem),
                Opcode::Jnx => control.op_jnx(mem),
                Opcode::Skm => control.op_skm(mem),
                Opcode::Spg => control.op_spg(mem),
                Opcode::Ios => control.op_ios(system_time),
                Opcode::Tsd => control.op_tsd(prev_program_counter, system_time, mem),
                _ => Err(Alarm::ROUNDTUITAL(format!(
                    "The emulator does not yet implement opcode {}",
                    opcode,
                ))),
            }
        }

        let seq_desc = match self.regs.k {
            None => "none".to_string(),
            Some(n) => format!("{:02o}", n),
        };

        // Fetch the current instruction into the N register.
        {
            let span = span!(Level::INFO,
			     "fetch",
			     seq=%seq_desc,
			     p=?self.regs.p);
            let _enter = span.enter();
            event!(Level::TRACE, "current sequence is {}", seq_desc);
            self.fetch_instruction(mem)
                .map_err(|alarm| (alarm, self.regs.p))?;
        }

        // Save the old program counter.
        let p = self.regs.p;
        self.set_program_counter(ProgramCounterChange::CounterUpdate);

        let elapsed_time = self.estimate_execute_time_ns(&self.regs.n);

        let result = if let Some(sym) = self.regs.n_sym.as_ref() {
            let inst = sym.to_string();
            let span = span!(Level::INFO,
			     "xop",
			     seq=%seq_desc,
			     p=?p,
			     op=%sym.opcode());
            let _enter = span.enter();
            event!(Level::TRACE, "executing instruction {}", &sym);
            match execute(p, &sym.opcode(), self, system_time, mem) {
                Ok(None) => {
                    // This is the usual case; the call to
                    // set_program_counter above will have incremented
                    // P.
                    Ok(())
                }
                Ok(Some(pc_change)) => {
                    // Instructions which return
                    // ProgramCounterChange::CounterUpdate do so in
                    // order perform a skip over the next instruction.
                    event!(Level::TRACE, "program counter change: {:?}", &pc_change);
                    self.set_program_counter(pc_change);
                    Ok(())
                }
                Err(e) => {
                    event!(Level::WARN, "instruction {} raised alarm {}", inst, e);
                    self.set_program_counter(ProgramCounterChange::Stop(p));
                    Err((e, p))
                }
            }
        } else {
            event!(
                Level::DEBUG,
                "fetched instruction {:?} is invalid",
                &self.regs.n
            );
            self.alarm_unit
                .fire_if_not_masked(self.invalid_opcode_alarm())
                .map_err(|e| (e, p))
        };

        // We have completed an attempt to execute instruction.  It
        // may not have been successful, so we cannot set the value of
        // prev_hold unconditionally. Determine whether this
        // instruction should be followed by a change of sequence.
        match result {
            Ok(()) => match self.select_sequence() {
                SequenceSelection::Continue => Ok((elapsed_time, RunMode::Running)),
                SequenceSelection::InLimbo => Ok((elapsed_time, RunMode::InLimbo)),
                SequenceSelection::Change(seq) => {
                    // The (previously) current sequence dropped
                    // out, or seq is a higher priority than the
                    // current sequence
                    self.change_sequence(self.regs.k, seq);
                    Ok((elapsed_time, RunMode::Running))
                }
            },
            Err((alarm, address)) => Err((alarm, address)),
        }
        // self.regs.k now identifies the sequence we should be
        // running and self.regs.p contains its program counter.
    }

    fn get_config(&self) -> SystemConfiguration {
        let cf = self.regs.n.configuration();
        self.regs.get_f_mem(cf)
    }

    fn fetch_operand_from_address_with_exchange(
        &mut self,
        mem: &mut MemoryUnit,
        operand_address: &Address,
        existing_dest: &Unsigned36Bit,
        update_e: &UpdateE,
    ) -> Result<(Unsigned36Bit, ExtraBits), Alarm> {
        let (memword, extra) =
            self.fetch_operand_from_address_without_exchange(mem, operand_address, update_e)?;
        let exchanged = exchanged_value_for_load(&self.get_config(), &memword, existing_dest);
        Ok((exchanged, extra))
    }

    fn fetch_operand_from_address_without_exchange(
        &mut self,
        mem: &mut MemoryUnit,
        operand_address: &Address,
        update_e: &UpdateE,
    ) -> Result<(Unsigned36Bit, ExtraBits), Alarm> {
        let meta_op: MetaBitChange = if self.trap.set_metabits_of_operands() {
            MetaBitChange::Set
        } else {
            MetaBitChange::None
        };
        match mem.fetch(operand_address, &meta_op) {
            Ok((word, extra_bits)) => {
                if extra_bits.meta && self.trap.trap_on_operand() {
                    self.raise_trap();
                }
                if update_e == &UpdateE::Yes {
                    self.regs.e = word;
                }
                Ok((word, extra_bits))
            }
            Err(MemoryOpFailure::NotMapped(addr)) => {
                self.alarm_unit.fire_if_not_masked(Alarm::QSAL(
                    self.regs.n,
                    BadMemOp::Read(Unsigned36Bit::from(addr)),
                    format!(
                        "memory unit indicated address {:o} is not mapped",
                        operand_address
                    ),
                ))?;
                // QSAL is masked to we have to return some value, but
                // we don't know what the TX-2 did in this case.
                return Err(self.alarm_unit.always_fire(Alarm::ROUNDTUITAL(
			format!(
			    "memory unit indicated address {:o} is not mapped and we don't know what to do when QSAL is masked",
			    operand_address
			))));
            }
            Err(MemoryOpFailure::ReadOnly(_, _)) => unreachable!(),
        }
    }

    fn memory_store_without_exchange(
        &mut self,
        mem: &mut MemoryUnit,
        target: &Address,
        value: &Unsigned36Bit,
        update_e: &UpdateE,
        meta_op: &MetaBitChange,
    ) -> Result<(), Alarm> {
        event!(
            Level::TRACE,
            "memory_store_without_exchange: write @{:>06o} <- {:o}",
            target,
            value,
        );
        if &UpdateE::Yes == update_e {
            // The E register gets updated to the value we want to
            // write, even if we cannot actually write it (see example
            // 10 on page 3-17 of the Users Handbook).
            self.regs.e = *value;
        }
        if let Err(e) = mem.store(target, value, meta_op) {
            self.alarm_unit.fire_if_not_masked(Alarm::QSAL(
                self.regs.n,
                BadMemOp::Write(Unsigned36Bit::from(*target)),
                format!("memory store to address {:#o} failed: {}", target, e,),
            ))?;
            Ok(()) // QSAL is masked, so just carry on.
        } else {
            Ok(())
        }
    }

    fn memory_store_with_exchange(
        &mut self,
        mem: &mut MemoryUnit,
        target: &Address,
        value: &Unsigned36Bit,
        existing: &Unsigned36Bit,
        update_e: &UpdateE,
        meta_op: &MetaBitChange,
    ) -> Result<(), Alarm> {
        self.memory_store_without_exchange(
            mem,
            target,
            &exchanged_value_for_store(&self.get_config(), value, existing),
            update_e,
            meta_op,
        )
    }

    /// Determine the address of the operand for instructions that use
    /// indexing.
    fn operand_address_with_optional_defer_and_index(
        self: &mut ControlUnit,
        mem: &mut MemoryUnit,
    ) -> Result<Address, Alarm> {
        self.resolve_operand_address(mem, None)
    }

    /// Determine the address of the operand for instructions that do
    /// not use indexing.
    fn operand_address_with_optional_defer_without_index(
        self: &mut ControlUnit,
        mem: &mut MemoryUnit,
    ) -> Result<Address, Alarm> {
        self.resolve_operand_address(mem, Some(Unsigned6Bit::ZERO))
    }

    /// Resolve the address of the operand of the current instruction,
    /// leaving this address in the Q register.  If
    /// `initial_index_override` is None, the final j bits are taken
    /// from the initial contents of the N register.  Otherwise
    /// (e.g. for JNX) they are taken to be the value in
    /// initial_index_override.
    fn resolve_operand_address(
        self: &mut ControlUnit,
        mem: &mut MemoryUnit,
        initial_index_override: Option<Unsigned6Bit>,
    ) -> Result<Address, Alarm> {
        // The deferred addressing process may be performed more than
        // once, in other words it is a loop.  This is explained in
        // section 9-7, "DEFERRED ADDRESSING CYCLES" of Volume 2 of
        // the technical manual.
        //
        // See also "TX-2 Introductory Notes" by A. Vanderburgh, 24
        // February 1959, available from the UMN collection (BCI61 Box
        // 8).
        let mut seen_deferred_addresses: HashSet<Address> = HashSet::new();
        while let OperandAddress::Deferred(physical) = self.regs.n.operand_address() {
            // In effect, this loop emulates a non-ultimate deferred
            // address cycle.
            //
            // According to the description of PK3 on page 5-9 of the
            // User handbook, the deferred address calculation and
            // indexing occurs in (i.e. by modifying) the N register.
            // "TX-2 Introductory Notes" explains the same thing.
            //
            // JPX and JNX seem to be handled differently, but I don't
            // think I understand exactly what the difference is
            // supposed to be. "TX-2 Introductory Notes" points out
            // that in JPX and JNX, the j bits are used for something
            // other than indexing, so the "handled differently" may
            // just be that deferred addressing is the only way to use
            // indexing in combination with JPX and JNX.
            //
            // (Vol 2, page 12-9): It should also be noted that the
            // N₂.₉ bit is presented as an input to the X Adder only
            // when no deferred address cycles are called for.  When
            // PI¹₂, the input to the X Adder from the N₂.₉ position
            // is forced to appear as a ZERO.
            event!(
                Level::TRACE,
                "deferred addressing: deferred address is {:o}",
                &physical
            );
            let meta_op = if self.trap.set_metabits_of_deferred_addresses() {
                MetaBitChange::Set
            } else {
                MetaBitChange::None
            };
            let fetched = match mem.fetch(&physical, &meta_op) {
                Err(e) => {
                    let msg = || {
                        format!(
                            "address {:#o} out of range while fetching deferred address: {}",
                            &physical, e
                        )
                    };

                    self.alarm_unit.fire_if_not_masked(Alarm::QSAL(
                        self.regs.n,
                        BadMemOp::Read(Unsigned36Bit::from(physical)),
                        msg(),
                    ))?;
                    // QSAL is masked.  I don't know what the TX-2 did in this situation.
                    return Err(self.alarm_unit.always_fire(Alarm::ROUNDTUITAL(format!(
                        "we don't know how to handle {} when QSAL is masked",
                        msg()
                    ))));
                }
                Ok((word, extra)) => {
                    if extra.meta && self.trap.trap_on_deferred_address() {
                        self.raise_trap();
                    }

                    // The TX2 performs indexation on deferred
                    // addreses.  Indeed, the "TX-2 Introductory
                    // Notes" by A. Vanderburg imply that the ability
                    // to do this is the motivation for having
                    // deferred addressing at all (see section
                    // "Deferred Addressing" in that document).
                    //
                    // This idea is also supported by the fact that
                    // the left subword of deferred addresses used in
                    // plugboard programs can be nonzero, and on the
                    // fact that the description of the SKM
                    // instruction notes "SKM is therefore
                    // non-indexable except through deferred
                    // addressing".
                    let (left, right) = subword::split_halves(word);
                    let mask: Unsigned18Bit = Unsigned18Bit::from(63_u8);
                    let j6: Unsigned6Bit = Unsigned6Bit::try_from(left.bitand(mask)).unwrap();
                    let next = Address::from(right).index_by(self.regs.get_index_register(j6));
                    event!(Level::TRACE,
			   "deferred addressing: fetched full word is {:o},,{:o}; j={:o}, using {:o} as the next address",
			   &left, &right, &j6, &next,
		    );
                    if !seen_deferred_addresses.insert(next) {
                        // A `false` return indicates that the map
                        // already contained `next`, meaning that we
                        // have a loop.
                        //
                        // Detection of this kind of loop is not a
                        // feature of the TX-2.  The "TX-2
                        // Introductory Notes" document explicitly
                        // states, "In fact, you can inadvertantly
                        // [sic] defer back to where you started and
                        // get a loop less than one instruction long".
                        return Err(self
                            .alarm_unit
                            .always_fire(Alarm::DEFERLOOPAL { address: right }));
                    }
                    next
                }
            };

            // We update the lower 18 bits (i.e. right half) of N with
            // the value we just loaded from memory.
            let unchanged_left = subword::left_half(Unsigned36Bit::from(self.regs.n));
            self.update_n_register(subword::join_halves(
                unchanged_left,
                Unsigned18Bit::from(fetched),
            ))?;
        }
        let physical_address = match self.regs.n.operand_address() {
            // Cannot be a deferred address any more, as loop above
            // loops until the address is not deferred.
            OperandAddress::Deferred(_) => unreachable!(),
            OperandAddress::Direct(physical_address) => physical_address,
        };
        // The defer bit in N is (now) not set.  Emulate a regular or
        // ultimate address cycle.  That is, add the index value to
        // the operand address.  While the index_address field in the
        // instruction is unsigned (following the conventions in the
        // assembly source), the indexation operation itself uses
        // signed arithmetic (see the explanation in the doc comment
        // for the IndexBy trait).
        let j = match initial_index_override {
            None => self.regs.n.index_address(),
            Some(overridden) => overridden,
        };
        let delta = self.regs.get_index_register(j); // this is Xj.

        // A number of things expect that the "most recent data (memory)
        // reference" is saved in register Q.  14JMP (a.k.a. JPQ) makes
        // use of this, for example.
        self.regs.q = physical_address.index_by(delta);

        // TODO: figure out if other parts of the system documentation
        // definitely expect the physical operand address to be
        // written back into the N register (in a
        // programmer-detectable way).
        //
        // "TX-2 Introductory Notes" states that this happens, but the
        // question is whether the programmer can detect it.
        Ok(self.regs.q)
    }

    fn memory_read_and_update_with_exchange<F>(
        &mut self,
        mem: &mut MemoryUnit,
        target: &Address,
        update_e: &UpdateE,
        transform: F,
    ) -> Result<(), Alarm>
    where
        F: FnOnce(Unsigned36Bit) -> Unsigned36Bit,
    {
        // We unconditionally perform the memory read.  But in the
        // real TX-2 there are cases where the read may not actually
        // need to happen.  For example the instruction `⁰STA T` is
        // implemented by a call to this function but does not need to
        // read from `target` although similar instructions might.
        // For example, `²STA T` modifies L(T) but not R(T) and so if
        // there were a hardware parity error affecting T, this
        // instruction would likely fail on the real hardware.
        match self.fetch_operand_from_address_without_exchange(mem, target, &UpdateE::No) {
            Ok((existing, _meta)) => {
                let newval = transform(existing);
                // TODO: handle "memory" stores to AE registers.
                self.memory_store_with_exchange(
                    mem,
                    target,
                    &newval,
                    &existing,
                    update_e,
                    &MetaBitChange::None,
                )
            }
            Err(Alarm::QSAL(inst, BadMemOp::Read(addr), msg)) => {
                // That read operation just failed.  So we handle this
                // as a _write_ failure, meaning that we change
                // BadMemOp::Read to BadMemOp::Write.
                self.alarm_unit.fire_if_not_masked(Alarm::QSAL(
                    inst,
                    BadMemOp::Write(addr),
                    msg,
                ))?;
                Ok(()) // QSAL is masked, we just carry on (the DPX instruction has no effect).
            }
            Err(other) => Err(other),
        }
    }

    fn dismiss(&mut self, reason: &str) {
        if let Some(current_seq) = self.regs.k {
            event!(
                Level::DEBUG,
                "dismissing current sequence (reason: {})",
                reason
            );
            self.regs.flags.lower(&current_seq);
            self.regs.current_sequence_is_runnable = false;
        }
    }

    fn dismiss_unless_held(&mut self, reason: &str) -> bool {
        if self.regs.n.is_held() {
            false
        } else {
            self.dismiss(reason);
            true
        }
    }
}

impl Default for ControlUnit {
    fn default() -> Self {
        Self::new()
    }
}
