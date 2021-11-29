use std::error;
/// The TX2 has several different kinds of memory.  Some of it (known
/// as S, T, U and V memories) are directly addressible.  These are
/// described in Chapter 11 (Volume 2) of the technical manual.
///
/// Locations of S, U and T memory are taken from page 5-13 of the Users Handbook (which describes memory alarms).
/// The location of V memory was deduced from the descrption of the plugboard in the user guide (which states that the plugboards end at 0377777) and the
///
/// The TX-2 also has other kinds of memory directly accessible to the
/// programmer but which don't have memory addresses.  These are the
/// F-memory and the X-memory.
///
/// Lastly there are some other memory stores which aren't accessible
/// to the programmer.  These include the M and N registers (see
/// below).
///
/// The memory system of the TX2 is described in chapters 4 and 11
/// ("Memory Element") of the TX-2 Technical Manual.
///
/// I don't currently know of a surviving copy of chapter 4, since
/// presumably it is in Volume 1 of the technical manual.  I don't
/// have a copy of that.
///
/// # Addressible Memory
///
/// ## S Memory
///
/// 65536 words (according to the WJCC papers, 1957).
///
/// ## T Memory
///
/// Mapped at 0200000 to 0207777 (User Handbook, page 5-13).  Hence
/// 4096 words.
///
/// ## U Memory
///
/// Mapped at 210000 to 217777 (User Handbook, page 5-13).  U memory
/// is not implemented.
///
/// ## V Memory
///
/// V memory consists of two groups; static (Vᴛ) and flip-flop (Vꜰꜰ)
/// memories.  Within the V memory there are the A (accumulator), B,
/// C, D, E registers.  The V memory used only 7 bits of the P/Q
/// (instruction/data address register) registers, meaning that it is
/// 128 (200 octal) words in size.
///
/// ### Plugboard
///
/// Two plugboards (A and B) each contain 16 registers of 37 bits each
/// (see section 11-7.1 in Volume 2 of the Technical Manual).  I'm not
/// certain whether the plugboard locations have meta bits (or parity bits).
///
/// The standard "memory clear" boot program in Plugboard A appears to
/// test the meta bit of location 377 744, which is in Plugboard A.
/// This may simply be a convenient way of determining whether
/// Plugboard B is set up before trying to execute code in it.
///
/// There is also a priority patch panel (technical manual volume 2,
/// section 12-7.2) but that is likely not memory-mapped.
///
/// ### Toggle Switches
///
/// 24 registers of 37 bits each.  However, as of June 1961, only
/// registers 0-17 were implemented.
///
/// ### Shaft Encoder
///
/// Mapped at 0377620.  Each shaft encoder emits a 9-bit number; four
/// shaft encoders together emit a 36-bit number; a toggle switch
/// provides the value of the meta bit (the user guide says this is a
/// push-button).
///
/// ### Real-Time Clock
///
/// Mapped at 0377630.  36-bit counter plus meta bit.  Counter
/// overflow (every 7.6 days) causes end-around carry.  Increments
/// every 10 microseconds.
///
/// ### External Input Register
///
/// Mapped at 0377621.  Reflects the state of 37 external
/// push-buttons.  Holding down a button produces a 1 bit.
///
/// ### Flip-Flop Memory
///
/// Registers A, C, C, D, E are memory-mapped.
///
/// The Programming Examples document, Program I states that A is
/// mapped at address 0377740.  The Jul 1961 Users Handbook (page 3-3)
/// states that it is mapped at address 0377604.  The user guide also
/// shows (page 5-17) that 0377740 is the first address of Plugboard
/// "B", so perhaps the arithmetic unit registers were moved to make
/// room for a second plugboard.  In any case, we're going with the
/// description in the Users Handbook.
///
/// A: 0377604
/// B: 0377605
/// C: 0377606
/// D: 0377607
/// E: 0377610
///
/// # Non-Addressible Memory
///
/// ## The M Register
///
/// The M register buffers memory stores and fetches.  Memory
/// transfers which occur via the E register cause the current
/// contents of the E register to be temporarily saved into the M
/// register (see Technical Manual Volume 2, section 11-7.6).
///
/// ## The N register
///
/// The N register holds the current instruction.  During deferred
/// address cycles, the N register holds the contents of a deferred
/// operand load.
///
/// ## F-memory
///
/// The F-memory contains 32 locations, each 16 bits wide.
///
/// The F-memory stores sytem configuration values; the configuration
/// field within each instruction is used as a lookup index into the
/// F-memory. The system configuration fetched from the F-memory
/// determines how memory transfers are carried out.  That is, how
/// word quarters are permuted, which quarters are active and whether
/// and how sign-extension ocurs ("subword form") on the value fetched
/// or to be written.
///
/// The F-memory can be examined and modified by the programmer using
/// the FLF and FLG (for read) and SPF and SPG (for write)
/// instructions.  See pages 3-54 and 3-55 of the User Guide.
///
/// F-memory location 0 (corresponding to a zero-valued configuraiton
/// field in the instruction: full 36-bit word form, no permutation,
/// all quarters active) is not modifiable.
///
/// Decoding of F-memory values is summarised in Figure 12-39
/// (Technical Manual, volume 2).
///
/// ## X-memory
///
/// The X memory is described in section 12-3 (Vol 2) of the Technical Manual.
///
/// The X memory is a 64 register 19-bit (magnetic core) memory.
///
/// ## Flag Register
///
/// The Flag register consists of 33 flip-flops, one for each
/// sequence.  A value 1 in a bit indicates that the associated I/O
/// unit requests attention.  See section 12-7.4 (volume 2) of the
/// Technical Manual.
///
/// # Parity
///
/// Various stores in the TX-2 include a parity bit, but these are not
/// all emulated because only some are programmer-detectable.  The SKM
/// instruction (for example) allows the programmer to detect the
/// state of a parity bit.   SKM does not allow the parity bit to be
/// altered though, so we simply compute its value on the fly.
///
/// # Memory map
///
/// 0000000 Start of S memory (Technical Manual Volume 2, sec 12-2.8)
/// 0177777 Last word of S memory (WJCC paper gives size as 65536 words)
///
/// 0200000 Start of T memory
/// 0207777 Last location in T memory.
/// 0210000 Start of U memory
/// 0217777 Last location in U memory.
///
/// 0377600 Start of V-memory.
///
/// 0377604 A register
/// 0377605 B register
/// 0377606 C register
/// 0377607 D register
/// 0377610 E register
///
/// 0377620 Knob (Shaft Encoder) Register (User Handbook, 5-20)
/// 0377621 External Input Register (User Handbook, 5-20)
/// 0377630 Real Time Clock
///
/// 0377710 Location of CODABO start point 0
/// 0377711 Location of CODABO start point 1
/// 0377712 Location of CODABO start point 2
/// 0377713 Location of CODABO start point 3
/// 0377714 Location of CODABO start point 4
/// 0377715 Location of CODABO start point 5
/// 0377716 Location of CODABO start point 6
/// 0377717 Location of CODABO start point 7
///
/// 0377740 Plugboard B memory start
///         The plugboard program code is given
///         in section 5-5.2 (page 5-27) of the
///         User Handbook.
/// 0377740 8 (Octal 10) words of data used by
///         SPG instructions of the code at
///         0377750 to set the standard configuration
///         in F-memory.
/// 0377750 Standard program, Set Configuration
///         Loads the standard configuration into
///         F-memory.  Then proceed to 0377760.
/// 0377757 Last location in Plugboard B.
/// 0377760 Plugboard A memory start
/// 0377760 Standard program, Read In Reader Leader.
///         Reads the first 21 words from paper tape
///         into registers 3 through 24 of S-memory,
///         then goes to register 3.
///         The 21 words would be the "standard reader leader"
///         of binary paper tapes.  The code for the standard
///         reader leader is given in the User Handbook,
///         section 5-5.2.
/// 0377770 Standard program, Clear Memory / Smear Memory
///         Sets all of S, T, U memory to 0 on the left
///         and the address of itself on the right.
///         Meta bits are not affected (User Guide 5-25).
///         Automatically proceeds to 037750 (Set
///         Configuration).
/// 0377777 Plugboard A memory end; end of V memory; end of memory.
use std::fmt::{Display, Error, Formatter};

use base::prelude::*;
use base::instruction::BitSelector;

pub const S_MEMORY_START: u32 = 0o0000000;
pub const S_MEMORY_SIZE: u32 = 1 + 0o0177777;
pub const T_MEMORY_START: u32 = 0o0200000;
pub const T_MEMORY_SIZE: u32 = 1 + 0o0207777 - 0o0200000;
pub const U_MEMORY_START: u32 = 0o0210000;
pub const U_MEMORY_SIZE: u32 = 1 + 0o0217777 - 0o0210000;
pub const V_MEMORY_START: u32 = 0o0377600;
pub const V_MEMORY_SIZE: u32 = 1 + 0o0377777 - 0o0377600;

pub const STANDARD_PROGRAM_CLEAR_MEMORY: Address = Address::MAX.and(0o0377770_u32);

#[derive(Debug)]
pub enum MemoryOpFailure {
    NotMapped,

    // I have no idea whether the real TX-2 alarmed on writes to
    // things that aren't really writeable (e.g. shaft encoder
    // registers).  But by implemeting this we may be able to answer
    // that question if some real (recovered) program writes to a
    // location we assumed would be read-only.
    ReadOnly,
}

impl Display for MemoryOpFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        f.write_str(match self {
            MemoryOpFailure::NotMapped => "address is not mapped to functioning memory",
            MemoryOpFailure::ReadOnly => "address is mapped to read-only memory",
        })
    }
}

impl error::Error for MemoryOpFailure {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MetaBitChange {
    None,
    Set,
}

// Clear,
// Flip,			// not used for fetch/store

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitChange {
    Clear,
    Set,
    Flip
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WordChange {
    pub bit: BitSelector,
    pub bitop: Option<BitChange>,
    pub cycle: bool,
}

impl WordChange {
    pub fn will_mutate_memory(&self) -> bool {
	if self.cycle {
	    true
	} else if self.bitop.is_none() {
	    false
	} else {
	    match self.bit {
		BitSelector { quarter: _, bitpos: 0 } => false,
		// bit positions 11 and 12 are parity and computed
		// parity which we cannot change.
		BitSelector { quarter: _, bitpos: 11|12 } => false,
		_ => true,
	    }
	}
    }
}


pub trait MemoryMapped {
    // Fetch a word.
    fn fetch(
        &mut self,
        addr: &Address,
        meta: &MetaBitChange,
    ) -> Result<(Unsigned36Bit, ExtraBits), MemoryOpFailure>;

    // Store a word.
    fn store(
        &mut self,
        addr: &Address,
        value: &Unsigned36Bit,
        meta: &MetaBitChange,
    ) -> Result<(), MemoryOpFailure>;

    // Mutate a bit in-place, returning its previous value.
    fn change_bit(
        &mut self,
        addr: &Address,
	op: &WordChange,
    ) -> Result<Option<bool>, MemoryOpFailure>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExtraBits {
    pub meta: bool,
    pub parity: bool,
}
