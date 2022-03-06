// This module emulates the TX-2's STUV memory.
///
/// STUV memory is memory-mapped.  That is, each location (which the
/// documentation describes as a "register") has an address between 0
/// and 377777 octal, inclusive.  Even registers that we would
/// describe today as being "CPU registers" (i.e. registers A-E) have
/// addresses.  See memorymap.rs for details of the memory map.
///
/// Other memories (for example X memory and F memory) are emulated in
/// control.rs.
///
/// The TX-2 uses 36-bit words.  We use Unsigned36Bit (defined in
/// onescomplement/unsigned.rs) to represent this.  The TX-2 has a
/// number of memories which have differing widths.  Its STUV memory
/// (which today we might describe as "main memory") has 38 bitplanes.
/// 36 for each of the value bits, plus two more:
///
/// - Meta bit; this can be read or written using special
///   memory-related instructions.  Programs can also set up a mode of
///   operation in which various operations (e.g.  loading an operand
///   or instruction) causes a meta bit to be set.
/// - Parity bit: value maintained and checked by the system.
///   Readable via the SKM instruction.  The emulator behaves as if
///   parity errors never occur.
///
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
#[cfg(test)]
use std::ops::RangeInclusive;

use tracing::{event, Level};

use base::prelude::*;

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
    ReadOnly(ExtraBits),
}

impl Display for MemoryOpFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            MemoryOpFailure::NotMapped => "address is not mapped to functioning memory",
            MemoryOpFailure::ReadOnly(_) => "address is mapped to read-only memory",
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
    Flip,
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
            // Only bit positions 1-9 (normal bits) and 10 (meta) are
            // modifiable.
            !matches!(
                self.bit,
                BitSelector {
                    quarter: _,
                    bitpos: 0 | 11 | 12
                }
            )
        }
    }
}

pub trait MemoryMapped {
    /// Fetch a word.
    fn fetch(
        &mut self,
        addr: &Address,
        meta: &MetaBitChange,
    ) -> Result<(Unsigned36Bit, ExtraBits), MemoryOpFailure>;

    /// Store a word.
    fn store(
        &mut self,
        addr: &Address,
        value: &Unsigned36Bit,
        meta: &MetaBitChange,
    ) -> Result<(), MemoryOpFailure>;

    /// Mutate a bit in-place, returning its previous value.
    fn change_bit(
        &mut self,
        addr: &Address,
        op: &WordChange,
    ) -> Result<Option<bool>, MemoryOpFailure>;

    /// Cycle a memory location one place to the left (as in hTSD).
    fn cycle_word(&mut self, addr: &Address) -> Result<ExtraBits, MemoryOpFailure>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExtraBits {
    pub meta: bool,
    pub parity: bool,
}

#[derive(Clone, Copy)]
struct MemoryWord(u64); // Not public.
const WORD_BITS: u64 = 0x0FFFFFFFFF;
const META_BIT: u64 = 0x1000000000;

impl Debug for MemoryWord {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:>012o}", self.0)
    }
}

fn compute_extra_bits(w: u64) -> ExtraBits {
    let parity: bool = match w.count_ones() & 1 {
        0 => false,
        1 => true,
        _ => unreachable!(),
    };
    let meta: bool = w & META_BIT != 0;
    ExtraBits { meta, parity }
}

impl From<&MemoryWord> for (Unsigned36Bit, ExtraBits) {
    fn from(w: &MemoryWord) -> (Unsigned36Bit, ExtraBits) {
        let valuebits: u64 = w.0 & WORD_BITS;
        (
            Unsigned36Bit::try_from(valuebits).unwrap(),
            compute_extra_bits(w.0),
        )
    }
}

impl From<&mut MemoryWord> for (Unsigned36Bit, ExtraBits) {
    fn from(w: &mut MemoryWord) -> (Unsigned36Bit, ExtraBits) {
        let valuebits: u64 = w.0 & WORD_BITS;
        (
            Unsigned36Bit::try_from(valuebits).unwrap(),
            compute_extra_bits(w.0),
        )
    }
}

#[test]
fn test_meta_bit_position() {
    println!("Meta bit is {:>012o}", &META_BIT);
    assert_eq!(
        36,
        META_BIT.trailing_zeros(),
        "meta bit should immediately follow data bits"
    );
    assert_eq!(
        1,
        META_BIT.count_ones(),
        "there should be only one meta bit"
    );
}

#[test]
fn test_word_bits() {
    dbg!(&WORD_BITS);
    println!("WORD_BITS is {:>012o}", &WORD_BITS);
    assert_eq!(
        0,
        WORD_BITS.trailing_zeros(),
        "word bits should begin at the least significant bit"
    );
    assert_eq!(36, WORD_BITS.count_ones(), "words should be 36 bits wide");
}

impl MemoryWord {
    fn set_meta_bit(&mut self, value: &bool) {
        if *value {
            self.0 |= META_BIT
        } else {
            self.0 &= !META_BIT;
        }
    }

    /// Update the value of the word in memory without changing the
    /// meta bit.
    fn set_value(&mut self, value: &Unsigned36Bit) {
        self.0 = (self.0 & META_BIT) | (u64::from(*value) & WORD_BITS);
    }
}

impl Default for MemoryWord {
    fn default() -> MemoryWord {
        MemoryWord(0)
    }
}

fn default_filled_memory_vec(size: u32) -> Vec<MemoryWord> {
    let size: usize = size.try_into().expect("unexpectedly large memory element");
    let mut result = Vec::with_capacity(size);
    while result.len() < size {
        result.push(MemoryWord::default());
    }
    result
}

#[derive(Debug)]
pub struct MemoryUnit {
    s_memory: Vec<MemoryWord>,
    t_memory: Vec<MemoryWord>,
    u_memory: Option<Vec<MemoryWord>>,
    v_memory: VMemory,
}

#[derive(Debug, Eq, PartialEq)]
pub enum MemoryAccess {
    Read,
    Write,
}

pub enum MemoryDecode {
    S(usize),
    T(usize),
    U(usize),
    V(usize),
}

fn decode(address: &Address) -> Option<MemoryDecode> {
    // MemoryDecode32 is a workaround for the fact that our address
    // arithmetic uses u32 but we want to return an offset of type
    // usize.
    enum MemoryDecode32 {
        S(u32),
        T(u32),
        U(u32),
        V(u32),
    }
    let addr: u32 = u32::from(address);
    let decoded = {
        if addr < T_MEMORY_START {
            Some(MemoryDecode32::S(addr - S_MEMORY_START))
        } else if addr < U_MEMORY_START {
            Some(MemoryDecode32::T(addr - T_MEMORY_START))
        } else if addr < (U_MEMORY_START + U_MEMORY_SIZE) {
            Some(MemoryDecode32::U(addr - U_MEMORY_START))
        } else if addr < V_MEMORY_START {
            // This address is valid, but this memory region (after the U
            // memory, before the V memory) is not mapped to anything.
            None
        } else if (V_MEMORY_START..V_MEMORY_START + V_MEMORY_SIZE).contains(&addr) {
            Some(MemoryDecode32::V(addr - V_MEMORY_START))
        } else {
            // The end of V memory is the highest address it is possible
            // to form in 17 bits.  So, it should not be possible to form
            // an invalid address in an Address struct, so we should not
            // be able to get here.
            panic!(
                "Access to memory address {:?} should be impossible",
                &address
            );
        }
    };
    // This code should not panic since the input Address type should
    // not allow an address which is large enough that it can't be
    // represented in a usize value.  The largest offset which the
    // code above should compute is the last address of S-memory, and
    // that fits into 16 bits.
    decoded.map(|d| match d {
        MemoryDecode32::S(addr) => MemoryDecode::S(addr.try_into().unwrap()),
        MemoryDecode32::T(addr) => MemoryDecode::T(addr.try_into().unwrap()),
        MemoryDecode32::U(addr) => MemoryDecode::U(addr.try_into().unwrap()),
        MemoryDecode32::V(addr) => MemoryDecode::V(addr.try_into().unwrap()),
    })
}

pub struct MemoryConfiguration {
    pub with_u_memory: bool,
}

impl MemoryUnit {
    pub fn new(config: &MemoryConfiguration) -> MemoryUnit {
        MemoryUnit {
            s_memory: default_filled_memory_vec(S_MEMORY_SIZE),
            t_memory: default_filled_memory_vec(T_MEMORY_SIZE),
            u_memory: if config.with_u_memory {
                Some(default_filled_memory_vec(U_MEMORY_SIZE))
            } else {
                None
            },
            v_memory: VMemory::new(),
        }
    }

    fn access(
        &mut self,
        access_type: &MemoryAccess,
        addr: &Address,
    ) -> Result<Option<&mut MemoryWord>, MemoryOpFailure> {
        match decode(addr) {
            Some(MemoryDecode::S(offset)) => Ok(Some(&mut self.s_memory[offset])),
            Some(MemoryDecode::T(offset)) => Ok(Some(&mut self.t_memory[offset])),
            Some(MemoryDecode::U(offset)) => {
                if let Some(u) = &mut self.u_memory {
                    Ok(Some(&mut u[offset]))
                } else {
                    Err(MemoryOpFailure::NotMapped)
                }
            }
            Some(MemoryDecode::V(_)) => self.v_memory.access(access_type, addr),
            None => Err(MemoryOpFailure::NotMapped),
        }
    }

    fn write_with_read_fallback<R, FW, FR>(
        &mut self,
        addr: &Address,
        on_write: FW,
        on_read: FR,
    ) -> Result<R, MemoryOpFailure>
    where
        FW: FnOnce(&mut MemoryWord) -> Result<R, MemoryOpFailure>,
        FR: FnOnce(&MemoryWord) -> Result<R, MemoryOpFailure>,
    {
        // If the memory address is not mapped at all, access will
        // return Err, causing the next line to bail out of this
        // function.
        match self.access(&MemoryAccess::Write, addr) {
            Ok(None) => {
                // The memory address is mapped to read-only memory.
                // For example, plugboard memory.
                //
                // We downgrade the bit operation to be non-mutating,
                // so that the outcome of the bit test is as it should
                // be, but the memory-write is inhibited.
                match self.access(&MemoryAccess::Read, addr) {
                    Ok(None) => unreachable!(),
                    Ok(Some(mem_word)) => on_read(mem_word),
                    Err(e) => Err(e),
                }
            }
            Ok(Some(mem_word)) => on_write(mem_word),
            Err(e) => Err(e),
        }
    }
}

/// Implement the heart of the change_bit() operation used by the SKM instruction.
fn change_word(mem_word: &mut MemoryWord, op: &WordChange) -> Option<bool> {
    // As the documentation for the SKM instruction (user
    // handbook, page 3-35) explains, we perform the
    // possible bit change before the possible rotate.
    let prev: Option<bool> = match (op.bit.quarter, op.bit.bitpos) {
        (_, 0) => None,
        (quarter, shift @ 1..=10) => {
            let mask: u64 = if shift < 10 {
                1 << ((u8::from(quarter) * 9) + (shift - 1))
            } else {
                META_BIT
            };
            let old_value: bool = (mem_word.0 & mask) != 0;
            match op.bitop {
                None => (),
                Some(BitChange::Clear) => mem_word.0 &= !mask,
                Some(BitChange::Set) => mem_word.0 |= mask,
                Some(BitChange::Flip) => mem_word.0 ^= mask,
            }
            Some(old_value)
        }
        // 11 is the partiy bit 12 is the computed parity.
        // Both a read-only, but I don't think an attempt
        // to modify them trips an alarm (at least, I
        // can't see any mention of this in the SKM
        // documentation).
        (_, 11 | 12) => {
            let (_wordval, extra_bits): (Unsigned36Bit, ExtraBits) = mem_word.into();
            Some(extra_bits.parity)
        }
        _ => unreachable!(),
    };
    if op.cycle {
        let (value, _extra) = mem_word.into();
        mem_word.set_value(&(value >> 1));
    }
    prev
}

impl MemoryMapped for MemoryUnit {
    fn fetch(
        &mut self,
        addr: &Address,
        side_effect: &MetaBitChange,
    ) -> Result<(Unsigned36Bit, ExtraBits), MemoryOpFailure> {
        match self.access(&MemoryAccess::Read, addr) {
            Err(e) => Err(e),
            Ok(None) => unreachable!(),
            Ok(Some(mem_word)) => {
                let (word, extra_bits) = mem_word.into();
                match side_effect {
                    MetaBitChange::None => (),
                    MetaBitChange::Set => {
                        if u32::from(addr) >= V_MEMORY_START {
                            // The description of the SKM instruction doesn't state
                            // explicitly that SKM works on V-memory, but since
                            // arithmetic unit registers are mapped to it, it would
                            // make sense.  However, there are clearly other locations
                            // in V memory (e.g. the plugboard) that we can't cycle.
                            if *side_effect != MetaBitChange::None {
                                // Changng meta bits in V memory is not allowed,
                                // see the longer comment in the store() method.
                                return Err(MemoryOpFailure::ReadOnly(extra_bits));
                            }
                        }
                        mem_word.set_meta_bit(&true)
                    }
                }
                Ok((word, extra_bits))
            }
        }
    }

    fn store(
        &mut self,
        addr: &Address,
        value: &Unsigned36Bit,
        meta: &MetaBitChange,
    ) -> Result<(), MemoryOpFailure> {
        if u32::from(addr) >= V_MEMORY_START && matches!(meta, MetaBitChange::Set) {
            // This is an attempt to set a meta bit in V memory.
            //
            // The meta bits of registers A..E cannot be
            // set by the "set metabits of.." modes of IOS 42.
            //
            // According to page 5-23 of the User Handbook, attempts
            // to set the metabit of registers via the MKC instruction
            // actually set the meta bit of the M register.  But I
            // don't know how that manifests to the programmer as an
            // observable behaviour.
            //
            // For now we generate a failure in the hope that we will
            // eventually find a program which performs this action,
            // and study it to discover the actual behaviour of the
            // TX-2 that the program expects.
            //
            // The User Handbook also states that V-memory locations
            // other than registers A-E cannot be written at all.
            //return Err(MemoryOpFailure::ReadOnly);
            return Ok(()); // ignore the write.
        }

        // TODO: instructions are not allowed to write to V-memory
        // (directly) though writes to registers are allowed.  For
        // example EXA is permitted, I think.
        match self.access(&MemoryAccess::Write, addr) {
            Err(e) => {
                return Err(e);
            }
            Ok(None) => {
                // Attempt to write to memory that cannot be written.
                // We just ignore this.
                return Ok(());
            }
            Ok(Some(mem_word)) => {
                mem_word.set_value(value);
                match meta {
                    MetaBitChange::None => (),
                    MetaBitChange::Set => mem_word.set_meta_bit(&true),
                }
            }
        }
        Ok(())
    }

    fn cycle_word(&mut self, addr: &Address) -> Result<ExtraBits, MemoryOpFailure> {
        fn on_write_cycle(mem_word: &mut MemoryWord) -> Result<ExtraBits, MemoryOpFailure> {
            let (value, extra_bits) = mem_word.into();
            mem_word.set_value(&(value << 1));
            Ok(extra_bits)
        }
        fn on_read_only_fail(mem_word: &MemoryWord) -> Result<ExtraBits, MemoryOpFailure> {
            event!(Level::DEBUG, "Cannot cycle read-only memory location");
            let (_word, extra_bits) = mem_word.into();
            Err(MemoryOpFailure::ReadOnly(extra_bits))
        }
        self.write_with_read_fallback(addr, on_write_cycle, on_read_only_fail)
    }

    fn change_bit(
        &mut self,
        addr: &Address,
        op: &WordChange,
    ) -> Result<Option<bool>, MemoryOpFailure> {
        let memory_access: MemoryAccess = if op.will_mutate_memory() {
            MemoryAccess::Write
        } else {
            MemoryAccess::Read
        };
        // If the memory address is not mapped at all, access will
        // return Err, causing the next line to bail out of this
        // function.
        match self.access(&memory_access, addr)? {
            None => {
                // The memory address is mapped to read-only memory.
                // For example, plugboard memory.
                //
                // We downgrade the bit operation to be non-mutating,
                // so that the outcome of the bit test is as it should
                // be, but the memory-write is inhibited.
                match self.access(&MemoryAccess::Read, addr)? {
                    None => unreachable!(),
                    Some(mem_word) => {
                        let downgraded_op = WordChange {
                            bit: op.bit,  // access the same bit
                            bitop: None,  // read-only
                            cycle: false, // read-only
                        };
                        assert!(!downgraded_op.will_mutate_memory()); // should be read-only now
                        Ok(change_word(mem_word, &downgraded_op))
                    }
                }
            }
            Some(mem_word) => Ok(change_word(mem_word, op)),
        }
    }
}

#[derive(Debug)]
struct VMemory {
    // Arithmetic registers have no meta bit.  Accesses which attempt
    // to read the meta bit of registers A, B, , D, E actually return
    // the meta bit in the M register.  This is briefly described on
    // page 5-23 of the User Handbook.
    //
    // It says,
    //
    // "The data reference metabit (M^4.10) can be detected only when
    // set (just as N^4.10 above).  Note that it can be changed
    // without a memory reference for it serves as the metabit of the
    // A, B, C, D, and E registers. (i.e., MKC_4.10 A or MKC_4.10 B
    // will change bit 4.10 of M."
    //
    // V memory in general does behave as if it has a meta bit.  For
    // example, there is a push-button on the console that acts as the
    // value of the meta bit of the shaft encoder register.
    //
    // Hence we store registers as MemoryWord values.  It's not clear
    // to me yet how to implement the behaviour described on page
    // 5-23.
    a_register: MemoryWord,
    b_register: MemoryWord,
    c_register: MemoryWord,
    d_register: MemoryWord,
    e_register: MemoryWord,

    unimplemented_shaft_encoder: MemoryWord,
    unimplemented_external_input_register: MemoryWord,
    unimplemented_rtc: MemoryWord,

    codabo_start_point: [MemoryWord; 8],
    plugboard: [MemoryWord; 32],
}

const fn standard_plugboard_internal() -> [MemoryWord; 32] {
    const fn mw(value: u64) -> MemoryWord {
        MemoryWord(META_BIT | (value & WORD_BITS))
    }
    // This data has not yet been double-checked and no tests
    // validate it, so it might be quite wrong.
    [
        // Plugboard memory starts with Plugboard B at 0o3777740.
        //
        // F-memory settings; these are verified against the
        // information from Table 7-2 by a test in the exchanger code.
        mw(0o_760342_340000),
        mw(0o_410763_762761),
        mw(0o_160142_140411),
        mw(0o_202163_162161),
        mw(0o_732232_230200),
        mw(0o_605731_730733),
        mw(0o_320670_750600),
        mw(0o_604331_330333),
        // 0o377750: standard program to load the F-memory settings
        // (this is not verified by the test in the exchanger code).
        mw(0o_002200_377740),
        mw(0o_042200_377741),
        mw(0o_102200_377742),
        mw(0o_142200_377743),
        mw(0o_202200_377744),
        mw(0o_242200_377745),
        mw(0o_302200_377746),
        mw(0o_342200_377747),
        // Plugboard A, 0o377760-0o377777
        // 0o0377760: Standard program: read in reader leader from paper tape
        mw(0o011254_000023),
        mw(0o001252_377763),
        mw(0o210452_030106),
        mw(0o001253_000005),
        mw(0o405754_000026),
        mw(0o760653_377764),
        mw(0o410754_377763),
        mw(0o140500_000003),
        // 0o0377770: Standard program: clear memory
        mw(0o001277_207777),
        mw(0o001677_777776),
        mw(0o140500_377773),
        mw(0o001200_777610),
        mw(0o760677_377771),
        mw(0o301712_377744),
        mw(0o000077_000000),
        mw(0o140500_377750),
    ]
}

#[cfg(test)]
pub fn get_standard_plugboard() -> Vec<Unsigned36Bit> {
    standard_plugboard_internal()
        .iter()
        .map(|mw| mw.into())
        .map(|(word, _meta)| word) // discard meta bits.
        .collect()
}

impl VMemory {
    fn new() -> VMemory {
        VMemory {
            a_register: MemoryWord::default(),
            b_register: MemoryWord::default(),
            c_register: MemoryWord::default(),
            d_register: MemoryWord::default(),
            e_register: MemoryWord::default(),
            codabo_start_point: [
                MemoryWord::default(),
                MemoryWord::default(),
                MemoryWord::default(),
                MemoryWord::default(),
                MemoryWord::default(),
                MemoryWord::default(),
                MemoryWord::default(),
                MemoryWord::default(),
            ],
            plugboard: standard_plugboard_internal(),
            unimplemented_shaft_encoder: MemoryWord::default(),
            unimplemented_external_input_register: MemoryWord::default(),
            unimplemented_rtc: MemoryWord::default(),
        }
    }

    fn access(
        &mut self,
        access_type: &MemoryAccess,
        addr: &Address,
    ) -> Result<Option<&mut MemoryWord>, MemoryOpFailure> {
        if access_type == &MemoryAccess::Write {
            // TODO: there appear to be some instructions which
            // special-case attempts to write to arithmetic unit
            // registers, so we may need a more sophisticated approach
            // here.
            return Ok(None);
        }
        match u32::from(addr) {
            0o0377604 => Ok(Some(&mut self.a_register)),
            0o0377605 => Ok(Some(&mut self.b_register)),
            0o0377606 => Ok(Some(&mut self.c_register)),
            0o0377607 => Ok(Some(&mut self.d_register)),
            0o0377610 => Ok(Some(&mut self.e_register)),
            0o0377620 => {
                // Shaft encoder is not yet implemented.
                event!(
                    Level::WARN,
                    "Reading the shaft encoder is not yet implemented"
                );
                Ok(Some(&mut self.unimplemented_shaft_encoder))
            }
            0o0377621 => {
                // Shaft encoder is not yet implemented.
                event!(
                    Level::WARN,
                    "Reading the external input register is not yet implemented"
                );
                Ok(Some(&mut self.unimplemented_external_input_register))
            }
            0o0377630 => {
                event!(
                    Level::WARN,
                    "Reading the real-time clock is not yet implemented"
                );
                Ok(Some(&mut self.unimplemented_rtc))
            }
            0o0377710 => Ok(Some(&mut self.codabo_start_point[0])), // CODABO Reset0
            0o0377711 => Ok(Some(&mut self.codabo_start_point[1])), // CODABO Reset1
            0o0377712 => Ok(Some(&mut self.codabo_start_point[2])), // CODABO Reset2
            0o0377713 => Ok(Some(&mut self.codabo_start_point[3])), // CODABO Reset3
            0o0377714 => Ok(Some(&mut self.codabo_start_point[4])), // CODABO Reset4
            0o0377715 => Ok(Some(&mut self.codabo_start_point[5])), // CODABO Reset5
            0o0377716 => Ok(Some(&mut self.codabo_start_point[6])), // CODABO Reset6
            0o0377717 => Ok(Some(&mut self.codabo_start_point[7])), // CODABO Reset7

            addr @ 0o0377740..=0o0377777 => {
                if let Ok(offset) = TryInto::<usize>::try_into(addr - 0o0377740) {
                    Ok(Some(&mut self.plugboard[offset]))
                } else {
                    // Unreachable because the matched range is
                    // not large enough to exceed the capacity of
                    // usize (which we assume is at least 2^16).
                    unreachable!()
                }
            }
            _ => Err(MemoryOpFailure::NotMapped),
        }
    }
}

#[cfg(test)]
fn all_physical_memory_addresses() -> RangeInclusive<u32> {
    let start = 0_u32;
    let end: u32 = u32::from(Unsigned18Bit::MAX) >> 1;
    start..=end
}

#[test]
fn test_write_all_mem() {
    let mut mem = MemoryUnit::new(&MemoryConfiguration {
        with_u_memory: false,
    });
    for a in all_physical_memory_addresses() {
        let addr: Address = Address::try_from(a).unwrap();
        // The point of this test is to verify that we con't have any
        // todo!()s in reachable code paths.
        drop(mem.access(&MemoryAccess::Write, &addr));
        // TODO: make this test fail if there is a ROUNDTUITAL.
    }
}

#[test]
fn test_read_all_mem() {
    let mut mem = MemoryUnit::new(&MemoryConfiguration {
        with_u_memory: false,
    });
    for a in all_physical_memory_addresses() {
        let addr: Address = Address::try_from(a).unwrap();
        // The point of this test is to verify that we con't have any
        // todo!()s in reachable code paths.
        drop(mem.access(&MemoryAccess::Read, &addr))
        // TODO: make this test fail if there is a ROUNDTUITAL.
    }
}
