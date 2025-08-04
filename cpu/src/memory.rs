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
use core::time::Duration;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
#[cfg(test)]
use std::ops::RangeInclusive;

use tracing::{Level, event};

use base::prelude::*;

use super::context::Context;
use mref::{MemoryRead, MemoryReadRef, MemoryWriteRef};

pub(crate) const S_MEMORY_START: u32 = 0o0000000;
pub(crate) const S_MEMORY_SIZE: u32 = 1 + 0o0177777;
pub(crate) const T_MEMORY_START: u32 = 0o0200000;
pub(crate) const T_MEMORY_SIZE: u32 = 1 + 0o0207777 - 0o0200000;
pub(crate) const U_MEMORY_START: u32 = 0o0210000;
pub(crate) const U_MEMORY_SIZE: u32 = 1 + 0o0217777 - 0o0210000;
pub(crate) const V_MEMORY_START: u32 = 0o0377600;
pub(crate) const V_MEMORY_SIZE: u32 = 1 + 0o0377777 - 0o0377600;

//pub const STANDARD_PROGRAM_CLEAR_MEMORY: Address = Address::new(u18!(0o0377770));
pub(crate) const STANDARD_PROGRAM_INIT_CONFIG: Address = Address::new(u18!(0o0377750));

#[derive(Debug, Clone)]
pub(crate) enum MemoryOpFailure {
    NotMapped(Address),

    // I have no idea whether the real TX-2 alarmed on writes to
    // things that aren't really writeable (e.g. shaft encoder
    // registers).  But by implemeting this we may be able to answer
    // that question if some real (recovered) program writes to a
    // location we assumed would be read-only.
    ReadOnly(Address, ExtraBits),
}

impl Display for MemoryOpFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            MemoryOpFailure::NotMapped(addr) => {
                write!(f, "address {addr:o} is not mapped to functioning memory")
            }
            MemoryOpFailure::ReadOnly(addr, _extra) => {
                write!(f, "address {addr:o}is mapped to read-only memory")
            }
        }
    }
}

impl error::Error for MemoryOpFailure {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum MetaBitChange {
    None,
    Set,
}

// Clear,
// Flip,                        // not used for fetch/store

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum BitChange {
    Clear,
    Set,
    Flip,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct WordChange {
    pub(crate) bit: BitSelector,
    pub(crate) bitop: Option<BitChange>,
    pub(crate) cycle: bool,
}

impl WordChange {
    pub(crate) fn will_mutate_memory(&self) -> bool {
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

pub(crate) trait MemoryMapped {
    /// Fetch a word.
    fn fetch(
        &mut self,
        ctx: &Context,
        addr: &Address,
        meta: &MetaBitChange,
    ) -> Result<(Unsigned36Bit, ExtraBits), MemoryOpFailure>;

    /// Store a word.
    fn store(
        &mut self,
        ctx: &Context,
        addr: &Address,
        value: &Unsigned36Bit,
        meta: &MetaBitChange,
    ) -> Result<(), MemoryOpFailure>;

    /// Mutate a bit in-place, returning its previous value.
    fn change_bit(
        &mut self,
        ctx: &Context,
        addr: &Address,
        op: &WordChange,
    ) -> Result<Option<bool>, MemoryOpFailure>;

    /// Cycle a memory location one place to the left (as in TSD).
    fn cycle_word(&mut self, ctx: &Context, addr: &Address) -> Result<ExtraBits, MemoryOpFailure>;
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ExtraBits {
    pub(crate) meta: bool,
    // Notionally we could keep track of the parity bit here.
    // However, in the absence of hardware failures there is no way to
    // set it.  Therefore, we simply compute the expected value of the
    // parity bit when we need it in change_word.
}

fn extra_bits_for_readonly_location() -> ExtraBits {
    RESULT_OF_VMEMORY_UNKNOWN_READ.compute_extra_bits()
}

#[derive(Clone, Copy, Default)]
pub(crate) struct MemoryWord {
    // Fields are deliberately not public.
    word: Unsigned36Bit,
    meta: bool, // the metabit
}

impl MemoryWord {
    fn compute_extra_bits(&self) -> ExtraBits {
        ExtraBits { meta: self.meta }
    }
}

impl Debug for MemoryWord {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:>012o}", self.word)
    }
}

/// The mref module exists to hide the internals of MemoryWriteRef and
/// MemoryReadRef.
///
/// We cannot simply use `&mut MemoryWord` because the arithmetic
/// element's registers A-E share a metabit (the metabit of the M
/// register).
///
mod mref {
    use super::{ExtraBits, MemoryWord};
    use base::prelude::*;

    pub(super) trait MemoryRead {
        fn get_value(&self) -> Unsigned36Bit;
        fn get_meta_bit(&self) -> bool;
        /// Some memory fetches set the metabit of the fetched word.
        fn set_meta_bit(&mut self);
        fn extra_bits(&self) -> ExtraBits {
            ExtraBits {
                meta: self.get_meta_bit(),
            }
        }
    }

    /// MemoryReadRef logically represents a memory location
    /// (register) which we can read.
    pub(super) struct MemoryReadRef<'a> {
        word: &'a Unsigned36Bit,
        meta: &'a mut bool,
    }

    impl<'a> MemoryReadRef<'a> {
        pub(super) fn new(word: &'a Unsigned36Bit, meta: &'a mut bool) -> MemoryReadRef<'a> {
            MemoryReadRef { word, meta }
        }

        pub(super) fn readonly_from(mw: &'a mut MemoryWord) -> MemoryReadRef<'a> {
            MemoryReadRef::new(&mw.word, &mut mw.meta)
        }
    }

    impl MemoryRead for MemoryReadRef<'_> {
        fn get_meta_bit(&self) -> bool {
            *self.meta
        }

        fn set_meta_bit(&mut self) {
            *self.meta = true;
        }

        fn get_value(&self) -> Unsigned36Bit {
            *self.word
        }
    }

    /// MemoryWriteRef logically represents a memory location
    /// (register) which we can write to or read.
    pub(super) struct MemoryWriteRef<'a> {
        word: &'a mut Unsigned36Bit,
        meta: &'a mut bool,
    }

    impl<'a> MemoryWriteRef<'a> {
        pub(super) fn new(word: &'a mut Unsigned36Bit, meta: &'a mut bool) -> MemoryWriteRef<'a> {
            MemoryWriteRef { word, meta }
        }
    }

    impl MemoryRead for MemoryWriteRef<'_> {
        fn get_meta_bit(&self) -> bool {
            *self.meta
        }

        fn set_meta_bit(&mut self) {
            *self.meta = true;
        }

        fn get_value(&self) -> Unsigned36Bit {
            *self.word
        }
    }

    impl MemoryWriteRef<'_> {
        pub(super) fn set_meta_bit_to_value(&mut self, value: bool) {
            *self.meta = value;
        }

        pub(super) fn set_value(&mut self, value: Unsigned36Bit) {
            *self.word = value;
        }
    }
}

#[cfg(test)]
fn make_ctx() -> Context {
    Context {
        simulated_time: Duration::new(42, 42),
        real_elapsed_time: Duration::new(7, 12),
    }
}
#[derive(Debug)]
struct Memory {
    words: Vec<MemoryWord>,
}

impl Memory {
    fn get_mut(&mut self, offset: usize) -> MemoryWriteRef<'_> {
        let mw = &mut self.words[offset];
        MemoryWriteRef::new(&mut mw.word, &mut mw.meta)
    }

    fn get(&mut self, offset: usize) -> MemoryReadRef<'_> {
        let mw = &mut self.words[offset];
        MemoryReadRef::new(&mw.word, &mut mw.meta)
    }

    fn new(size: usize) -> Memory {
        let mut words = Vec::with_capacity(size);
        while words.len() < size {
            words.push(MemoryWord::default());
        }
        Memory { words }
    }
}

#[derive(Debug)]
pub struct MemoryUnit {
    s_memory: Memory,
    t_memory: Memory,
    u_memory: Option<Memory>,
    v_memory: VMemory,
}

enum MemoryDecode {
    S(usize),
    T(usize),
    U(usize),
    // The V-memory emulation is implemented in terms of absolute
    // addresses, not in terms of offsets into the V-memory.  So there
    // is no need for an offset field for the V-memory case.
    V,
}

fn decode(address: &Address) -> Option<MemoryDecode> {
    // MemoryDecode32 is a workaround for the fact that our address
    // arithmetic uses u32 but we want to return an offset of type
    // usize.
    enum MemoryDecode32 {
        S(u32),
        T(u32),
        U(u32),
        V,
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
            Some(MemoryDecode32::V)
        } else {
            // The end of V memory is the highest address it is possible
            // to form in 17 bits.  So, it should not be possible to form
            // an invalid address in an Address struct, so we should not
            // be able to get here.
            unreachable!(
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
        MemoryDecode32::V => MemoryDecode::V,
    })
}

pub struct MemoryConfiguration {
    pub with_u_memory: bool,
}

impl MemoryUnit {
    pub fn new(ctx: &Context, config: &MemoryConfiguration) -> MemoryUnit {
        fn u32_to_usize(n: u32) -> usize {
            usize::try_from(n).expect("Only systems where u32 fits into usize are supported")
        }
        MemoryUnit {
            s_memory: Memory::new(u32_to_usize(S_MEMORY_SIZE)),
            t_memory: Memory::new(u32_to_usize(T_MEMORY_SIZE)),
            u_memory: if config.with_u_memory {
                Some(Memory::new(u32_to_usize(U_MEMORY_SIZE)))
            } else {
                None
            },
            v_memory: VMemory::new(ctx),
        }
    }

    pub fn get_a_register(&self) -> Unsigned36Bit {
        self.v_memory.get_a_register()
    }

    pub fn get_b_register(&self) -> Unsigned36Bit {
        self.v_memory.get_b_register()
    }

    pub fn get_c_register(&self) -> Unsigned36Bit {
        self.v_memory.get_c_register()
    }

    pub fn get_d_register(&self) -> Unsigned36Bit {
        self.v_memory.get_d_register()
    }

    pub fn get_e_register(&self) -> Unsigned36Bit {
        self.v_memory.get_e_register()
    }

    pub fn set_a_register(&mut self, value: Unsigned36Bit) {
        self.v_memory.set_a_register(value);
    }

    pub fn set_b_register(&mut self, value: Unsigned36Bit) {
        self.v_memory.set_b_register(value);
    }

    pub fn set_c_register(&mut self, value: Unsigned36Bit) {
        self.v_memory.set_c_register(value);
    }

    pub fn set_d_register(&mut self, value: Unsigned36Bit) {
        self.v_memory.set_d_register(value);
    }

    pub fn set_e_register(&mut self, value: Unsigned36Bit) {
        self.v_memory.set_e_register(value);
    }

    /// Perform a memory read access.  Return a MemoryReadRef for the
    /// memory word being accessed.
    fn read_access<'a>(
        &'a mut self,
        ctx: &Context,
        addr: &Address,
    ) -> Result<MemoryReadRef<'a>, MemoryOpFailure> {
        match decode(addr) {
            Some(MemoryDecode::S(offset)) => Ok(self.s_memory.get(offset)),
            Some(MemoryDecode::T(offset)) => Ok(self.t_memory.get(offset)),
            Some(MemoryDecode::U(offset)) => {
                if let Some(u) = &mut self.u_memory {
                    Ok(u.get(offset))
                } else {
                    Err(MemoryOpFailure::NotMapped(*addr))
                }
            }
            Some(MemoryDecode::V) => self.v_memory.read_access(ctx, addr),
            None => Err(MemoryOpFailure::NotMapped(*addr)),
        }
    }

    /// Perform a memory write access.  Return a MemoryWriteRef for
    /// the memory word being accessed.  If the memory location is
    /// read-only, return Ok(None).
    fn write_access<'a>(
        &'a mut self,
        ctx: &Context,
        addr: &Address,
    ) -> Result<Option<MemoryWriteRef<'a>>, MemoryOpFailure> {
        match decode(addr) {
            Some(MemoryDecode::S(offset)) => Ok(Some(self.s_memory.get_mut(offset))),
            Some(MemoryDecode::T(offset)) => Ok(Some(self.t_memory.get_mut(offset))),
            Some(MemoryDecode::U(offset)) => {
                if let Some(u) = &mut self.u_memory {
                    Ok(Some(u.get_mut(offset)))
                } else {
                    Err(MemoryOpFailure::NotMapped(*addr))
                }
            }
            Some(MemoryDecode::V) => self.v_memory.write_access(ctx, addr),
            None => Err(MemoryOpFailure::NotMapped(*addr)),
        }
    }
}

fn skm_bit_mask(bit: &BitSelector) -> Unsigned36Bit {
    if bit.bitpos <= 9 {
        match Unsigned36Bit::try_from(1 << ((u8::from(bit.quarter) * 9) + (bit.bitpos - 1))) {
            Ok(value) => value,
            Err(_) => unreachable!("mask calculation cannot yield an out-of-range value"),
        }
    } else {
        panic!("unexpected bit selector {bit:?}")
    }
}

/// Implement the heart of the change_bit() operation used by the SKM
/// instruction.  Returns the value of the selected bit, or None if
/// the bit selector indicates a nonexistent bit (e.g. 0.0, 1.0).
fn skm_bitop_get<R: MemoryRead>(target_word: &R, op: &WordChange) -> Option<bool> {
    // As the documentation for the SKM instruction (user
    // handbook, page 3-35) explains, we perform the
    // possible bit change before the possible rotate.
    match op.bit.bitpos {
        0 => None,
        1..=9 => {
            let mask = skm_bit_mask(&op.bit);
            Some((target_word.get_value() & mask) != 0)
        }
        10 => {
            // The metabit.
            Some(target_word.get_meta_bit())
        }
        // 11 is the parity bit 12 is the computed parity.
        // Both are read-only, but I don't think an attempt
        // to modify them trips an alarm (at least, I
        // can't see any mention of this in the SKM
        // documentation).
        11 | 12 => Some(u64::from(target_word.get_value()).count_ones() & 1 != 0),
        _ => unreachable!(),
    }
}

fn skm_bitop_write(mut target: MemoryWriteRef<'_>, op: &WordChange) -> Option<bool> {
    let maybe_bit: Option<bool> = skm_bitop_get(&target, op);
    match (maybe_bit, op.bit.bitpos) {
        (None, _) => {
            // A nonexistent bit has been selected, so we can't change
            // it.
        }
        (_, 1..=9) => {
            let mask = skm_bit_mask(&op.bit);
            match op.bitop {
                None => (),
                Some(BitChange::Clear) => target.set_value(target.get_value() & !mask),
                Some(BitChange::Set) => target.set_value(target.get_value() | mask),
                Some(BitChange::Flip) => target.set_value(target.get_value() ^ mask),
            }
        }
        (Some(meta_bit_val), 10) => {
            // The metabit.
            match op.bitop {
                None => (),
                Some(BitChange::Clear) => target.set_meta_bit_to_value(false),
                Some(BitChange::Set) => target.set_meta_bit_to_value(true),
                Some(BitChange::Flip) => target.set_meta_bit_to_value(!meta_bit_val),
            }
        }
        (_, 11 | 12) => {
            // Cannot set the parity bits in software.
        }
        (Some(_), 0 | 13..=u8::MAX) => unreachable!(),
    }
    if op.cycle {
        target.set_value(target.get_value() >> 1);
    }
    maybe_bit
}

impl MemoryMapped for MemoryUnit {
    fn fetch(
        &mut self,
        ctx: &Context,
        addr: &Address,
        side_effect: &MetaBitChange,
    ) -> Result<(Unsigned36Bit, ExtraBits), MemoryOpFailure> {
        match self.read_access(ctx, addr) {
            Err(e) => Err(e),
            Ok(mut mem_word) => {
                let word = mem_word.get_value();
                let extra_bits = mem_word.extra_bits();
                match side_effect {
                    MetaBitChange::None => (),
                    MetaBitChange::Set => {
                        let a32 = u32::from(addr);
                        if a32 >= V_MEMORY_START {
                            // The description of the SKM instruction doesn't state
                            // explicitly that SKM works on V-memory, but since
                            // arithmetic unit registers are mapped to it, it would
                            // make sense.  However, there are clearly other locations
                            // in V memory (e.g. the plugboard) that we can't cycle.
                            if *side_effect != MetaBitChange::None {
                                // Changng meta bits in V memory is not allowed,
                                // see the longer comment in the store() method.
                                return Err(MemoryOpFailure::ReadOnly(*addr, extra_bits));
                            }
                        } else {
                            mem_word.set_meta_bit();
                        }
                    }
                }
                Ok((word, extra_bits))
            }
        }
    }

    fn store(
        &mut self,
        ctx: &Context,
        addr: &Address,
        value: &Unsigned36Bit,
        meta: &MetaBitChange,
    ) -> Result<(), MemoryOpFailure> {
        let a32 = u32::from(addr);
        if a32 >= V_MEMORY_START && matches!(meta, MetaBitChange::Set) {
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

        match self.write_access(ctx, addr) {
            Err(e) => {
                return Err(e);
            }
            Ok(None) => {
                // Attempt to write to memory that cannot be written.
                // We just ignore this.
                return Ok(());
            }
            Ok(Some(mut mem_word)) => {
                mem_word.set_value(*value);
                match meta {
                    MetaBitChange::None => (),
                    MetaBitChange::Set => mem_word.set_meta_bit(),
                }
            }
        }
        Ok(())
    }

    fn cycle_word(&mut self, ctx: &Context, addr: &Address) -> Result<ExtraBits, MemoryOpFailure> {
        match self.write_access(ctx, addr) {
            Ok(Some(mut target)) => {
                let extra_bits = target.extra_bits();
                target.set_value(target.get_value() << 1);
                Ok(extra_bits)
            }
            Err(e) => {
                // The memory address is not mapped at all.
                Err(e)
            }
            Ok(None) => {
                event!(Level::DEBUG, "Cannot cycle read-only memory location");
                Err(MemoryOpFailure::ReadOnly(
                    *addr,
                    extra_bits_for_readonly_location(),
                ))
            }
        }
    }

    fn change_bit(
        &mut self,
        ctx: &Context,
        addr: &Address,
        op: &WordChange,
    ) -> Result<Option<bool>, MemoryOpFailure> {
        fn downgrade_op(op: &WordChange) -> WordChange {
            WordChange {
                bit: op.bit,  // access the same bit
                bitop: None,  // read-only
                cycle: false, // read-only
            }
        }

        if op.will_mutate_memory() {
            // If the memory address is not mapped at all, access will
            // return Err, causing the next line to bail out of this
            // function.
            match self.write_access(ctx, addr)? {
                None => {
                    // The memory address is mapped to read-only
                    // memory.  For example, plugboard memory.
                    //
                    // We downgrade the bit operation to be
                    // non-mutating, so that the outcome of the bit
                    // test is as it should be, but the memory-write
                    // is inhibited.
                    let mem_word = self.read_access(ctx, addr)?;
                    let downgraded_op = downgrade_op(op);
                    assert!(!downgraded_op.will_mutate_memory()); // should be read-only now
                    Ok(skm_bitop_get(&mem_word, &downgraded_op))
                }
                Some(mem_word) => Ok(skm_bitop_write(mem_word, op)),
            }
        } else {
            let mem_word = self.read_access(ctx, addr)?;
            Ok(skm_bitop_get(&mem_word, op))
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
    // See also https://github.com/TX-2/TX-2-simulator/issues/59.
    a_register: Unsigned36Bit,
    b_register: Unsigned36Bit,
    c_register: Unsigned36Bit,
    d_register: Unsigned36Bit,
    e_register: Unsigned36Bit,
    m_register_metabit: bool,

    unimplemented_shaft_encoder: MemoryWord,
    unimplemented_external_input_register: MemoryWord,
    rtc: MemoryWord,
    rtc_start: Duration,
    codabo_start_point: [Unsigned36Bit; 8],
    plugboard: [Unsigned36Bit; 32],

    /// Writes to unknown locations are required to be ignored, but
    /// reads have to return a value.  If permit_unknown_reads is set,
    /// a special value is returned.  If not, a QSAL alarm will be
    /// raised (though that alarm may in turn be suppressed).
    permit_unknown_reads: bool,
    sacrificial_word_for_unknown_reads: MemoryWord,

    // Writes to VMemory metabits are civerted to here so that setting
    // the metabit has no (permanent) effect.
    sacrificial_metabit: bool,
}

const fn standard_plugboard_internal() -> [Unsigned36Bit; 32] {
    // This data has not yet been double-checked and no tests
    // validate it, so it might be quite wrong.
    //
    // This is taken from the listing in section 5-5.2 (page 5-27) of
    // the Users Handbook.
    [
        // Plugboard memory starts with Plugboard B at 0o3777740.
        //
        // F-memory settings; these are verified against the
        // information from Table 7-2 by a test in the exchanger code.
        u36!(0o_760342_340000),
        u36!(0o_410763_762761),
        u36!(0o_160142_140411),
        u36!(0o_202163_162161),
        u36!(0o_732232_230200),
        u36!(0o_605731_730733),
        u36!(0o_320670_750600),
        u36!(0o_604331_330333),
        // 0o377750: standard program to load the F-memory settings
        // (this is not verified by the test in the exchanger code).
        u36!(0o_002200_377740), // ⁰⁰SPG 377740
        u36!(0o_042200_377741), // ⁰⁴SPG 377741
        u36!(0o_102200_377742), // ¹⁰SPG 277742
        u36!(0o_142200_377743), // ¹⁴SPG 277743
        u36!(0o_202200_377744), // ²⁰SPG 277744
        u36!(0o_242200_377745), // ²⁴SPG 277745
        u36!(0o_302200_377746), // ³⁰SPG 277746
        u36!(0o_342200_377747), // ³⁴SPG 277747
        // Plugboard A, 0o377760-0o377777
        // 0o0377760: Standard program: read in reader leader from paper tape
        //
        // This code uses 3 index registers:
        // X₅₂: start address for sequence 52, for PETR (paper tape) device
        // X₅₃: counts the number of TSD operations needed to fill a word
        // X₅₄: starts at -23, counts upward; we add this to 26 to get the
        //      address into which we perform tape transfers (with TSD),
        //      so that the standard reader leader is read into locations 3 to 26
        u36!(0o011254_000023), // ¹SKX₅₄ 23        ** X₅₄=-23, length of reader leader
        u36!(0o001252_377763), // REX₅₂ 377763     ** Load 377763 into X₅₂ (seq 52 start point)
        u36!(0o210452_030106), // ²¹IOS₅₂ 30106    ** PETR: Load bin, read assembly mode
        // 0o0377763
        u36!(0o001253_000005), // REX₅₃ 5          ** Load 5 into X₅₃
        // 0o0377764
        u36!(0o405754_000026), // h TSD₅₄ 26       ** Load into 26+X₅₄ (which is negative)
        // 0o0377765
        u36!(0o760653_377764), // h ³⁶JPX₅₃ 377764 ** loop if X₅₃>0, decrement it
        // 0o0377766
        u36!(0o410754_377763), // h ¹JNX₅₄ 377763  ** loop if X₅₄<0, increment it
        // 0o0377767
        u36!(0o140500_000003), // ¹⁴JPQ 3          ** Jump to start of reader leader
        // At the time we jump, sequence 0o52 is executing, with
        // X₅₂ = 0o377763, X₅₃ = 0, X₅₄ = 0.
        //
        // 0o0377770: Standard program: clear memory
        u36!(0o001277_207777),
        u36!(0o001677_777776),
        u36!(0o140500_377773),
        u36!(0o001200_777610),
        u36!(0o760677_377771),
        u36!(0o301712_377744),
        u36!(0o000077_000000),
        u36!(0o140500_377750),
    ]
}

pub(crate) fn get_standard_plugboard() -> Vec<Unsigned36Bit> {
    standard_plugboard_internal().to_vec()
}

const RESULT_OF_VMEMORY_UNKNOWN_READ: MemoryWord = MemoryWord {
    word: u36!(0o404_404_404_404),
    meta: false,
};

impl VMemory {
    fn new(ctx: &Context) -> VMemory {
        let mut result = VMemory {
            a_register: Unsigned36Bit::default(),
            b_register: Unsigned36Bit::default(),
            c_register: Unsigned36Bit::default(),
            d_register: Unsigned36Bit::default(),
            e_register: Unsigned36Bit::default(),
            m_register_metabit: false,
            codabo_start_point: [
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
                Unsigned36Bit::default(),
            ],
            plugboard: standard_plugboard_internal(),
            unimplemented_shaft_encoder: MemoryWord::default(),
            unimplemented_external_input_register: MemoryWord::default(),
            rtc: MemoryWord::default(),
            rtc_start: ctx.real_elapsed_time,
            permit_unknown_reads: true,
            sacrificial_word_for_unknown_reads: RESULT_OF_VMEMORY_UNKNOWN_READ,
            sacrificial_metabit: false,
        };
        result.reset_rtc(ctx);
        result
    }

    fn get_a_register(&self) -> Unsigned36Bit {
        self.a_register
    }

    fn get_b_register(&self) -> Unsigned36Bit {
        self.b_register
    }

    fn get_c_register(&self) -> Unsigned36Bit {
        self.c_register
    }

    fn get_d_register(&self) -> Unsigned36Bit {
        self.d_register
    }

    fn get_e_register(&self) -> Unsigned36Bit {
        self.e_register
    }

    fn set_a_register(&mut self, value: Unsigned36Bit) {
        self.a_register = value;
    }

    fn set_b_register(&mut self, value: Unsigned36Bit) {
        self.b_register = value;
    }

    fn set_c_register(&mut self, value: Unsigned36Bit) {
        self.c_register = value;
    }

    fn set_d_register(&mut self, value: Unsigned36Bit) {
        self.d_register = value;
    }

    fn set_e_register(&mut self, value: Unsigned36Bit) {
        self.e_register = value;
    }

    /// Perform a memory read.
    fn read_access<'a>(
        &'a mut self,
        ctx: &Context,
        addr: &Address,
    ) -> Result<MemoryReadRef<'a>, MemoryOpFailure> {
        // Most locations in V memory have a metabit which cannot be
        // set in software.  In some cases (e.g. the shaft encoders)
        // it can be set in hardware.
        let readonly = |word: &'a Unsigned36Bit, meta_value: bool, meta_loc: &'a mut bool| {
            *meta_loc = meta_value;
            MemoryReadRef::new(word, meta_loc)
        };

        match u32::from(addr) {
            // The metabit of the Arithmetic Element registers is
            // shared (in fact, it is the metabit of the M register).
            0o0377604 => Ok(MemoryReadRef::new(
                &self.a_register,
                &mut self.m_register_metabit,
            )),
            0o0377605 => Ok(MemoryReadRef::new(
                &self.b_register,
                &mut self.m_register_metabit,
            )),
            0o0377606 => Ok(MemoryReadRef::new(
                &self.c_register,
                &mut self.m_register_metabit,
            )),
            0o0377607 => Ok(MemoryReadRef::new(
                &self.d_register,
                &mut self.m_register_metabit,
            )),
            0o0377610 => Ok(MemoryReadRef::new(
                &self.e_register,
                &mut self.m_register_metabit,
            )),
            0o0377620 => {
                event!(
                    Level::WARN,
                    "Reading the shaft encoder is not yet implemented"
                );
                Ok(MemoryReadRef::readonly_from(
                    &mut self.unimplemented_shaft_encoder,
                ))
            }
            0o0377621 => {
                event!(
                    Level::WARN,
                    "Reading the external input register is not yet implemented"
                );
                Ok(readonly(
                    &self.unimplemented_external_input_register.word,
                    self.unimplemented_external_input_register.meta,
                    &mut self.sacrificial_metabit,
                ))
            }
            0o0377630 => {
                self.update_rtc(ctx);
                Ok(MemoryReadRef::readonly_from(&mut self.rtc))
            }
            0o0377710 => Ok(readonly(
                &self.codabo_start_point[0],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset0
            0o0377711 => Ok(readonly(
                &mut self.codabo_start_point[1],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset1
            0o0377712 => Ok(readonly(
                &mut self.codabo_start_point[2],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset2
            0o0377713 => Ok(readonly(
                &mut self.codabo_start_point[3],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset3
            0o0377714 => Ok(readonly(
                &mut self.codabo_start_point[4],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset4
            0o0377715 => Ok(readonly(
                &mut self.codabo_start_point[5],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset5
            0o0377716 => Ok(readonly(
                &mut self.codabo_start_point[6],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset6
            0o0377717 => Ok(readonly(
                &mut self.codabo_start_point[7],
                false,
                &mut self.sacrificial_metabit,
            )), // CODABO Reset7

            a @ 0o0377740..=0o0377777 => {
                if let Ok(offset) = TryInto::<usize>::try_into(a - 0o0377740) {
                    Ok(readonly(
                        &mut self.plugboard[offset],
                        false,
                        &mut self.sacrificial_metabit,
                    ))
                } else {
                    // Unreachable because the matched range is
                    // not large enough to exceed the capacity of
                    // usize (which we assume is at least 2^16).
                    unreachable!()
                }
            }
            _ => {
                if self.permit_unknown_reads {
                    Ok(MemoryReadRef::readonly_from(
                        &mut self.sacrificial_word_for_unknown_reads,
                    ))
                } else {
                    event!(
                        Level::ERROR,
                        "V-memory read of unknown location {:o} is not allowed",
                        addr
                    );
                    Err(MemoryOpFailure::NotMapped(*addr))
                }
            }
        }
    }

    /// Perform a memory write.  Return a mutable reference to the
    /// memory word being accessed or, if this is an attempt to write
    /// to a read-only location, return None.
    fn write_access<'a>(
        &'a mut self,
        _ctx: &Context,
        addr: &Address,
    ) -> Result<Option<MemoryWriteRef<'a>>, MemoryOpFailure> {
        // The AE registers are supposed to share a single metabit, the metabit of the M register.
        match u32::from(addr) {
            0o0377604 => Ok(Some(MemoryWriteRef::new(
                &mut self.a_register,
                &mut self.m_register_metabit,
            ))),
            0o0377605 => Ok(Some(MemoryWriteRef::new(
                &mut self.b_register,
                &mut self.m_register_metabit,
            ))),
            0o0377606 => Ok(Some(MemoryWriteRef::new(
                &mut self.c_register,
                &mut self.m_register_metabit,
            ))),
            0o0377607 => Ok(Some(MemoryWriteRef::new(
                &mut self.d_register,
                &mut self.m_register_metabit,
            ))),
            0o0377610 => Ok(Some(MemoryWriteRef::new(
                &mut self.e_register,
                &mut self.m_register_metabit,
            ))),
            // Example 10 on page 3-17 of the Users Handbook says "V
            // memory, except the A, B, C, D, and E registers cannot
            // be changed by any instruction".
            _ => Ok(None),
        }
    }

    fn reset_rtc(&mut self, ctx: &Context) {
        self.rtc_start = ctx.real_elapsed_time;
        self.rtc.word = Unsigned36Bit::ZERO;
    }

    fn update_rtc(&mut self, ctx: &Context) {
        if ctx.real_elapsed_time >= self.rtc_start {
            // Page 5-19 of the Nov 1963 Users Handbook states that the
            // RTC has a period of 10 microseconds and will reset itself
            // "every 7.6 days or so".
            //
            // These facts seems to be inconsistent, since 2^36 *
            // 10 microseconds is 7.953643140740741 days (assuming
            // 86400 seconds per day).  In other words, this
            // period is about 5% too high, and is an odd choice
            // of rounding (when the author could have said "just
            // under 8 days" or "just over 7.9 days").
            //
            // A clock period of 9.555 microseconds on the other
            // hand would give a rollover period of 7.5997 days
            // (about 7d 14h 23m 34.1s).
            //
            // Since the tick interval is more important than the
            // time between rollovers though, we stick with 10
            // microseconds.
            const TICK_MICROSEC: u128 = 10;
            let duration = ctx.real_elapsed_time - self.rtc_start;
            let tick_count = duration.as_micros() / TICK_MICROSEC;
            const RTC_MODULUS: u128 = 1 << 36;
            assert!(u128::from(u64::from(Unsigned36Bit::MAX)) < RTC_MODULUS);
            match u64::try_from(tick_count % RTC_MODULUS) {
                Ok(n) => match Unsigned36Bit::try_from(n) {
                    Ok(n) => {
                        self.rtc.word = n;
                    }
                    Err(_) => {
                        // (x % RTC_MODULUS) <= Unsigned36Bit::MAX for
                        // all x, so this case cannot occur.
                        unreachable!();
                    }
                },
                Err(_) => {
                    // (x % RTC_MODULUS) <= Unsigned36Bit::MAX for
                    // all x, so this case cannot occur.
                    unreachable!();
                }
            }
        } else {
            // There has been a correction to the system clock used
            // to generate `ctx.real_elapsed_time`.  We handle
            // this by pretending that the user has just pressed
            // the "reset RTC" button.
            self.reset_rtc(ctx);
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
    let context = make_ctx();
    let mut mem = MemoryUnit::new(
        &context,
        &MemoryConfiguration {
            with_u_memory: false,
        },
    );
    for a in all_physical_memory_addresses() {
        let addr: Address = Address::try_from(a).unwrap();
        // The point of this test is to verify that we con't have any
        // todo!()s in reachable code paths.
        let result = mem.write_access(&context, &addr);
        match result {
            Ok(Some(_)) => (),
            Ok(None) => {
                // The only memory for which writes are forbidden is
                // in V memory.
                assert!(a >= V_MEMORY_START);
                assert!(a <= 0o0377777);
                // However, writes to the arithmetic element are
                // permitted.
                assert_ne!(a, 0o0377604); // A
                assert_ne!(a, 0o0377605); // B
                assert_ne!(a, 0o0377606); // C
                assert_ne!(a, 0o0377607); // D
                assert_ne!(a, 0o0377610); // E
            }
            Err(MemoryOpFailure::NotMapped(_)) => (),
            Err(e) => {
                panic!("Failure {e:?} during write of memory address {addr:o}");
            }
        }
    }
}

#[test]
fn test_read_all_mem() {
    #[cfg(test)]
    let context = make_ctx();
    let mut mem = MemoryUnit::new(
        &context,
        &MemoryConfiguration {
            with_u_memory: false,
        },
    );
    for a in all_physical_memory_addresses() {
        let addr: Address = Address::try_from(a).unwrap();
        // The point of this test is to verify that we con't have any
        // todo!()s in reachable code paths.
        let result = mem.read_access(&context, &addr);
        match result {
            Ok(_) => (),
            Err(MemoryOpFailure::NotMapped(_)) => (),
            Err(e) => {
                panic!("Failure {e:?} during read of memory address {addr:o}");
            }
        }
    }
}

#[test]
fn test_ae_registers_share_metabit() {
    // Registers ABCDE share a single metabit (the metabit of the M
    // register, in fact) and so we should be able to set (or clear)
    // the metabit of one of them and read it back through another.
    let context = make_ctx();
    let mut mem = MemoryUnit::new(
        &context,
        &MemoryConfiguration {
            with_u_memory: false,
        },
    );
    let a_addr: Address = Address::from(u18!(0o0377604));
    let b_addr: Address = Address::from(u18!(0o0377605));
    let c_addr: Address = Address::from(u18!(0o0377606));
    let d_addr: Address = Address::from(u18!(0o0377607));
    let e_addr: Address = Address::from(u18!(0o0377610));
    let ae_regs = [a_addr, b_addr, c_addr, d_addr, e_addr];

    fn set_metabit(context: &Context, mem: &mut MemoryUnit, addr: Address, value: bool) {
        match mem.write_access(context, &addr) {
            Ok(Some(mut word)) => word.set_meta_bit_to_value(value),
            Ok(None) => {
                panic!("AE register at {addr:o} is not mapped");
            }
            Err(e) => {
                panic!("failed to write memory at {addr:o}: {e}");
            }
        }
    }

    fn get_metabit(context: &Context, mem: &mut MemoryUnit, addr: Address) -> bool {
        match mem.read_access(context, &addr) {
            Ok(word) => word.get_meta_bit(),
            Err(e) => {
                panic!("failed to read memory at {addr:o}: {e}");
            }
        }
    }

    for first in 0..ae_regs.len() {
        for second in 0..ae_regs.len() {
            // Set the metabit at the first location.
            set_metabit(&context, &mut mem, ae_regs[first], true);
            // Verify that the metabit at the second location is set (1).
            assert!(get_metabit(&context, &mut mem, ae_regs[second]));
            // Clear the metabit at the second location.
            set_metabit(&context, &mut mem, ae_regs[second], false);
            // Verify that the metabit at the first location is clear (0).
            assert!(!get_metabit(&context, &mut mem, ae_regs[first]));
        }
    }
}
