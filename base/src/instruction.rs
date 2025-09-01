//! Binary and symbolic representations of TX-2 instructions.
//!
//! A TX-2 instruction occupies 36 bits.  The 36 bits look like this
//! (least significant bit on the right, bits numbered 0 to 35 in
//! decimal):
//!
//! |Hold |Configuration| Opcode|Index  |Defer|Operand Memory Address|
//! |-----|-------------|-------|-------|-----|----------------------|
//! |1 bit|  5 bits     |6 bits |6 bits |1 bit|      17 bits         |
//! |(35) | (30-34)     |(24-29)|(18-23)|     |       (0-16)         |
//!
//! This diagram is taken from section 6-2.1 "INSTRUCTION WORDS" of the
//! TX-2 Users Handbook (page 6-4, being the 157th page of my PDF file).
//!
//! There is a similar diagram in Fig. 5 (p. 11) of "A Functional
//! Description of the Lincoln TX-2 Computer" by John M. Frankovitch
//! and H. Philip Peterson, but that is older and, I believe,
//! inaccurate in the width of the configuration field for example.
//! Section 6-2.1 of the User Handbook confirms that the configuration
//! "syllable" is 5 bits.
//!
//! Table 7-2 in the user guide defines values of `cf` for the range 0
//! to 037 inclusive in terms of the standard contents that they fetch
//! from the F-memory.
//!
//! In the programming examples (6M-5780, page 6) we have
//!
//! ```tx2
//! 34 21 00 377,751     ³⁴SPF 377,751
//! ```
//!
//! Here, the operand memory address is 0377751.  The index is 00.
//! The opcode is `SPF`, octal 21.  The top 6 bits are 034, or 11100
//! binary.  The user guide states that `SPF` is not configurable, so
//! presumably the configuration field simply specifies the address in
//! F-memory that we will write to.
//!
//! Later in the same page we have
//!
//! ```tx2
//! 74 11 71 377,762    ³⁴RSX⁷¹  377,762
//! ```
//!
//! It seems that the conventions for specifyign index registers
//! changed between the writing of that memo and the finalisation of
//! the syntax for the M4 assembler, and so in the 1963 assembler
//! input format, this would be:
//!
//! ```tx2
//! 74 11 71 377,762    ³⁴RSX₇₁  377,762
//! ```
//!
//! RSX is opcode 11.   Hence the top 6 bits are  074 = 111100 binary,
//! Of those only 034=11100 binary seem to be configuration code.  But
//! the hold bit  seems to be set without this  being indicated in the
//! symbolic form of the instruction.  Perhaps this was something that
//! changed after the writing of the  memo; certainly `RSX` is not one
//! of the instruction listed in section 4-3.2 with a default-hold bit
//! (TSD, JNX, JPX).

use std::fmt::{self, Debug, Display, Formatter};

#[cfg(test)]
use test_strategy::{Arbitrary, proptest};

use super::bitselect::{BitPos, BitSelector};
use super::prelude::*;
use super::subword;
mod format;

pub const DEFER_BIT: Unsigned36Bit = Unsigned36Bit {
    bits: 0o400_000_u64,
};

/// While examples usually choose 0 as the non-existent bit position,
/// the index portion of the instruction word (which encodes the
/// quarter and bit position for SKM instructions) stores two bits of
/// quarter number and four bits of bit position, meaning that the
/// possible range of bit positions is 0..=15 (decimal).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonexistentBitPos {
    Zero,
    Thirteen,
    Fourteen,
    Fifteen,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SkmBitPos {
    Value(BitPos), // bits 1 to 9 inclusive
    Meta,          // bit 10
    Parity,        // bit 11 (can be tested but not set)
    ParityCircuit, // bit 12 (can be tested but not set)

    /// Bit zero of any quarter is non-existent.  The interpretation
    /// of bit 0 is explained in the documentation for SKM (Users
    /// Handbook, page 3-34:
    ///
    /// If a non-existent bit is selected, e.g. bit 0.0,1.0,2.0,3.0
    /// for example, Unconditional Skips (SKU) and Rotate (CYR) will
    /// still work, but "makes" will do nothing, and conditional skips
    /// will not skip.
    Nonexistent(NonexistentBitPos),
}

impl Display for SkmBitPos {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            SkmBitPos::Nonexistent(NonexistentBitPos::Zero) => f.write_str("0"),
            SkmBitPos::Value(bitpos) => write!(f, "{bitpos}"),
            SkmBitPos::Meta => f.write_str("10"),
            SkmBitPos::Parity => f.write_str("11"),
            SkmBitPos::ParityCircuit => f.write_str("12"),
            SkmBitPos::Nonexistent(NonexistentBitPos::Thirteen) => f.write_str("13"),
            SkmBitPos::Nonexistent(NonexistentBitPos::Fourteen) => f.write_str("14"),
            SkmBitPos::Nonexistent(NonexistentBitPos::Fifteen) => f.write_str("15"),
        }
    }
}

/// `SkmBitSelector` is primarily for use with the SKM
/// instruction which can access bits 1-9 of quarters, plus the meta
/// and parity bits (of the full word).  Hence the wider range.  See
/// the [`index_address_to_bit_selection`] function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SkmBitSelector {
    pub quarter: Quarter,
    pub bitpos: SkmBitPos,
}

/// Render the bit selector in the form q.b.  Unfortunately the TX2
/// documentation is inconsistent in how the bit number is formatted.
/// Page 3-34 of the User Handbook clearly says "Bit Numbers are
/// interpreted as Decimal".
///
/// However, section 5-5.2 of the Users Handbook provides a listing of
/// the standard reader leader.  The instruction at location 17 is
/// shown as
///
/// ```TX2
/// INSTRUCTION              NUMERICAL FORM (OCTAL)
/// ²MKZ₄.₁₂ 400011          |021712 400011|
/// ```
///
/// Section 5-5.2 of the Users Handbook also shows an instruction in
/// Plugboard A at address 0377775:
///
/// ```TX2
/// INSTRUCTION              NUMERICAL FORM (OCTAL)
/// ³⁰SKN₄.₁₂ 377744         |301712 377744|
/// ```
///
/// In both our examples above, quarter 3 has the value 0712 octal.
/// This encodes the value generated by the 4.12 bit selector (as well
/// as the bottom 3 bits of the opcode).
///
/// `SKN` is shorthand for `³⁰SKM` and `MKZ` is shorthand for `²SKM`.
/// The opcode for `SKM` is 017.  In the TX-2's instruction word, the
/// index bits are used to store the bit selector for the SKN
/// instruction.  In the TX-2's convention these are bits 3.1 to 3.6
/// inclusive.  That is, bits 19 through 24 (counting from 0 as the
/// least significant):
///
/// | Q3 Bit     | Interpretation     | Octal | Meaning                 |
/// | ---------- | --------------     | ---   | ----------------------- |
/// | 3.1 to 3.4 | Bit number         | 012   | 10 decimal, the metabit |
/// | 3.5 to 3.6 | Quarter number     | 000   | Q4                      |
/// | 3.7 to 3.9 | Low bits of opcode | 007   | Part of 017, for SKM    |
///
/// However, for the moment we will adopt the decimal convention since
/// it is in wider use in the documentation.
///
impl Display for SkmBitSelector {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}.{}", self.quarter, self.bitpos)
    }
}

impl SkmBitSelector {
    pub fn to_value_bit(self) -> Option<BitSelector> {
        match self.bitpos {
            SkmBitPos::Value(b) => Some(BitSelector {
                quarter: self.quarter,
                bitpos: b,
            }),
            _ => None,
        }
    }
}

/// Convert the index address field of an SKM instruction into a
/// `BitSelector` struct describing which bit we will operate on.
pub fn index_address_to_bit_selection(index_address: Unsigned6Bit) -> SkmBitSelector {
    let j: u8 = u8::from(index_address);
    let bitpos: SkmBitPos = match j & 0b1111_u8 {
        0 => SkmBitPos::Nonexistent(NonexistentBitPos::Zero),
        1 => SkmBitPos::Value(BitPos::B1),
        2 => SkmBitPos::Value(BitPos::B2),
        3 => SkmBitPos::Value(BitPos::B3),
        4 => SkmBitPos::Value(BitPos::B4),
        5 => SkmBitPos::Value(BitPos::B5),
        6 => SkmBitPos::Value(BitPos::B6),
        7 => SkmBitPos::Value(BitPos::B7),
        8 => SkmBitPos::Value(BitPos::B8),
        9 => SkmBitPos::Value(BitPos::B9),
        10 => SkmBitPos::Meta,
        11 => SkmBitPos::Parity,
        12 => SkmBitPos::ParityCircuit,
        13 => SkmBitPos::Nonexistent(NonexistentBitPos::Thirteen),
        14 => SkmBitPos::Nonexistent(NonexistentBitPos::Fourteen),
        15 => SkmBitPos::Nonexistent(NonexistentBitPos::Fifteen),
        _ => unreachable!(),
    };
    SkmBitSelector {
        quarter: match (j >> 4) & 0b11 {
            0 => Quarter::Q4,
            1 => Quarter::Q1,
            2 => Quarter::Q2,
            3 => Quarter::Q3,
            _ => unreachable!(),
        },
        bitpos,
    }
}

/// A TX-2 Instruction.
#[derive(Clone, Copy)]
pub struct Instruction(Unsigned36Bit);

impl Instruction {
    /// Returns an unspecified invalid instruction.
    pub fn invalid() -> Instruction {
        Instruction(Unsigned36Bit::ZERO)
    }

    pub fn bits(&self) -> Unsigned36Bit {
        self.0
    }
}

impl From<Unsigned36Bit> for Instruction {
    fn from(w: Unsigned36Bit) -> Instruction {
        Instruction(w)
    }
}

impl From<Instruction> for Unsigned36Bit {
    fn from(inst: Instruction) -> Unsigned36Bit {
        inst.0
    }
}

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let lhs = match SymbolicInstruction::try_from(self) {
            Ok(sym) => format!("{sym}"),
            Err(e) => format!("(invalid instruction: {e})"),
        };
        write!(f, "{:<40} {}", lhs, self.0)
    }
}

/// The `Inst` trait provides a way to extract the various fields
/// within an instruction.
pub trait Inst {
    /// Obtain the value of the "hold" bit.
    fn is_held(&self) -> bool;

    /// Fetch the configuration field of the instruction.  This is
    /// used as an index to fetch a system configuration from the
    /// F-memory.  Table 7-2 in the TX-2 User Handbook explains what
    /// data exists in the F-memory in the standard configuration.
    ///
    /// The meaning of the values fetched from the F-memory (and thus,
    /// the significance of the configuration values of an
    /// instruction) is explained in Volume 2 (pages 12-19) of the
    /// Technical manual.  Some instructions (JMP, for example) use
    /// this field differently.
    fn configuration(&self) -> Unsigned5Bit;

    /// indexation is actually a signed operation (see the [`IndexBy`]
    /// trait) but index addresses are shown as positive numbers
    /// (e.g. 77) in assembler source code.
    fn index_address(&self) -> Unsigned6Bit;

    /// The opcode of the instruction.
    fn opcode_number(&self) -> u8;

    /// The value of the defer bit from the operand address field.
    fn is_deferred_addressing(&self) -> bool;

    /// Fetches the operand address with the defer bit (if set) in bit
    /// position 17.
    fn operand_address_and_defer_bit(&self) -> Unsigned18Bit;

    fn operand_address(&self) -> OperandAddress;
}

impl Inst for Instruction {
    fn is_held(&self) -> bool {
        const HOLD_BIT: u64 = 1_u64 << 35;
        !(self.0 & HOLD_BIT).is_zero()
    }

    fn configuration(&self) -> Unsigned5Bit {
        let val: u8 = u8::try_from((self.0 >> 30) & 31_u64).unwrap();
        Unsigned5Bit::try_from(val).unwrap()
    }

    fn opcode_number(&self) -> u8 {
        u8::try_from((self.0 >> 24) & 63_u64).unwrap()
    }

    fn index_address(&self) -> Unsigned6Bit {
        Unsigned6Bit::try_from((self.0 >> 18) & 63_u64).unwrap()
    }

    fn is_deferred_addressing(&self) -> bool {
        self.0 & DEFER_BIT != 0
    }

    fn operand_address(&self) -> OperandAddress {
        let bits: Unsigned18Bit = subword::right_half(self.0);
        OperandAddress::from_raw_bits(bits)
    }

    fn operand_address_and_defer_bit(&self) -> Unsigned18Bit {
        let bits: u32 = u32::try_from(self.0 & 0o777_777).unwrap();
        Unsigned18Bit::try_from(bits).unwrap() // range already checked above.
    }
}

/// `Opcode` enumerates all the valid TX-2 opcodes.  These values are
/// taken from the User Handbook.  Volume 3 of the Technical Manual
/// (page 1-5-3) describes opcodes 00, 01, 02, 03, 04 (mentioning bit
/// 2.8 of N being in state 1), 13, 23, 33, 45, 50, 51, 52, 53, 63, 73
/// as being undefined.
///
/// Different copies of the User Handbook differ in the description of
/// opcodes 0o44 and 0o45.
#[repr(u8)]
#[cfg_attr(test, derive(Arbitrary))]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Opcode {
    // opcode 1 is unused
    // opcode 2 may be XEQ, but no documentation on this.
    // opcode 3 is unused
    /// Opcode 04 (which is sometimes known as OPR) is used to encode
    /// two kinds of instructions, IOS and AOP.
    ///
    /// IOS is the I/O select instruction and is described in the TX-2
    /// Users Handbook, section 4-3.5.
    ///
    /// Bits 2.7 and 2.8 of the instruction work determine whether an
    /// OPR instruction is IOS or AOP (or invalid).
    ///
    /// AOP is (apparently, documentation is a bit thin) the
    /// Arithmetic Operation instruction.  This operates only on the
    /// Arithmetic unit (that is, it makes no memory reference).
    ///
    /// See Technical Manual Vol 2 section 10-2.5.3 (AOP
    /// instructions), Technical Manual Vol 3 section 16-5.1 (OPR (04)
    /// AOP, see physical PDF page number 45).  Section 16-5.1 claims
    /// that AOP is described in detail in chapter 4 of the Technical
    /// Manual.
    Opr = 0o4,
    Jmp = 0o5,
    Jpx = 0o6,
    Jnx = 0o7,
    Aux = 0o10,
    Rsx = 0o11,
    Skx = 0o12,
    // opcode 0o13 = 11 is undefined (unused).
    Exx = 0o14,
    Adx = 0o15,
    Dpx = 0o16,
    Skm = 0o17,
    Lde = 0o20,
    Spf = 0o21,
    Spg = 0o22,
    // opcode 0o23 = 19 is undefined (unused).
    Lda = 0o24,
    Ldb = 0o25,
    Ldc = 0o26,
    Ldd = 0o27,
    Ste = 0o30,
    Flf = 0o31,
    Flg = 0o32,
    // opcode 033 = 27 is unused.
    Sta = 0o34,
    Stb = 0o35,
    Stc = 0o36,
    Std = 0o37,
    Ite = 0o40,
    Ita = 0o41,
    Una = 0o42,
    Sed = 0o43,

    /// I have two copies of the User Handbook and they differ in
    /// their description of opcodes 0o44, 0o45.
    ///
    /// In the August 1963 copy, 0o44 is missing and 0045 is JOV.
    ///
    /// In the index of the October 1961 copy, 0o44 is JOV and 0o45 is
    /// JZA (handwritten).  However, in this copy, page 3-32 (which
    /// describes JPA, JNA, JOV) gives JOV as 0o45.  So I assume this
    /// is just an error in the index.  This copy does not otherwise
    /// describe a JZA opcode.
    Jov = 0o45,

    Jpa = 0o46,
    Jna = 0o47,
    // opcode 0o50 = 40 is undefined (unused).
    // opcode 0o51 = 41 is undefined (unused).
    // opcode 0o52 = 42 is undefined (unused).
    // opcode 0o53 = 43 is undefined (unused).
    Exa = 0o54,
    Ins = 0o55,
    Com = 0o56,
    Tsd = 0o57,
    Cya = 0o60,
    Cyb = 0o61,
    Cab = 0o62,
    // opcode 0o63 = 51 is unused.
    Noa = 0o64,
    Dsa = 0o65,
    Nab = 0o66,
    Add = 0o67,
    Sca = 0o70,
    Scb = 0o71,
    Sab = 0o72,
    // opcode 0o71 = 59 is unused.
    Tly = 0o74,
    Div = 0o75,
    Mul = 0o76,
    Sub = 0o77,
}

impl Opcode {
    pub fn number(&self) -> u8 {
        *self as u8
    }

    pub fn hold_is_implicit(&self) -> bool {
        matches!(self, Opcode::Lde | Opcode::Ite | Opcode::Jpx | Opcode::Jnx)
    }
}

impl TryFrom<u8> for Opcode {
    type Error = DisassemblyFailure;
    fn try_from(opcode: u8) -> Result<Opcode, DisassemblyFailure> {
        use Opcode::*;
        match opcode {
            // TODO: change these opcode values to octal.
            0 | 1 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            2 => {
                // Maybe XEQ?
                Err(DisassemblyFailure::UnimplementedOpcode(opcode))
            }
            3 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o4 => Ok(Opr),
            0o5 => Ok(Jmp),
            0o6 => Ok(Jpx),
            0o7 => Ok(Jnx),

            0o10 => Ok(Aux),
            0o11 => Ok(Rsx),
            0o12 => Ok(Skx),
            0o13 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o14 => Ok(Exx),
            0o15 => Ok(Adx),
            0o16 => Ok(Dpx),
            0o17 => Ok(Skm),

            0o20 => Ok(Lde),
            0o21 => Ok(Spf),
            0o22 => Ok(Spg),
            0o23 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o24 => Ok(Lda),
            0o25 => Ok(Ldb),
            0o26 => Ok(Ldc),
            0o27 => Ok(Ldd),

            0o30 => Ok(Ste),
            0o31 => Ok(Flf),
            0o32 => Ok(Flg),
            0o33 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o34 => Ok(Sta),
            0o35 => Ok(Stb),
            0o36 => Ok(Stc),
            0o37 => Ok(Std),

            0o40 => Ok(Ite),
            0o41 => Ok(Ita),
            0o42 => Ok(Una),
            0o43 => Ok(Sed),
            0o44 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o45 => Ok(Jov),
            0o46 => Ok(Jpa),
            0o47 => Ok(Jna),

            0o50..=0o53 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o54 => Ok(Exa),
            0o55 => Ok(Ins),
            0o56 => Ok(Com),
            0o57 => Ok(Tsd),

            0o60 => Ok(Cya),
            0o61 => Ok(Cyb),
            0o62 => Ok(Cab),
            0o63 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o64 => Ok(Noa),
            0o65 => Ok(Dsa),
            0o66 => Ok(Nab),
            0o67 => Ok(Add),

            0o70 => Ok(Sca),
            0o71 => Ok(Scb),
            0o72 => Ok(Sab),
            0o73 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            0o74 => Ok(Tly),
            0o75 => Ok(Div),
            0o76 => Ok(Mul),
            0o77 => Ok(Sub),
            _ => Err(DisassemblyFailure::InvalidOpcode(opcode)),
        }
    }
}

/// OperandAddress represents the least-significant 18 bits of an
/// instruction word.  If the top bit is set, this indicates the use
/// of deferred addressing (i.e. this bit has the same significance as
/// it does in TX-2 instructions).
#[cfg_attr(test, derive(Arbitrary))]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct OperandAddress(Address);

impl Default for OperandAddress {
    fn default() -> OperandAddress {
        OperandAddress(Address::ZERO)
    }
}

impl OperandAddress {
    pub fn is_deferred(&self) -> bool {
        let (_, deferred) = self.0.split();
        deferred
    }

    pub fn split(&self) -> (bool, Address) {
        let (physical, deferred) = self.0.split();
        (deferred, Address::from(physical))
    }

    pub fn bits(&self) -> Unsigned18Bit {
        Unsigned18Bit::from(self.0)
    }

    pub fn direct(address: Address) -> OperandAddress {
        let (_, defer) = address.split();
        assert!(!defer);
        Self(address)
    }

    pub fn deferred(address: Address) -> OperandAddress {
        let (bits, _) = address.split();
        Self(Address::join(bits, true))
    }

    fn from_raw_bits(bits: Unsigned18Bit) -> OperandAddress {
        Self(Address::from(bits))
    }
}

/// A TX-2 instruction broken down into its component fields.
#[cfg_attr(test, derive(Arbitrary))]
#[derive(Debug, PartialEq, Eq)]
pub struct SymbolicInstruction {
    pub held: bool,
    pub configuration: Unsigned5Bit,
    pub opcode: Opcode,
    pub index: Unsigned6Bit,
    pub operand_address: OperandAddress,
}

impl SymbolicInstruction {
    pub fn opcode(&self) -> Opcode {
        self.opcode
    }
}

impl Inst for SymbolicInstruction {
    fn is_held(&self) -> bool {
        self.held
    }

    fn configuration(&self) -> Unsigned5Bit {
        self.configuration
    }

    fn index_address(&self) -> Unsigned6Bit {
        self.index
    }

    fn opcode_number(&self) -> u8 {
        self.opcode.number()
    }

    fn is_deferred_addressing(&self) -> bool {
        self.operand_address.is_deferred()
    }

    fn operand_address(&self) -> OperandAddress {
        self.operand_address
    }

    fn operand_address_and_defer_bit(&self) -> Unsigned18Bit {
        self.operand_address.bits()
    }
}

impl From<&SymbolicInstruction> for Instruction {
    fn from(s: &SymbolicInstruction) -> Instruction {
        let hold_bit: u64 = if s.is_held() { 1 << 35 } else { 0 };
        let cf_bits: u64 = (u64::from(s.configuration()) & 31_u64) << 30;
        let op_bits: u64 = (u64::from(s.opcode_number()) & 63) << 24;
        let index_bits: u64 = (u64::from(s.index_address())) << 18;
        let address_and_defer_bits: u64 = s.operand_address_and_defer_bit().into();
        let val: u64 = hold_bit | cf_bits | op_bits | index_bits | address_and_defer_bits;
        Instruction(Unsigned36Bit::try_from(val).unwrap())
    }
}

#[cfg(test)]
#[proptest]
fn reversible_disassembly(input: SymbolicInstruction) {
    let inst: Instruction = Instruction::from(&input);
    let bits = inst.bits();
    match SymbolicInstruction::try_from(&inst) {
        Ok(symbolic_disassembly) => {
            assert_eq!(symbolic_disassembly, input);
        }
        Err(e) => {
            panic!("input {input:?} assembled to {bits} but that could not be disassembled ({e})");
        }
    }
}

/// Signals that an [`Instruction`] could not be converted to a
/// [`SymbolicInstruction`].
#[derive(PartialEq, Eq)]
pub enum DisassemblyFailure {
    /// The opcode field of the instruction word does not correspond
    /// to a known opcode.
    InvalidOpcode(u8),

    /// The opcode field of the instruction word corresponds to an
    /// operation we know nothing about.  This enumerator shouldn't be
    /// considered stable; we might remove it entirely.  Currently only
    /// opcode 2 yields this result (corresponding to "XEQ?"
    /// hand-written on a copy of the User Handbook).
    UnimplementedOpcode(u8),
}

impl Debug for DisassemblyFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let opcode = match self {
            DisassemblyFailure::InvalidOpcode(n) => {
                f.write_str("InvalidOpcode")?;
                n
            }
            DisassemblyFailure::UnimplementedOpcode(n) => {
                f.write_str("UnimplementedOpcode")?;
                n
            }
        };
        write!(f, "(0{opcode:o})")
    }
}

impl TryFrom<&Instruction> for SymbolicInstruction {
    type Error = DisassemblyFailure;
    fn try_from(inst: &Instruction) -> Result<SymbolicInstruction, DisassemblyFailure> {
        Ok(SymbolicInstruction {
            operand_address: inst.operand_address(),
            index: inst.index_address(),
            opcode: Opcode::try_from(inst.opcode_number())?,
            configuration: inst.configuration(),
            held: inst.is_held(),
        })
    }
}

// disassemble_word is intended to be used in the emulator's UI to
// show what the program counter is pointing at, and to show the next
// instruction to be emulated etc.  Since this is not yet implemented,
// right now the only callers are unit tests.
#[cfg(test)]
pub fn disassemble_word(w: Unsigned36Bit) -> Result<SymbolicInstruction, DisassemblyFailure> {
    let inst: Instruction = Instruction(w);
    dbg!(inst.operand_address());
    SymbolicInstruction::try_from(&inst)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config_value(n: u8) -> Unsigned5Bit {
        Unsigned5Bit::try_from(n).expect("valid test data")
    }

    #[test]
    fn test_instruction_jmp() {
        let inst = Instruction(Unsigned36Bit::from(0o0500377750_u32));
        assert_eq!(
            inst.operand_address(),
            OperandAddress::direct(Address::from(u18!(0o377_750u32))),
            "wrong address"
        );
        assert!(!inst.is_deferred_addressing(), "wrong dismiss");
        assert_eq!(inst.index_address(), 0, "wrong index");
        assert_eq!(inst.opcode_number(), 5, "wrong opcode");
        assert!(inst.configuration().is_zero(), "wrong cf");
        assert!(!inst.is_held(), "wrong held");
    }

    #[test]
    fn test_instruction_held() {
        assert!(!Instruction(Unsigned36Bit::ZERO).is_held());
        assert!(
            Instruction(
                Unsigned36Bit::try_from(1_u64 << 35).expect("test data should be in-range")
            )
            .is_held()
        );
    }

    #[test]
    fn test_opcode_value_round_trip() {
        for opcode_number in 0..u8::MAX {
            if let Ok(opcode) = Opcode::try_from(opcode_number) {
                assert_eq!(opcode_number, opcode.number());
            }
        }
    }

    #[test]
    fn test_disassemble_jmp() {
        assert_eq!(
            disassemble_word(u36!(0o000_500_377_750)),
            Ok(SymbolicInstruction {
                operand_address: OperandAddress::direct(Address::from(u18!(0o0377750))),
                index: Unsigned6Bit::ZERO,
                opcode: Opcode::Jmp,
                configuration: config_value(0),
                held: false,
            })
        );
    }

    #[test]
    fn test_disassemble_jpx() {
        assert_eq!(
            disassemble_word(
                Unsigned36Bit::try_from(0o700_603_377_752_u64)
                    .expect("test data should be in range")
            ),
            Ok(SymbolicInstruction {
                operand_address: OperandAddress::direct(Address::from(u18!(0o0377752))),
                index: Unsigned6Bit::try_from(3_u8).unwrap(),
                opcode: Opcode::Jpx,
                configuration: config_value(24), // -7
                held: true,
            })
        );

        assert_eq!(
            disassemble_word(
                Unsigned36Bit::try_from(0o360_601_377_751_u64)
                    .expect("test data should be in range")
            ),
            Ok(SymbolicInstruction {
                operand_address: OperandAddress::direct(Address::from(u18!(0o0377751))),
                index: Unsigned6Bit::ONE,
                opcode: Opcode::Jpx,
                configuration: config_value(30),
                held: false,
            })
        );
    }

    #[test]
    fn test_disassemble_dpx() {
        // This instruction is taken from the code for Leonard
        // Kleinrock's network simulation, at address 200762.
        assert_eq!(
            disassemble_word(u36!(0o011_600_777_605_u64)),
            Ok(SymbolicInstruction {
                operand_address: OperandAddress::deferred(Address::from(u18!(0o377_605))),
                index: Unsigned6Bit::try_from(0_u8).unwrap(),
                opcode: Opcode::Dpx,
                configuration: config_value(1),
                held: false,
            })
        );
    }

    #[test]
    fn test_assemble_rsx() {
        // This instruction is taken from position 0o3 of the standard
        // reader leader on page 5-26 of the Users Handbook.
        let sym = SymbolicInstruction {
            held: false,
            configuration: Unsigned5Bit::try_from(1_u8).expect("valid configuraiton field"),
            opcode: Opcode::Rsx,
            index: Unsigned6Bit::try_from(0o54_u8).expect("valid index field"),
            operand_address: OperandAddress::direct(Address::from(u18!(5))),
        };
        let got: u64 = u64::from(Instruction::from(&sym).bits());
        const EXPECTED: u64 = 0o011_154_000_005_u64;
        assert_eq!(
            got, EXPECTED,
            "Mismatch in assembly of {:?}: expected 0o{:012o}, got 0o{:012o}",
            &sym, EXPECTED, got
        );
    }
}
