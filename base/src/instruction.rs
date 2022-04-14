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
//! `34 21 00 377,751     34SPF 377751`
//!
//! Here, the operand memory address is 0377751.  The index is 00.
//! The opcode is `SPF`, octal 21.  The top 6 bits are 034, or 11100
//! binary.  The user guide states that `SPF` is not configurable, so
//! presumably the configuration field simply specifies the address in
//! F-memory that we will write to.
//!
//! Later in the same page we have
//!
//! `74 11 71 377,762    34RSX71  377,762`
//!
//! RSX is opcode 11.  Hence the top 6 bits are 074 = 111100 binary,
//! Of those only 034=11100 binary seem to be configuration code.  But
//! the hold bit seems to be set without this being indicated in the
//! symbolic form of the instruction.

use std::fmt::{self, Debug, Formatter};

use crate::prelude::*;
use crate::subword;

mod format;

/// `Quarter` describes which quarter of a word an SKM instruction
/// will operate on.  See the [`index_address_to_bit_selection`]
/// function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quarter {
    Q1 = 0,
    Q2 = 1,
    Q3 = 2,
    Q4 = 3,
}

/// Convert the `Quarter` enumeration value into the position of that
/// quarter (counting from the least-significant end of the 36-bit
/// word).
impl From<Quarter> for u8 {
    fn from(q: Quarter) -> u8 {
        match q {
            Quarter::Q1 => 0,
            Quarter::Q2 => 1,
            Quarter::Q3 => 2,
            Quarter::Q4 => 3,
        }
    }
}

/// `BitSelector` is primarily for use with the SKM instruction which
/// can access bits 1-9 of quarters, plus the meta and parity bits (of
/// the full word).  Hence the wider range.  See the
/// [`index_address_to_bit_selection`] function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSelector {
    pub quarter: Quarter,
    /// `bitpos` values 1 to 9 inclusive are normal bit positions in a
    /// quarter.  0 is a valid value but not a valid bit (so a default
    /// will be used when SKM tests bit 0).  10 is the meta bit.  11
    /// is the parity bit stored in memory.  12 is the parity value
    /// computed from the bits stored in memory.
    pub bitpos: u8, // takes values 0..=12.
}

/// Convert the index address field of an SKM instruction into a
/// `BitSelector` struct describing which bit we will operate on.
pub fn index_address_to_bit_selection(index_address: Unsigned6Bit) -> BitSelector {
    let j: u8 = u8::from(index_address);
    BitSelector {
        quarter: match (j >> 4) & 0b11 {
            0 => Quarter::Q4,
            1 => Quarter::Q1,
            2 => Quarter::Q2,
            3 => Quarter::Q3,
            _ => unreachable!(),
        },
        bitpos: j & 0b1111_u8,
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
            Ok(sym) => format!("{}", sym),
            Err(e) => format!("(invalid instruction: {})", e),
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

    /// The operand address field (including the defer bit)
    fn operand_address(&self) -> OperandAddress;

    /// Fetches the operand address with the defer bit (if set) in bit
    /// position 17.
    fn operand_address_and_defer_bit(&self) -> Unsigned18Bit;
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
        self.0 & 0o400_000_u64 != 0
    }

    fn operand_address(&self) -> OperandAddress {
        const PHYSICAL_ADDRESS_BITS: u32 = 0o377_777;
        let physical_address = Address::from(subword::right_half(self.0) & PHYSICAL_ADDRESS_BITS);
        if self.0 & 0o400_000 != 0 {
            OperandAddress::Deferred(physical_address)
        } else {
            OperandAddress::Direct(physical_address)
        }
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
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Opcode {
    // opcode 1 is unused
    // opcode 2 may be XEQ, but no documentation on this.
    // opcode 3 is unused
    Ios = 0o4, // see also Vol 3 page 16-05-07
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
            0o4 => Ok(Ios),
            0o5 => Ok(Jmp),
            0o6 => Ok(Jpx),
            0o7 => Ok(Jnx),
            0o10 => Ok(Aux),
            0o11 => Ok(Rsx),
            0o12 => Ok(Skx),
            11 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            12 => Ok(Exx),
            13 => Ok(Adx),
            14 => Ok(Dpx),
            15 => Ok(Skm),
            16 => Ok(Lde),
            17 => Ok(Spf),
            18 => Ok(Spg),
            19 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            20 => Ok(Lda),
            21 => Ok(Ldb),
            22 => Ok(Ldc),
            23 => Ok(Ldd),
            24 => Ok(Ste),
            25 => Ok(Flf),
            26 => Ok(Flg),
            27 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            28 => Ok(Sta),
            29 => Ok(Stb),
            30 => Ok(Stc),
            31 => Ok(Std),
            32 => Ok(Ite),
            33 => Ok(Ita),
            34 => Ok(Una),
            35 => Ok(Sed),
            // 36 is unused
            36 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            37 => Ok(Jov),
            38 => Ok(Jpa),
            39 => Ok(Jna),
            40..=43 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            44 => Ok(Exa),
            45 => Ok(Ins),
            46 => Ok(Com),
            47 => Ok(Tsd),
            48 => Ok(Cya),
            49 => Ok(Cyb),
            50 => Ok(Cab),
            51 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            52 => Ok(Noa),
            53 => Ok(Dsa),
            54 => Ok(Nab),
            55 => Ok(Add),
            56 => Ok(Sca),
            57 => Ok(Scb),
            58 => Ok(Sab),
            59 => Err(DisassemblyFailure::InvalidOpcode(opcode)),
            60 => Ok(Tly),
            61 => Ok(Div),
            62 => Ok(Mul),
            63 => Ok(Sub),
            _ => Err(DisassemblyFailure::InvalidOpcode(opcode)),
        }
    }
}

/// OperandAddress represents the least-significant 18 bits of an
/// instruction word.  By using an enumeration for this we make it
/// harder to accidentally mix up operand addresses (which might have
/// a defer bit) and physical addresses (which only have 17 useful
/// bits, since the highest physical memory address is 377 777).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum OperandAddress {
    Direct(Address),
    Deferred(Address),
}

/// A TX-2 instruction broken down into its component fields.
#[derive(Debug, PartialEq, Eq)]
pub struct SymbolicInstruction {
    operand_address: OperandAddress,
    index: Unsigned6Bit,
    opcode: Opcode,
    configuration: Unsigned5Bit,
    held: bool,
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
        matches!(self.operand_address, OperandAddress::Deferred(_))
    }

    fn operand_address(&self) -> OperandAddress {
        self.operand_address
    }

    fn operand_address_and_defer_bit(&self) -> Unsigned18Bit {
        const ADDRESS_DEFER_BIT: u32 = 0o400_000;
        match self.operand_address {
            OperandAddress::Deferred(addr) => {
                let defer_bit = Unsigned18Bit::try_from(ADDRESS_DEFER_BIT).unwrap();
                Unsigned18Bit::from(addr) | defer_bit
            }
            OperandAddress::Direct(addr) => Unsigned18Bit::from(addr),
        }
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
        write!(f, "(0{:o})", opcode)
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

    fn addr(a: u32) -> Address {
        Address::from(Unsigned18Bit::try_from(a).expect("valid test data"))
    }

    #[test]
    fn test_instruction_jmp() {
        let inst = Instruction(Unsigned36Bit::from(0o0500377750_u32));
        assert_eq!(
            inst.operand_address(),
            OperandAddress::Direct(addr(0o0377750_u32)),
            "wrong address"
        );
        assert_eq!(inst.is_deferred_addressing(), false, "wrong dismis");
        assert_eq!(inst.index_address(), 0, "wrong index");
        assert_eq!(inst.opcode_number(), 5, "wrong opcode");
        assert!(inst.configuration().is_zero(), "wrong cf");
        assert_eq!(inst.is_held(), false, "wrong held");
    }

    #[test]
    fn test_instruction_held() {
        assert!(!Instruction(Unsigned36Bit::ZERO).is_held());
        assert!(Instruction(
            Unsigned36Bit::try_from(1_u64 << 35).expect("test data should be in-range")
        )
        .is_held());
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
            disassemble_word(
                Unsigned36Bit::try_from(0o000_500_377_750).expect("test data should be in range")
            ),
            Ok(SymbolicInstruction {
                operand_address: OperandAddress::Direct(addr(0o0377750)),
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
                operand_address: OperandAddress::Direct(addr(0o0377752)),
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
                operand_address: OperandAddress::Direct(addr(0o0377751)),
                index: Unsigned6Bit::ONE,
                opcode: Opcode::Jpx,
                configuration: config_value(30),
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
            operand_address: OperandAddress::Direct(Address::new(u18!(5))),
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
