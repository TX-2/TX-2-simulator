/// Human-oriented formatting for instructions (or parts of instructions).
use std::fmt::{self, Display, Formatter, Octal, Write};

use super::super::bitselect::{BitPos, BitSelector, bit_select};
use super::super::charset::{
    NoSubscriptKnown, NoSuperscriptKnown, subscript_char, superscript_char,
};
use super::super::instruction::{
    DisassemblyFailure, Inst, Opcode, OperandAddress, SkmBitSelector, SymbolicInstruction,
    index_address_to_bit_selection,
};
use super::super::prelude::*;

/// Convert an opcode to its text representation.
///
/// The primary (i.e. not supernumerary) opcode mnemonic is used,
/// because the configuration value which would identify a
/// supernumerary opcode is not passed to the `fmt` method of the
/// `Display` trait.
impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Opcode::*;
        f.write_str(match self {
            Opr => "OPR",
            Jmp => "JMP",
            Jpx => "JPX",
            Jnx => "JNX",
            Aux => "AUX",
            Rsx => "RSX",
            Skx => "SKX",
            Exx => "EXX",
            Adx => "ADX",
            Dpx => "DPX",
            Skm => "SKM",
            Lde => "LDE",
            Spf => "SPF",
            Spg => "SPG",
            Lda => "LDA",
            Ldb => "LDB",
            Ldc => "LDC",
            Ldd => "LDD",
            Ste => "STE",
            Flf => "FLF",
            Flg => "FLG",
            Sta => "STA",
            Stb => "STB",
            Stc => "STC",
            Std => "STD",
            Ite => "ITE",
            Ita => "ITA",
            Una => "UNA",
            Sed => "SED",
            Jov => "JOV",
            Jpa => "JPA",
            Jna => "JNA",
            Exa => "EXA",
            Ins => "INS",
            Com => "COM",
            Tsd => "TSD",
            Cya => "CYA",
            Cyb => "CYB",
            Cab => "CAB",
            Noa => "NOA",
            Dsa => "DSA",
            Nab => "NAB",
            Add => "ADD",
            Sca => "SCA",
            Scb => "SCB",
            Sab => "SAB",
            Tly => "TLY",
            Div => "DIV",
            Mul => "MUL",
            Sub => "SUB",
        })
    }
}

/// Format an operand address in octal.
///
/// Deferred addresses are formatted in square brackets.  TX-2
/// documentation seems variously to represent deferred addressing
/// with `[...]` or `*`.  We use `[...]`.
impl Octal for OperandAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let (defer, physical_address) = self.split();
        if defer {
            f.write_char('[')?;
        }
        write!(f, "{physical_address:o}")?;
        if defer {
            f.write_char(']')?;
        }
        Ok(())
    }
}

impl Display for DisassemblyFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let opcode = match self {
            DisassemblyFailure::InvalidOpcode(n) => {
                f.write_str("invalid opcode")?;
                n
            }
            DisassemblyFailure::UnimplementedOpcode(n) => {
                f.write_str("unimplemented opcode")?;
                n
            }
        };
        write!(f, " {opcode:03o}")
    }
}

fn octal_superscript_u8(n: u8) -> Result<String, NoSuperscriptKnown> {
    format!("{n:o}").chars().map(superscript_char).collect()
}

fn subscript(s: &str) -> Result<String, NoSubscriptKnown> {
    s.chars().map(subscript_char).collect()
}

fn octal_subscript_number(n: u8) -> String {
    subscript(&format!("{n:o}")).unwrap()
}

fn write_opcode(
    op: Opcode,
    cfg: Unsigned5Bit,
    base_address_bits: Unsigned18Bit,
    f: &mut Formatter<'_>,
) -> Result<(), fmt::Error> {
    let w = Unsigned36Bit::from(base_address_bits);
    let bit_2_8 = bit_select(
        w,
        BitSelector {
            quarter: Quarter::Q2,
            bitpos: BitPos::B8,
        },
    );
    let bit_2_7 = bit_select(
        w,
        BitSelector {
            quarter: Quarter::Q2,
            bitpos: BitPos::B8,
        },
    );
    // Where there is a supernumerary mnemonic, prefer it.
    // This list is taken from table 7-3 in the Users
    // Handbook.
    let cfg = u8::from(cfg);
    match op {
        Opcode::Opr => f.write_str(if bit_2_8 {
            "OPR"
        } else if bit_2_7 {
            "AOP"
        } else {
            "IOS"
        }),
        Opcode::Jmp => f.write_str(match cfg {
            0o00 => "JMP",
            0o01 => "BRC",
            0o02 => "JPS",
            0o03 => "BRS",
            0o14 => "JPQ",
            0o15 => "BPQ",
            0o16 => "JES",
            0o20 => "JPD",
            0o21 => "JMP",
            0o22 => "JDS",
            0o23 => "BDS",
            _ => "JMP",
        }),
        Opcode::Skx => f.write_str(match cfg {
            0o00 => "REX",
            0o02 => "INX",
            0o03 => "DEX",
            0o04 => "SXD",
            0o06 => "SXL",
            0o07 => "SXG",
            0o10 => "RXF",
            0o20 => "RXD",
            0o30 => "RFD",
            _ => "SKX",
        }),
        Opcode::Skm => f.write_str(match cfg {
            0o00 => "SKM",
            0o01 => "MKC",
            0o02 => "MKZ",
            0o03 => "MKN",
            0o10 => "SKU",
            0o11 => "SUC",
            0o12 => "SUZ",
            0o13 => "SUN",
            0o20 => "SKZ",
            0o21 => "SZC",
            0o22 => "SZZ",
            0o23 => "SZN",
            0o30 => "SKN",
            0o31 => "SNC",
            0o32 => "SNZ",
            0o33 => "SNN",
            0o04 => "CYR",
            0o05 => "MCR",
            0o06 => "MZR",
            0o07 => "MNR",
            0o34 => "SNR",
            0o24 => "SZR",
            0o14 => "SUR",
            _ => "SKM",
        }),
        _ => write!(f, "{op}"),
    }
}

impl Display for SymbolicInstruction {
    /// Convert a `SymbolicInstruction` to text (Unicode) form.
    ///
    /// We use supernumerary opcode mnemonics where one is suitable
    /// (though we keep the original configuration value).
    /// Configuration values are rendered as superscripts.  Index
    /// addresses are rendered as subscripts and operand addresses as
    /// normal digits.  These match the conventions used in the TX-2
    /// User Handbook.
    ///
    /// The User Handbook indicates that the hold bit should be
    /// represented as _h_ (lower-case "H") when 1 and as _h_ with
    /// overbar when 0.  We use &#x0127; (a Unicode lower-case h with
    /// stroke) to signal that.  When the defer bit takes the value
    /// which is the default for the current instruction, nothing
    /// (neither "h" nor "&#x0127;") is printed.
    ///
    /// This documentation comment previously said that Sketchpad used
    /// ':' for hold, but I cannot find an example of this in Jurij's
    /// transcription, so the statement that Sketchpad used ':' must
    /// have been wrong.
    ///
    /// The representation of instructions may change over time as we
    /// discover archival material containing program listings.  The
    /// idea is to generally be consistent with the materials we have
    /// available.
    ///
    /// Instructions such as SKM should show the index address as a
    /// bit selector, but this may not yet happen in all the cases we
    /// would want it.  This will change over time as we implement
    /// more of the instruction opcodes in the emulator.
    ///
    /// Some addresses (arithmetic unit registers for example) are
    /// "well-known" but we do not currently display these in symbolic
    /// form.
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        // This implementation of Display is incomplete because, for
        // example there are some instructions for which the index
        // value is rendered as X.Y (I believe these are the
        // bit-manipulation instructions).  The I/O instructions also
        // have special cases.
        //
        // We also don't render "special" addresses, such as the
        // addresses of actual registers, in symbolic form.
        match (self.opcode().hold_is_implicit(), self.is_held()) {
            (true, false) => {
                // I didn't find any examples of this (a programmer
                // override to make a normally-held opcode actually
                // not held) in the documentation so far.
                //
                // We will use the notation given in section 6-2.1
                // ("Instruction Words") of the User Handbook.
                f.write_str("\u{0127} ")?; // lower-case h with stroke
            }
            (false, true) => {
                // Some documentation uses ':' to indicate a held
                // instruction, but this is not part of the Lincoln
                // Writer character set.
                f.write_str("h ")?;
            }
            _ => {
                // This is the default, so it needs no annotation.
            }
        }
        if !self.configuration().is_zero() {
            let cf: u8 = self.configuration().into();
            f.write_str(&octal_superscript_u8(cf).unwrap())?;
        }
        let base_address = self.operand_address_and_defer_bit();
        write_opcode(self.opcode(), self.configuration(), base_address, f)?;
        let j = self.index_address();
        match self.opcode() {
            Opcode::Skm => {
                // The index address field in SKM instructions
                // identify a bit in the operand to operate on, and
                // are shown in the form "q.b".  The "q" identifies
                // the quarter and the "b" the bit.
                let selector: SkmBitSelector = index_address_to_bit_selection(j);
                let rendering: String = subscript(&selector.to_string()).unwrap();
                f.write_str(&rendering)?;
            }
            _ => {
                if j != 0 {
                    f.write_str(&octal_subscript_number(u8::from(j)))?;
                }
            }
        }
        write!(f, " {:>08o}", self.operand_address()) // includes [] if needed.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config_value(n: u8) -> Unsigned5Bit {
        Unsigned5Bit::try_from(n).expect("valid test data")
    }

    #[test]
    fn test_octal_superscript_u8() {
        assert_eq!(
            octal_superscript_u8(0),
            Ok("\u{2070}".to_string()),
            "0 decimal is 0 octal"
        );
        assert_eq!(
            octal_superscript_u8(1),
            Ok("\u{00B9}".to_string()),
            "1 decimal is 1 octal"
        );
        assert_eq!(
            octal_superscript_u8(4),
            Ok("\u{02074}".to_string()),
            "4 decimal is 4 octal"
        );
        assert_eq!(
            octal_superscript_u8(11),
            Ok("\u{00B9}\u{00B3}".to_string()),
            "11 decimal is 13 octal"
        );
        assert_eq!(
            octal_superscript_u8(255),
            Ok("\u{00B3}\u{2077}\u{2077}".to_string()),
            "255 decimal is 377 octal"
        );
    }

    #[test]
    fn test_display_jmp() {
        let sinst = SymbolicInstruction {
            operand_address: OperandAddress::direct(Address::from(u18!(0o0_377_750))),
            index: Unsigned6Bit::ZERO,
            opcode: Opcode::Jmp,
            configuration: Unsigned5Bit::ZERO,
            held: false,
        };
        assert_eq!(&sinst.to_string(), "JMP 377750");
    }

    #[test]
    fn test_display_jpx_sutherland() {
        // Example from the plotter service routine from Ivan Sutherland's
        // SKETCHPAD, as held by the Computer History museum, PDF file
        // 102726903-05-02-acc.pdf page 124 (hand-written page number
        // 274).
        //
        // -1 JPX $ UNITS OFF1        76 06 34 200 156
        //
        // The $ there is a placeholder (just in this comment) for a blob
        // on the scanned page that I simply can't read.  The assembled
        // word on the right-hand side is easier to read, but the value
        // there (34 octal) doesn't seem to correspond very well with what
        // looks like a single digit index value.
        //
        // Based on Jurij's transcription of the Sketchpad code, I
        // think $ is actually @alpha@.  From the sk2 transcript:
        //
        // 4986 S1@alpha@= 34
        // [..]
        // 5002 @alpha@= S1@alpha@
        // [..]
        // 5337 @sup_minus@@sup_1@JPX @sub_alpha@ UNITS OFF1
        //
        // Hold is used in conjunction with the JPX opcode in order to
        // prevent DISMISS (see page 3-26 of the User Guide which
        // describes JPX).  Hence the -1 seems reasonable, though in
        // any case M4 automatically puts a hold on JPX (as described
        // on page 3-27 of the user guide).
        //
        // The TSX-2 has a front-panel button "Hold on LSPB" which
        // makes the system behave as if the hold bit were set on all
        // instructions; see User Guide, page 5-17.
        let sinst = SymbolicInstruction {
            operand_address: OperandAddress::direct(Address::from(u18!(0o200_156_u32))),
            index: Unsigned6Bit::try_from(0o34_u8).unwrap(),
            opcode: Opcode::Jpx,
            configuration: config_value(0o36), // 036 octal = 30 decimal = 0b11110
            held: true,
        };
        assert_eq!(&sinst.to_string(), "³⁶JPX₃₄ 200156");
    }

    #[test]
    fn test_display_jpx_progex() {
        // These cases are taken from the programming examples
        // document (memo 6M-5780, July 23, 1958).

        // Example from Program I, address 377 765, instruction word 36 06 01 377 751.
        let sinst1 = SymbolicInstruction {
            operand_address: OperandAddress::direct(Address::from(u18!(0o0_377_751))),
            index: Unsigned6Bit::ONE,
            opcode: Opcode::Jpx,
            // 036 = 30 decimal = 0b11110, which is one's complement -1.
            configuration: config_value(0o36),

            // In the example program, we see the octal equivalent of
            // the instruction, and the top bit is clearly not set, so
            // instruction is not held.
            held: false,
        };
        // In the Program I listing, there is no annotation indicating
        // that the instruction is not held.  This memo is from 1958.
        // Perhaps the conventions changed between then and the date
        // of the User Handbook (1963).
        //
        // The actual example gives a configuration value of -1, but
        // we have to choose a single way to render config values
        // (i.e. choose one of -1 or 36 for bit pattern 0b11110).
        // Compare for example test_display_rsx(), which points to an
        // example where the configuration value is formatted the
        // other way.
        assert_eq!(&sinst1.to_string(), "ħ ³⁶JPX₁ 377751");

        // Example from Program II ("Inchworm"), address 15, instruction word not stated,
        let sinst2 = SymbolicInstruction {
            operand_address: OperandAddress::direct(Address::from(u18!(0o0_377_752))),
            index: Unsigned6Bit::try_from(3_u8).unwrap(),
            opcode: Opcode::Jpx,
            // In the Program II example, the configuration value is
            // given as -7.  We're using octal 30 and believe that is
            // equivalent.
            configuration: Unsigned5Bit::try_from(0o30_u8).expect("valid test data"),
            held: false,
        };
        // ħ here for the same reason as sinst1 disassembled above.
        assert_eq!(&sinst2.to_string(), "ħ ³⁰JPX₃ 377752");
    }

    #[test]
    fn test_display_rsx() {
        // Example from Program II ("Inchworm"), address 377 755,
        // instruction word 74 11 71 377 763.  Note the leading colon,
        // indicating the hold bit.  We use 'h' instead since ':' is
        // not actually part of the Lincoln Writer character set.
        let sinst = SymbolicInstruction {
            operand_address: OperandAddress::direct(Address::from(u18!(0o377_762))),
            index: Unsigned6Bit::try_from(0o71_u8).unwrap(),
            opcode: Opcode::Rsx,
            configuration: config_value(0o34),
            held: true, // this is signaled by the 'h'.
        };
        assert_eq!(&sinst.to_string(), "h ³⁴RSX₇₁ 377762"); // the 'h' indicates `held`
    }

    #[test]
    fn test_display_ios() {
        // This instruction appears in the listing for the "READER
        // LEADER" in section 5-5.2 of the Users Handbook.
        let sinst = SymbolicInstruction {
            operand_address: OperandAddress::direct(Address::from(u18!(0o020_000_u32))),
            index: Unsigned6Bit::try_from(0o52_u8).unwrap(),
            // Bits 2.7 and 2.8 in the base address field distinguish
            // the IOS and AOP variants of the OPR opcode.  If they're
            // both zero, we're looking at IOS.
            //
            // This distinction and the bits used to make it are
            // described in section 7-11 ("MISCELLANEOUS OPERATION
            // CODES") of Volume 1 of the TX-2 Technical Manual.
            opcode: Opcode::Opr,
            configuration: config_value(0o1),
            held: false,
        };
        assert_eq!(&sinst.to_string(), "¹IOS₅₂ 20000");
    }

    #[test]
    fn test_disassemble_ios() {
        // This instruction appears in the listing for the "READER
        // LEADER" in section 5-5.2 of the Users Handbook.
        let inst = Instruction::from(u36!(0o010_452_020_000));
        assert_eq!(
            SymbolicInstruction::try_from(&inst),
            Ok(SymbolicInstruction {
                operand_address: OperandAddress::direct(Address::from(u18!(0o020_000_u32))),
                index: Unsigned6Bit::try_from(0o52_u8).unwrap(),
                opcode: Opcode::Opr,
                configuration: config_value(0o1),
                held: false,
            })
        );
    }
    #[test]
    fn test_assemble_ios() {
        // This instruction appears in the listing for the "READER
        // LEADER" in section 5-5.2 of the Users Handbook, in both
        // symbolic and octal form.
        assert_eq!(
            Instruction::from(&SymbolicInstruction {
                operand_address: OperandAddress::direct(Address::from(u18!(0o020_000_u32))),
                index: Unsigned6Bit::try_from(0o52_u8).unwrap(),
                opcode: Opcode::Opr,
                configuration: config_value(0o1),
                held: false,
            })
            .bits(),
            u36!(0o010_452_020_000)
        );
    }
}
