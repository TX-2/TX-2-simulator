//! Instruction and event timing.
//!
//! This module deals with the relationship between actual time and the
//! time taken by events in the simulator.
//!
//! In the physical TX-2 machine, the operator has some control over
//! the execution speed of the computer, and eventually we will
//! accomodate this control, but for now this is not implemented.

use super::memory::*;
use base::instruction::Opcode;
use base::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum MemoryType {
    S,
    T,
    V,
}

fn address_to_memory_type(addr: &Address) -> MemoryType {
    let addr: u32 = u32::from(addr);
    if addr < T_MEMORY_START {
        MemoryType::S
    } else if addr < V_MEMORY_START {
        MemoryType::T
    } else {
        MemoryType::V
    }
}

/// These figures are taken, approximately, from section 7-8 of the
/// User Handbook.
pub(crate) fn estimate_instruction_ns(
    inst_from: Address,
    op: u8,
    defer_from: Option<Address>,
    operand_from: Option<Address>,
) -> u64 {
    // Units of tenths are tenths of microseconds
    let inst_loaded_from = address_to_memory_type(&inst_from);
    let mut tenths: u64 = if inst_loaded_from == MemoryType::S {
        80
    } else {
        60
    };
    // instruction from : add 20 for T or 40 for S memory
    tenths += match inst_loaded_from {
        MemoryType::V | MemoryType::T => 0,
        MemoryType::S => 20,
    };
    if let Ok(opcode) = Opcode::try_from(op) {
        tenths += match opcode {
            Opcode::Ios => 72,
            Opcode::Jmp => 56,
            Opcode::Jpx => 76,
            Opcode::Jnx => 76,
            Opcode::Aux => 116,
            Opcode::Rsx => 108,
            Opcode::Skx => 80,
            Opcode::Exx => 112,
            Opcode::Adx => 84,
            Opcode::Dpx => 100,
            Opcode::Skm => 96,
            Opcode::Lde => 68,
            Opcode::Spf => 88,
            Opcode::Spg => 96,
            Opcode::Lda => 64,
            Opcode::Ldb => 68,
            Opcode::Ldc => 68,
            Opcode::Ldd => 68,
            Opcode::Ste => 68,
            Opcode::Flf => 68,
            Opcode::Flg => 84,
            Opcode::Sta => 68,
            Opcode::Stb => 68,
            Opcode::Stc => 68,
            Opcode::Std => 68,
            Opcode::Ite => 64,
            Opcode::Ita => 68,
            Opcode::Una => 48,
            Opcode::Sed => 80,
            Opcode::Jov => 60,
            Opcode::Jpa => 60,
            Opcode::Jna => 60,
            Opcode::Exa => 48,
            Opcode::Ins => 68,
            Opcode::Com => 68,
            Opcode::Tsd => 76,
            Opcode::Cya => 382,
            Opcode::Cyb => 1060,
            Opcode::Cab => 1072,
            Opcode::Noa => 68,
            Opcode::Dsa => 52,
            Opcode::Nab => 320,
            Opcode::Add => 68,
            Opcode::Sca => 1060,
            Opcode::Scb => 1044,
            Opcode::Sab => 1072,
            Opcode::Tly => 68,
            Opcode::Div => 770,
            Opcode::Mul => 100,
            Opcode::Sub => 68,
        }
    }
    if operand_from == Some(inst_from) || defer_from == Some(inst_from) {
        tenths += 20;
    }
    if operand_from == defer_from {
        tenths += 20;
    }

    // Convert from tenths of a microsecond to nanoseconds.
    tenths * 100
}
