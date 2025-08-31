//! Code for identifying quarters and bits of TX-2 words using the
//! notations from the TX-2 documentation.
//!
//! In this notation, "bit 2.3" is bit 3 (counting from 1 as the least
//! significant) of quarter 2 (counting from 1 as the least
//! significant).  Bit 2.3 would have the value 02000 (octal).
use std::fmt::{Display, Write};

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

/// Render the quarter ("q") part of the bit selector ("q.b").
impl Display for Quarter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            Quarter::Q1 => '1',
            Quarter::Q2 => '2',
            Quarter::Q3 => '3',
            Quarter::Q4 => '4',
        })
    }
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
