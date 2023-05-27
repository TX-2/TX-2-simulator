//! This is an implementation of unsigned types of various bit
//! widths which accompanies the SignedXXBit one's-complement types.
//! Since these types are unsigned, there is no sign bit and they
//! aren't really one's-complement types.  But the interface to these
//! is mostly similar to that of the signed (real one's-complement)
//! types.

use std::cmp::Ordering;
use std::fmt::{self, Debug, Display, Formatter, Octal};
use std::hash::{Hash, Hasher};

use serde::Serialize;

use super::super::subword::{right_half, split_halfword, split_halves};
use super::error::ConversionFailed;
use super::signed::*;
use super::{Sign, WordCommon};

#[cfg(test)]
mod tests;

/// This macro implements conversions from native types to Unsigned*Bit
/// which are always possible (e.g. From<u8> for Unsigned9Bit).
macro_rules! from_native_type_to_self {
    ($SelfT:ty, $($from:ty)*) => {
        $(
            impl From<$from> for $SelfT {
                fn from(n: $from) -> Self {
                    Self {
                        bits: n.into(),
                    }
                }
            }
        )*
    }
}

/// This macro implements conversions from Unsigned*Bit to native
/// types which are always possible (e.g. From<Unsigned9Bit> for i16).
macro_rules! from_self_to_native_type {
    ($SelfT:ty, $($to:ty)*) => {
        $(
            impl From<$SelfT> for $to {
                fn from(n: $SelfT) -> $to {
                    // Note that $InnerT for Unsigned9Bit is u16, and
                    // from_self_to_native_type is called with $to =
                    // i16, because the limits of Unsigned9Bit are
                    // wholly inside the limits of i16.  However,
                    // since some u16 values call outside the range of
                    // i16, we cannot use .into() here.  That is, we
                    // know more about the range of values n.bits can
                    // take than te compiler knows).
                    n.bits as $to
                }
            }
        )*
    }
}

/// This macro implements conversions from Unsigned*Bit to native
/// types where the conversion may not always fit.  For example
/// TryFrom<Unsigned18Bit> for u8.
macro_rules! try_from_self_to_native_type {
    ($SelfT:ty, $($to:ty)*) => {
        $(
            impl TryFrom<$SelfT> for $to {
                type Error = ConversionFailed;
                fn try_from(n: $SelfT) -> Result<$to, ConversionFailed> {
                    <$to>::try_from(n.bits).map_err(|_| ConversionFailed::TooLarge)
                }
            }
        )*
    }
}

/// This macro implements a conversions from native types to
/// Unsigned*Bit where the conversion may not always fit.  For example
/// TryFrom<u64> for Unsigned36Bit.
macro_rules! try_from_native_type_to_self {
    ($SelfT:ty, $InnerT:ty, $($from:ty)*) => {
        $(
            impl TryFrom<$from> for $SelfT {
                type Error = ConversionFailed;
                fn try_from(n: $from) -> Result<Self, ConversionFailed> {
                    let bits: $InnerT = match n.try_into() {
                        Err(_) => {
                            // Because $InnerT is unsigned, we know
                            // that n < 0 is always an error case.
                            // Since this macro also gets used for
                            // conversions from unsigned types,
                            // sometimes this conditional is useless
                            // (and we expect it to be optimized
                            // away).
                            #[allow(unused_comparisons)]
                            if n < 0 {
                                return Err(ConversionFailed::TooSmall);
                            } else {
                                return Err(ConversionFailed::TooLarge);
                            }
                        }
                        Ok(value) if value > Self::VALUE_BITS => {
                            return Err(ConversionFailed::TooLarge);
                        }
                        Ok(value) => value,
                    };
                    Ok(
                        Self {
                            bits,
                        }
                    )
                }
            }
        )*
    }
}

/// This macro implements the base functionality of the unsigned
/// types.  The `SelfT` argument is the name of the (unsigned in this
/// case) type we are defining.  `BITS` is the bit width of the type
/// we are defining.  `InnerT` is the name of the native type which
/// will store those bits.  `SignedPeerT` is the name of the
/// equivalent signed type having the same width (e.g. for
/// `Unsigned18Bit` this should be `Signed`8Bit`).
macro_rules! unsigned_ones_complement_impl {
    ($SelfT:ty, $BITS:expr, $InnerT:ty, $SignedPeerT:ty) => {
        impl $SelfT {
            const MODULUS: $InnerT = (1 << $BITS);
            const VALUE_BITS: $InnerT = Self::MODULUS - 1;

            pub const MAX: Self = Self {
                bits: Self::MODULUS - 1,
            };

            pub const ZERO: Self = Self { bits: 0 };
            pub const ONE: Self = Self { bits: 1 };
            pub const MIN: Self = Self::ZERO;

            // This will always fail at compile time, so no need to
            // hide it.  It's pub so that it can be used in u36!() and
            // similar.
            pub const fn new<const N: $InnerT>() -> $SelfT {
                type Word = $SelfT;
                struct Helper<const M: $InnerT>;
                impl<const M: $InnerT> Helper<M> {
                    const U: Word = {
                        if M > Word::MAX.bits {
                            panic!("input value is out of range")
                        } else {
                            Word {
                                bits: Word::MAX.bits & M,
                            }
                        }
                    };
                }
                Helper::<N>::U
            }

            pub const fn is_zero(&self) -> bool {
                self.bits == 0
            }

            pub const fn is_negative(&self) -> bool {
                false
            }

            pub const fn is_positive(&self) -> bool {
                true
            }

            pub const fn reinterpret_as_signed(&self) -> $SignedPeerT {
                type T = $SignedPeerT;
                T { bits: self.bits }
            }

            pub fn wrapping_add(self, rhs: $SelfT) -> $SelfT {
                let left = <$InnerT>::from(self);
                let right = <$InnerT>::from(rhs);
                let in_range_value: $InnerT = left.wrapping_add(right) & Self::VALUE_BITS;
                Self::try_from(in_range_value).unwrap()
            }

            pub fn wrapping_sub(self, rhs: $SelfT) -> $SelfT {
                let left = <$InnerT>::from(self);
                let right = <$InnerT>::from(rhs);
                let in_range_value = (left + Self::MODULUS).wrapping_sub(right) & Self::VALUE_BITS;
                Self::try_from(in_range_value).unwrap()
            }

            pub fn checked_add(self, rhs: $SelfT) -> Option<$SelfT> {
                let left = <$InnerT>::from(self);
                let right = <$InnerT>::from(rhs);
                match left.checked_add(right) {
                    Some(result) => Self::try_from(result).ok(),
                    None => None,
                }
            }

            pub fn checked_sub(self, rhs: $SelfT) -> Option<$SelfT> {
                let left = <$InnerT>::from(self);
                let right = <$InnerT>::from(rhs);
                match left.checked_sub(right) {
                    Some(result) => Self::try_from(result).ok(),
                    None => None,
                }
            }

            pub fn wrapping_mul(self, rhs: $SelfT) -> $SelfT {
                let left = <$InnerT>::from(self);
                let right = <$InnerT>::from(rhs);
                let in_range_value = left.wrapping_mul(right) & Self::VALUE_BITS;
                Self::try_from(in_range_value).unwrap()
            }

            pub fn checked_mul(self, rhs: $SelfT) -> Option<$SelfT> {
                let left = <$InnerT>::from(self);
                let right = <$InnerT>::from(rhs);
                match left.checked_mul(right) {
                    Some(result) => Self::try_from(result).ok(),
                    None => None,
                }
            }

            pub const fn abs(self) -> Self {
                self
            }

            pub const fn overflowing_abs(self) -> (Self, bool) {
                (self, false)
            }

            // We cannot call std::ops::And in a const because trait
            // methods cannot be const.  So we have this work-alike in
            // impl, since it can be called in a const context.
            pub const fn and(self, mask: $InnerT) -> Self {
                Self {
                    bits: self.bits & mask,
                }
            }

            // We cannot call std::ops::BitOr in a const because trait
            // methods cannot be const.  So we have this work-alike in
            // impl, since it can be called in a const context.
            pub const fn bitor(self, mask: $InnerT) -> Self {
                Self {
                    bits: self.bits | mask,
                }
            }
        }

        impl WordCommon for $SelfT {
            fn signum(&self) -> Sign {
                if self.is_zero() {
                    Sign::Zero
                } else if self.is_negative() {
                    Sign::Negative
                } else {
                    Sign::Positive
                }
            }
        }

        impl Default for $SelfT {
            fn default() -> Self {
                Self { bits: 0 }
            }
        }

        impl Display for $SelfT {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
                Octal::fmt(&self.bits, f)
            }
        }

        impl Octal for $SelfT {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
                Octal::fmt(&self.bits, f)
            }
        }

        impl Debug for $SelfT {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                write!(f, concat!(stringify!($SelfT), "{{bits: {:#o}}}"), self.bits)
            }
        }

        impl Hash for $SelfT {
            fn hash<H>(&self, state: &mut H)
            where
                H: Hasher,
            {
                self.bits.hash(state)
            }
        }

        impl<T> PartialEq<T> for $SelfT
        where
            T: TryInto<$SelfT> + Copy,
        {
            fn eq(&self, other: &T) -> bool {
                let converted: Result<$SelfT, _> = (*other).try_into();
                if let Ok(rhs) = converted {
                    match self.cmp(&rhs) {
                        Ordering::Equal => true,
                        _ => false,
                    }
                } else {
                    false
                }
            }
        }

        impl Eq for $SelfT {}

        impl PartialOrd<$SelfT> for $SelfT {
            fn partial_cmp(&self, other: &$SelfT) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl PartialOrd<u32> for $SelfT {
            fn partial_cmp(&self, other: &u32) -> Option<Ordering> {
                match <$SelfT>::try_from(*other) {
                    Ok(value) => Some(self.cmp(&value)),
                    // The error case tells us that `other` doesn't fit
                    // into $SelfT, so `other` must be greater.
                    Err(_) => Some(Ordering::Less),
                }
            }
        }

        impl PartialOrd<u64> for $SelfT {
            fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
                match <$SelfT>::try_from(*other) {
                    Ok(value) => Some(self.cmp(&value)),
                    // The error case tells us that `other` doesn't fit
                    // into $SelfT, so `other` must be greater.
                    Err(_) => Some(Ordering::Less),
                }
            }
        }

        impl Ord for $SelfT {
            fn cmp(&self, other: &$SelfT) -> Ordering {
                // We perform conversion here so that -0 == +0.
                let lhs = <$InnerT>::from(*self);
                let rhs = <$InnerT>::from(*other);
                lhs.cmp(&rhs)
            }
        }

        impl std::ops::Not for $SelfT {
            type Output = Self;
            fn not(self) -> Self {
                Self {
                    bits: (!self.bits) & Self::VALUE_BITS,
                }
            }
        }

        impl std::ops::BitAnd<$InnerT> for $SelfT {
            type Output = Self;
            fn bitand(self, mask: $InnerT) -> Self {
                Self {
                    bits: self.bits & mask,
                }
            }
        }

        impl std::ops::BitAnd<$SelfT> for $SelfT {
            type Output = Self;
            fn bitand(self, rhs: Self) -> Self {
                self.bitand(rhs.bits)
            }
        }

        impl std::ops::BitOr<$InnerT> for $SelfT {
            type Output = Self;
            fn bitor(self, mask: $InnerT) -> Self {
                Self {
                    bits: self.bits | mask,
                }
            }
        }

        impl std::ops::BitOr for $SelfT {
            type Output = Self;
            fn bitor(self, rhs: Self) -> Self {
                self.bitor(rhs.bits)
            }
        }

        impl std::ops::BitXor<$InnerT> for $SelfT {
            type Output = Self;
            fn bitxor(self, mask: $InnerT) -> Self {
                Self {
                    bits: self.bits ^ mask,
                }
            }
        }

        impl std::ops::BitXor for $SelfT {
            type Output = Self;
            fn bitxor(self, rhs: Self) -> Self {
                self.bitxor(rhs.bits)
            }
        }

        impl std::ops::Shr<$SelfT> for $SelfT {
            type Output = $SelfT;
            fn shr(self, rhs: Self) -> Self {
                let shift_by = rhs.bits % $BITS;
                // Compute a mask which has a 1 in the positions which
                // we're about to shift off the right of the word.
                let goners_mask: $InnerT = (1 << shift_by) - 1;

                // Preserve the bits we're about to shift off the
                // right-hand side.  Although shr() will shift them
                // back onto the most-significant end of the value,
                // these are in the wrong position in the word (as
                // self.bits, being wider than the value we are
                // representing, has bits which are ignored).
                let saved = (self.bits & goners_mask) << ($BITS - shift_by);

                let bits = (self.bits.shr(shift_by) | saved) & Self::VALUE_BITS;
                Self { bits }
            }
        }

        impl std::ops::Shr<u32> for $SelfT {
            type Output = $SelfT;
            fn shr(self, shift_by: u32) -> Self {
                // Compute a mask which has a 1 in the positions which
                // we're about to shift off the right of the word.
                let goners_mask: $InnerT = (1 << shift_by) - 1;

                // Preserve the bits we're about to shift off the
                // right-hand side.  Although shr() will shift them
                // back onto the most-significant end of the value,
                // these are in the wrong position in the word (as
                // self.bits, being wider than the value we are
                // representing, has bits which are ignored).
                let saved = (self.bits & goners_mask) << ($BITS - shift_by);

                let bits = (self.bits.shr(shift_by) | saved) & Self::VALUE_BITS;
                Self { bits }
            }
        }

        impl std::ops::Shl<$SelfT> for $SelfT {
            type Output = $SelfT;
            fn shl(self, shift_by: $SelfT) -> Self {
                // Clippy is suspicious of the use of the modulus
                // operation, but this lint check is really intended
                // to detect things like subtractions inside an add
                // operation.
                #[allow(clippy::suspicious_arithmetic_impl)]
                let shift: u32 = (shift_by.bits % $BITS) as u32;
                self.shl(shift)
            }
        }

        impl std::ops::Shl<u32> for $SelfT {
            type Output = $SelfT;
            fn shl(self, rhs: u32) -> Self {
                let shift_by = rhs % $BITS;
                // `goners_mask` has a 1 in the positions which we're
                // about to shift off the left of the word.
                let mask: $InnerT = (1 << shift_by) - 1; // correct size, wrong position
                let goners_mask: $InnerT = mask << ($BITS - shift_by); // correct size+pos

                // Preserve the bits we're about to shift off the
                // left-hand side.  Although shl() will shift bits
                // back onto the least-significant end of the value,
                // the bits shifted there are the previous top bits of
                // self.bits, but the top bits of self.bits aren't
                // part of the value of `self`, since `self.bits` has
                // a width greater than $BITS.
                let saved = (self.bits & goners_mask) >> ($BITS - shift_by);
                let bits = ((self.bits << shift_by) | saved) & Self::VALUE_BITS;
                Self { bits }
            }
        }
    };
}

/// `Unsigned5Bit` is used as a system configuration value; that is,
/// an index into F-memory.
#[derive(Clone, Copy, Serialize)]
pub struct Unsigned5Bit {
    pub(crate) bits: u8,
}

/// `Unsigned6Bit` is used as an X-register address. That is, the `j`
/// in `Xj`.
#[derive(Clone, Copy, Serialize)]
pub struct Unsigned6Bit {
    pub(crate) bits: u8,
}

/// `Unsigned9Bit` is the value of a "quarter" of the 36-bit TX-2
/// machine word.  A number of instructions - and in particular the
/// Exchange Unit - work on the quarters of a word.
#[derive(Clone, Copy, Serialize)]
pub struct Unsigned9Bit {
    pub(crate) bits: u16,
}

/// `Unsigned12Bit` is used as the _mode_ of a connected I/O device.
#[derive(Clone, Copy, Serialize)]
pub struct Unsigned12Bit {
    pub(crate) bits: u16,
}

/// `Unsigned18Bit` is the value of a "half" of the 36-bit TX-2
/// machine word.  We use this type to hold STUV-memory addresses,
/// among other things.  Physical memory addresses though are only 17
/// bits wide.  The remaining bit can be used to "mark" an address
/// either for tracing (when it's an instruction address) or for
/// deferred addressing (when it's an operand address).
#[derive(Clone, Copy, Serialize)]
pub struct Unsigned18Bit {
    pub(crate) bits: u32,
}

/// `Unsigned36Bit` is the basic machine word of the TX-2.  This is
/// the width of the registers in the Arithmetic Unit, and it is the
/// unit on which the Exchange Unit operates when performing memory
/// fetches or stores.  This is also the width of all instructions.
#[derive(Clone, Copy, Serialize)]
pub struct Unsigned36Bit {
    pub(crate) bits: u64,
}

unsigned_ones_complement_impl!(Unsigned5Bit, 5, u8, Signed5Bit);
unsigned_ones_complement_impl!(Unsigned6Bit, 6, u8, Signed6Bit);
unsigned_ones_complement_impl!(Unsigned9Bit, 9, u16, Signed9Bit);
unsigned_ones_complement_impl!(Unsigned12Bit, 12, u16, Signed12Bit);
unsigned_ones_complement_impl!(Unsigned18Bit, 18, u32, Signed18Bit);
unsigned_ones_complement_impl!(Unsigned36Bit, 36, u64, Signed36Bit);

////////////////////////////////////////////////////////////////////////
// Unsigned5Bit
////////////////////////////////////////////////////////////////////////

// all the things that always fit into Unsigned5Bit
// (there are none)
// all the things that Unsigned5Bit always fits into
from_self_to_native_type!(Unsigned5Bit, u8 i8 u16 i16 u32 i32 u64 i64 usize isize);
// all the things that Unsigned5Bit may not fit into
// (there are none)
// all the things that may not fit into Unsigned5Bit
try_from_native_type_to_self!(Unsigned5Bit, u8, i8 u8 u16 i16 u32 i32 u64 i64 usize isize);

////////////////////////////////////////////////////////////////////////
// Unsigned6Bit
////////////////////////////////////////////////////////////////////////

// all the things that always fit into Unsigned6Bit
// (there are none)
// all the things that Unsigned5Bit always fits into
from_self_to_native_type!(Unsigned6Bit, u8 i8 u16 i16 u32 i32 u64 i64 usize isize);
// all the things that Unsigned6Bit may not fit into
// (there are none)
// all the things that may not fit into Unsigned6Bit
try_from_native_type_to_self!(Unsigned6Bit, u8, i8 u8 u16 i16 u32 i32 u64 i64 usize isize);

impl From<Unsigned5Bit> for Unsigned6Bit {
    fn from(n: Unsigned5Bit) -> Self {
        Self { bits: n.bits }
    }
}

impl TryFrom<Unsigned18Bit> for Unsigned6Bit {
    type Error = ConversionFailed;
    fn try_from(n: Unsigned18Bit) -> Result<Self, ConversionFailed> {
        match u8::try_from(n.bits) {
            Ok(n) => {
                if n > Self::VALUE_BITS {
                    Err(ConversionFailed::TooLarge)
                } else {
                    Ok(Self { bits: n })
                }
            }
            Err(_) => Err(ConversionFailed::TooLarge),
        }
    }
}

////////////////////////////////////////////////////////////////////////
// Unsigned9Bit
////////////////////////////////////////////////////////////////////////

// all the things that always fit into Unsigned9Bit
from_native_type_to_self!(Unsigned9Bit, u8);
// all the things that Unsigned9Bit always fits into
from_self_to_native_type!(Unsigned9Bit, u16 i16 u32 i32 u64 i64 usize isize);
// all the things that Unsigned9Bit may not fit into
try_from_self_to_native_type!(Unsigned9Bit, u8 i8);
// all the things that may not fit into Unsigned9Bit
try_from_native_type_to_self!(Unsigned9Bit, u16, i8 u16 i16 u32 i32 u64 i64 usize isize);

impl From<Unsigned5Bit> for Unsigned9Bit {
    fn from(n: Unsigned5Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned6Bit> for Unsigned9Bit {
    fn from(n: Unsigned6Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

////////////////////////////////////////////////////////////////////////
// Unsigned12Bit
////////////////////////////////////////////////////////////////////////

// all the things that always fit into Unsigned12Bit
from_native_type_to_self!(Unsigned12Bit, u8);
// all the things that Unsigned12Bit always fits into
from_self_to_native_type!(Unsigned12Bit, u16 i16 u32 i32 u64 i64 usize isize);
// all the things that Unsigned12Bit may not fit into
try_from_self_to_native_type!(Unsigned12Bit, u8 i8);
// all the things that may not fit into Unsigned12Bit
try_from_native_type_to_self!(Unsigned12Bit, u16, i8 u16 i16 u32 i32 u64 i64);

impl From<Unsigned5Bit> for Unsigned12Bit {
    fn from(n: Unsigned5Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned6Bit> for Unsigned12Bit {
    fn from(n: Unsigned6Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned9Bit> for Unsigned12Bit {
    fn from(n: Unsigned9Bit) -> Self {
        Self { bits: n.bits }
    }
}

impl TryFrom<Unsigned18Bit> for Unsigned12Bit {
    type Error = ConversionFailed;
    fn try_from(n: Unsigned18Bit) -> Result<Self, ConversionFailed> {
        match u16::try_from(n.bits) {
            Ok(n) => {
                if n > Self::VALUE_BITS {
                    Err(ConversionFailed::TooLarge)
                } else {
                    Ok(Self { bits: n })
                }
            }
            Err(_) => Err(ConversionFailed::TooLarge),
        }
    }
}

////////////////////////////////////////////////////////////////////////
// Unsigned18Bit
////////////////////////////////////////////////////////////////////////

// all the things that always fit into Unsigned18Bit
from_native_type_to_self!(Unsigned18Bit, u8 u16);
// all the things that Unsigned18Bit always fits into
from_self_to_native_type!(Unsigned18Bit, u32 i32 u64 i64 usize isize);
// all the things Unsigned18Bit may not fit into
try_from_self_to_native_type!(Unsigned18Bit, u8 i8 u16 i16);
// all the things that may not fit into Unsigned18Bit
try_from_native_type_to_self!(Unsigned18Bit, u32, i8 i16 u32 i32 u64 i64);

impl From<Unsigned5Bit> for Unsigned18Bit {
    fn from(n: Unsigned5Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned9Bit> for Unsigned18Bit {
    fn from(n: Unsigned9Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl TryFrom<Unsigned36Bit> for Unsigned18Bit {
    type Error = ConversionFailed;
    fn try_from(n: Unsigned36Bit) -> Result<Self, ConversionFailed> {
        let (high, low) = split_halves(n);
        if high == Unsigned18Bit::ZERO {
            Ok(low)
        } else {
            Err(ConversionFailed::TooLarge)
        }
    }
}

impl TryFrom<usize> for Unsigned18Bit {
    type Error = ConversionFailed;
    fn try_from(n: usize) -> Result<Self, ConversionFailed> {
        match n.try_into() {
            Ok(bits) => {
                if bits > Unsigned18Bit::MAX.bits {
                    Err(ConversionFailed::TooLarge)
                } else {
                    Ok(Unsigned18Bit { bits })
                }
            }
            Err(_) => Err(ConversionFailed::TooLarge),
        }
    }
}

////////////////////////////////////////////////////////////////////////
// Unsigned36Bit
////////////////////////////////////////////////////////////////////////

// all the things that always fit into Unsigned36Bit
from_native_type_to_self!(Unsigned36Bit, u8 u16 u32);
// all the things that Unsigned36Bit always fits into
from_self_to_native_type!(Unsigned36Bit, u64 i64);
// all the things Unsigned36Bit may not fit into
try_from_self_to_native_type!(Unsigned36Bit, u8 i8 u16 i16 u32 i32);
// all the things that may not fit into Unsigned36Bit
try_from_native_type_to_self!(Unsigned36Bit, u64, i8 i16 i32 u64 i64);

impl TryFrom<Unsigned36Bit> for Unsigned6Bit {
    type Error = ConversionFailed;
    fn try_from(n: Unsigned36Bit) -> Result<Self, ConversionFailed> {
        match u8::try_from(n.bits) {
            Ok(n) => {
                if n > Self::VALUE_BITS {
                    Err(ConversionFailed::TooLarge)
                } else {
                    Ok(Self { bits: n })
                }
            }
            Err(_) => Err(ConversionFailed::TooLarge),
        }
    }
}

impl From<Unsigned5Bit> for Unsigned36Bit {
    fn from(n: Unsigned5Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned6Bit> for Unsigned36Bit {
    fn from(n: Unsigned6Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned9Bit> for Unsigned36Bit {
    fn from(n: Unsigned9Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned12Bit> for Unsigned36Bit {
    fn from(n: Unsigned12Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl From<Unsigned18Bit> for Unsigned36Bit {
    fn from(n: Unsigned18Bit) -> Self {
        Self {
            bits: n.bits.into(),
        }
    }
}

impl std::ops::BitAnd<Unsigned18Bit> for Unsigned36Bit {
    type Output = Unsigned18Bit;
    fn bitand(self, rhs: Unsigned18Bit) -> Unsigned18Bit {
        right_half(self).bitand(rhs)
    }
}

impl std::ops::BitAnd<Unsigned9Bit> for Unsigned36Bit {
    type Output = Unsigned9Bit;
    fn bitand(self, rhs: Unsigned9Bit) -> Unsigned9Bit {
        let (_q2, q1) = split_halfword(right_half(self));
        q1.bitand(rhs)
    }
}

impl std::ops::BitAnd<Unsigned6Bit> for Unsigned36Bit {
    type Output = Unsigned6Bit;
    fn bitand(self, rhs: Unsigned6Bit) -> Unsigned6Bit {
        Unsigned6Bit {
            bits: u8::try_from(self.bits & 0o77).expect("a six-bit quantity should be in-range")
                & rhs.bits,
        }
    }
}
