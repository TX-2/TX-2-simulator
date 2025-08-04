use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter, Octal};
use std::hash::{Hash, Hasher};

use super::error::ConversionFailed;
use super::unsigned::*;
use super::{Signum, WordCommon};

#[cfg(test)]
mod tests18;
#[cfg(test)]
mod tests36;
#[cfg(test)]
mod tests5;
#[cfg(test)]
mod tests9;

// This macro implements conversions from native types to Unsigned*Bit
// which are always possible (e.g. From<i8> for Signed9Bit).
macro_rules! from_native_type_to_self {
    ($SelfT:ty, $InnerT:ty, $SignedInnerT:ty, $($from:ty)*) => {
        $(
            impl From<$from> for $SelfT {
                fn from(n: $from) -> Self {
                    let v: $SignedInnerT = n.into();
                    Self {
                        bits: <$SelfT>::convert_to_ones_complement(v),
                    }
                }
            }
        )*
    }
}

macro_rules! try_from_native_type_to_self {
    ($SelfT:ty, $InnerT:ty, $SignedInnerT:ty, $($from:ty)*) => {
        $(
            impl TryFrom<$from> for $SelfT {
                type Error = ConversionFailed;
                fn try_from(n: $from) -> Result<$SelfT, ConversionFailed> {
                    match n.try_into() {
                        Err(_) if n > 0 => Err(ConversionFailed::TooLarge),
                        Err(_) => Err(ConversionFailed::TooSmall),
                        Ok(signed_value) => {
                            if signed_value > (Self::VALUE_BITS as $SignedInnerT) {
                                Err(ConversionFailed::TooLarge)
                            } else if signed_value < -(Self::VALUE_BITS as $SignedInnerT) {
                                Err(ConversionFailed::TooSmall)
                            } else {
                                Ok(Self {
                                    bits: <$SelfT>::convert_to_ones_complement(signed_value)
                                })
                            }
                        }
                    }
                }
            }
        )*
    }
}

// This macro implements conversions from Unsigned*Bit to native types
// which are always possible (e.g. From<Signed9Bit> for i16).
macro_rules! from_self_to_native_type {
    ($SelfT:ty, $InnerT:ty, $SignedInnerT:ty, $($to:ty)*) => {
        $(
            impl From<$SelfT> for $to {
                fn from(n: $SelfT) -> $to {
                    if n.is_zero() {
                        0 as Self
                    } else if n.is_negative() {
                        let inverted_bits = (!n.bits) & <$SelfT>::VALUE_BITS;
                        let absolute_value = inverted_bits as $SignedInnerT;
                        (-absolute_value) as Self
                    } else {
                        n.bits as Self
                    }
                }
            }
        )*
    }
}

// This macro implements conversions from Unsigned*Bit to native types
// which may not always be possible (e.g. From<Signed18Bit> for u16).
macro_rules! try_from_self_to_native_type {
    ($SelfT:ty, $InnerT:ty, $SignedInnerT:ty, $($to:ty)*) => {
        $(
            impl TryFrom<$SelfT> for $to {
                type Error = ConversionFailed;
                fn try_from(n: $SelfT) -> Result<$to, ConversionFailed> {
                    if n.is_zero() {
                        return Ok(0);
                    }
                    #[allow(unused_comparisons)]
                    if n.is_negative() {
                        let inverted_bits: $InnerT = (!n.bits) & <$SelfT>::VALUE_BITS;
                        let absolute_value: $SignedInnerT = inverted_bits as $SignedInnerT;
                        <$to>::try_from(-absolute_value)
                            .map_err(|_| ConversionFailed::TooSmall)
                    } else {
                        <$to>::try_from(n.bits)
                            .map_err(|_| ConversionFailed::TooLarge)
                    }
                }
            }
        )*
    }
}

macro_rules! signed_ones_complement_impl {
    ($SelfT:ty, $BITS:expr_2021, $InnerT:ty, $SignedInnerT:ty, $UnsignedPeerT:ty) => {
        impl $SelfT {
            const SIGN_BIT: $InnerT = 1 << ($BITS - 1);
            const VALUE_BITS: $InnerT = Self::SIGN_BIT - 1;
            const ALL_BITS: $InnerT = Self::SIGN_BIT | Self::VALUE_BITS;

            pub const MAX: Self = Self {
                bits: Self::VALUE_BITS,
            };

            pub const MIN: Self = Self {
                bits: Self::SIGN_BIT,
            };

            pub const ZERO: Self = Self { bits: 0 };
            pub const MINUS_ZERO: Self = Self {
                bits: Self::ALL_BITS,
            };
            pub const ONE: Self = Self { bits: 1 };

            pub const fn is_positive_zero(&self) -> bool {
                self.bits == 0
            }

            pub const fn is_negative_zero(&self) -> bool {
                self.bits == Self::ALL_BITS
            }

            pub const fn is_zero(&self) -> bool {
                self.is_positive_zero() || self.is_negative_zero()
            }

            pub const fn reinterpret_as_unsigned(&self) -> $UnsignedPeerT {
                type T = $UnsignedPeerT;
                T { bits: self.bits }
            }

            pub const fn is_negative(&self) -> bool {
                self.bits & Self::SIGN_BIT != 0 && !self.is_zero()
            }

            pub const fn is_positive(&self) -> bool {
                self.bits & Self::SIGN_BIT == 0 || self.is_zero()
            }

            pub const fn convert_to_ones_complement(signed: $SignedInnerT) -> $InnerT {
                if signed < 0 {
                    let absolute: $InnerT = (-signed) as $InnerT;
                    let bits: $InnerT = (!absolute) & Self::ALL_BITS;
                    bits
                } else {
                    signed as $InnerT
                }
            }

            pub fn checked_add(self, rhs: $SelfT) -> Option<$SelfT> {
                let left = <$SignedInnerT>::from(self);
                let right = <$SignedInnerT>::from(rhs);
                match left.checked_add(right) {
                    Some(result) => Self::try_from(result).ok(),
                    None => None,
                }
            }

            pub fn checked_sub(self, rhs: $SelfT) -> Option<$SelfT> {
                let left = <$SignedInnerT>::from(self);
                let right = <$SignedInnerT>::from(rhs);
                match left.checked_sub(right) {
                    Some(result) => Self::try_from(result).ok(),
                    None => None,
                }
            }

            pub fn wrapping_add(self, rhs: $SelfT) -> $SelfT {
                let left = <$SignedInnerT>::from(self);
                let right = <$SignedInnerT>::from(rhs);
                let (result, overflow) = left.overflowing_add(right);
                if overflow {
                    panic!(
                        "bug: $SignedInnerT is not wide enough to perform no-overflow arithmetic"
                    );
                }
                const MODULUS: $SignedInnerT = 1 << ($BITS - 1);
                Self {
                    bits: Self::convert_to_ones_complement(result % MODULUS),
                }
            }

            pub fn wrapping_sub(self, rhs: $SelfT) -> $SelfT {
                let left = <$SignedInnerT>::from(self);
                let right = <$SignedInnerT>::from(rhs);
                let (result, overflow) = left.overflowing_sub(right);
                if overflow {
                    panic!(
                        "bug: $SignedInnerT is not wide enough to perform no-overflow arithmetic"
                    );
                }
                const MODULUS: $SignedInnerT = 1 << ($BITS - 1);
                Self {
                    bits: Self::convert_to_ones_complement(result % MODULUS),
                }
            }

            pub fn checked_div(self, rhs: $SelfT) -> Option<$SelfT> {
                if rhs.is_zero() {
                    None
                } else {
                    let left = <$SignedInnerT>::from(self);
                    let right = <$SignedInnerT>::from(rhs);
                    match left.checked_div(right) {
                        Some(result) => Self::try_from(result).ok(),
                        None => unreachable!("division cannot overflow if rhs is nonzero"),
                    }
                }
            }

            pub const fn abs(self) -> Self {
                if self.is_zero() {
                    Self::ZERO
                } else if self.is_negative() {
                    Self {
                        bits: (!self.bits) & Self::VALUE_BITS,
                    }
                } else {
                    self
                }
            }

            pub const fn overflowing_abs(self) -> (Self, bool) {
                (self.abs(), false)
            }
        }

        impl Default for $SelfT {
            fn default() -> Self {
                Self { bits: 0 }
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
                if self.is_zero() {
                    // -0 should hash to the same value as +0.
                    let instead: $InnerT = 0;
                    instead.hash(state)
                } else {
                    self.bits.hash(state)
                }
            }
        }

        impl PartialEq for $SelfT {
            fn eq(&self, other: &$SelfT) -> bool {
                match self.cmp(other) {
                    Ordering::Equal => true,
                    _ => false,
                }
            }
        }

        impl PartialEq<$SignedInnerT> for $SelfT {
            fn eq(&self, other: &$SignedInnerT) -> bool {
                match self.partial_cmp(other) {
                    Some(Ordering::Equal) => true,
                    _ => false,
                }
            }
        }

        impl Eq for $SelfT {}

        impl PartialOrd for $SelfT {
            fn partial_cmp(&self, other: &$SelfT) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl PartialOrd<$SignedInnerT> for $SelfT {
            fn partial_cmp(&self, other: &$SignedInnerT) -> Option<Ordering> {
                let lhs = <$SignedInnerT>::from(*self);
                Some(lhs.cmp(other))
            }
        }

        impl Ord for $SelfT {
            fn cmp(&self, other: &$SelfT) -> Ordering {
                // We perform conversion here so that -0 == +0.
                let lhs = <$SignedInnerT>::from(*self);
                let rhs = <$SignedInnerT>::from(*other);
                lhs.cmp(&rhs)
            }
        }

        impl WordCommon for $SelfT {
            fn signum(&self) -> Signum {
                if self.is_zero() {
                    Signum::Zero
                } else if self.is_negative() {
                    Signum::Negative
                } else {
                    Signum::Positive
                }
            }
        }
    };
}

////////////////////////////////////////////////////////////////////////
// Signed5Bit
////////////////////////////////////////////////////////////////////////

/// Signed5Bit is somewhat special-purpose for instructions such as
/// JPX which use the instruction's configuration value as a 5-bit
/// signed integer.
#[derive(Clone, Copy)]
pub struct Signed5Bit {
    pub(crate) bits: u8,
}

signed_ones_complement_impl!(Signed5Bit, 5, u8, i8, Unsigned5Bit);

// from_native_type_to_self: nothing is narrow enough to always succeed.
try_from_native_type_to_self!(Signed5Bit, u8, i8, i8 u8 i16 u16 i32 u32 i64 u64 isize usize);

from_self_to_native_type!(Signed5Bit, u8, i8, i8 i16 i32 i64 isize);
try_from_self_to_native_type!(Signed5Bit, u8, i8, u8 u16 u32 u64 usize);

////////////////////////////////////////////////////////////////////////
// Signed6Bit
////////////////////////////////////////////////////////////////////////

/// Signed6Bit is somewhat special-purpose as the signed counterpart
/// for Unsigned6Bit, which is for handlng index register numbers and
/// sequence numbers.
#[derive(Clone, Copy)]
pub struct Signed6Bit {
    pub(crate) bits: u8,
}

signed_ones_complement_impl!(Signed6Bit, 6, u8, i8, Unsigned6Bit);

// from_native_type_to_self: nothing is narrow enough to always succeed.
try_from_native_type_to_self!(Signed6Bit, u8, i8, i8 u8 i16 u16 i32 u32 i64 u64 isize usize);

from_self_to_native_type!(Signed6Bit, u8, i8, i8 i16 i32 i64 isize);
try_from_self_to_native_type!(Signed6Bit, u8, i8, u8 u16 u32 u64 usize);

////////////////////////////////////////////////////////////////////////
// Signed9Bit
////////////////////////////////////////////////////////////////////////

/// Signed counterpart of [`Unsigned9Bit`].
#[derive(Clone, Copy)]
pub struct Signed9Bit {
    pub(crate) bits: u16,
}

signed_ones_complement_impl!(Signed9Bit, 9, u16, i16, Unsigned9Bit);

from_native_type_to_self!(Signed9Bit, u16, i16, i8 u8);
try_from_native_type_to_self!(Signed9Bit, u16, i16, i16 u16 i32 u32 i64 u64 isize usize);

from_self_to_native_type!(Signed9Bit, u16, i16, i16 i32 i64 isize);
try_from_self_to_native_type!(Signed9Bit, u16, i16, i8 u8 u16 u32 u64 usize);

////////////////////////////////////////////////////////////////////////
// Signed12Bit
////////////////////////////////////////////////////////////////////////

/// Signed counterpart of [`Unsigned12Bit`].
#[derive(Clone, Copy)]
pub struct Signed12Bit {
    pub(crate) bits: u16,
}

signed_ones_complement_impl!(Signed12Bit, 12, u16, i16, Unsigned12Bit);

from_native_type_to_self!(Signed12Bit, u16, i16, i8 u8);
try_from_native_type_to_self!(Signed12Bit, u16, i16, i16 u16 i32 u32 i64 u64 isize usize);

from_self_to_native_type!(Signed12Bit, u16, i16, i16 i32 i64 isize);
try_from_self_to_native_type!(Signed12Bit, u16, i16, i8 u8 u16 u32 u64);

////////////////////////////////////////////////////////////////////////
// Signed18Bit
////////////////////////////////////////////////////////////////////////

/// Signed counterpart of [`Unsigned18Bit`].
#[derive(Clone, Copy)]
pub struct Signed18Bit {
    pub(crate) bits: u32,
}

signed_ones_complement_impl!(Signed18Bit, 18, u32, i32, Unsigned18Bit);

from_native_type_to_self!(Signed18Bit, u32, i32, i8 u8 i16 u16);
try_from_native_type_to_self!(Signed18Bit, u32, i32, i32 u32 i64 u64 isize usize);

from_self_to_native_type!(Signed18Bit, u32, i32, i32 i64 isize);
try_from_self_to_native_type!(Signed18Bit, u32, i32, i8 u8 i16 u16 u32 u64 usize);

////////////////////////////////////////////////////////////////////////
// Signed36Bit
////////////////////////////////////////////////////////////////////////

/// Signed counterpart of [`Unsigned36Bit`].
#[derive(Clone, Copy)]
pub struct Signed36Bit {
    pub(crate) bits: u64,
}

signed_ones_complement_impl!(Signed36Bit, 36, u64, i64, Unsigned36Bit);

from_native_type_to_self!(Signed36Bit, u64, i64, i8 u8 i16 u16 i32 u32);
try_from_native_type_to_self!(Signed36Bit, u64, i64, i64 u64 isize usize);

from_self_to_native_type!(Signed36Bit, u64, i64, i64);
try_from_self_to_native_type!(Signed36Bit, u64, i64, i8 u8 i16 u16 i32 u32 u64 isize usize);

impl TryFrom<Unsigned18Bit> for Signed18Bit {
    type Error = ConversionFailed;
    fn try_from(n: Unsigned18Bit) -> Result<Self, ConversionFailed> {
        let val: i32 = i32::from(n);
        Signed18Bit::try_from(val)
    }
}

impl From<Signed5Bit> for Signed18Bit {
    fn from(n: Signed5Bit) -> Self {
        Signed18Bit::from(i8::from(n))
    }
}

impl From<Signed6Bit> for Signed18Bit {
    fn from(n: Signed6Bit) -> Self {
        Signed18Bit::from(i8::from(n))
    }
}

impl From<Signed9Bit> for Signed18Bit {
    fn from(n: Signed9Bit) -> Self {
        Signed18Bit::from(i16::from(n))
    }
}
