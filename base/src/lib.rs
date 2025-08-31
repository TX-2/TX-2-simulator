//! The `base` crate defines the TX2-related things which are useful
//! in both a simulator and other associated tools.  The idea is that
//! if you want to write an assembler, it would depend on the base
//! crate but would not need to depend on the simulator library
//! itself.
#![deny(unreachable_pub)]
#![deny(unsafe_code)]
#![deny(unused_crate_dependencies)]

pub mod bitselect;
pub mod charset;
pub mod collections;
pub mod instruction;
mod onescomplement;
pub mod prelude;
pub mod quarters;
pub mod splay;
pub mod subword;
mod types;
pub use onescomplement::error;
pub use onescomplement::unsigned::*;

#[macro_export]
macro_rules! u36 {
    ($n:expr_2021) => {
        $crate::prelude::Unsigned36Bit::new::<{ $n }>()
    };
}

#[macro_export]
macro_rules! u18 {
    ($n:expr_2021) => {
        $crate::prelude::Unsigned18Bit::new::<{ $n }>()
    };
}

#[macro_export]
macro_rules! u5 {
    ($n:expr_2021) => {
        $crate::prelude::Unsigned5Bit::new::<{ $n }>()
    };
}

#[macro_export]
macro_rules! u6 {
    ($n:expr_2021) => {
        $crate::prelude::Unsigned6Bit::new::<{ $n }>()
    };
}

#[macro_export]
macro_rules! u9 {
    ($n:expr_2021) => {
        $crate::prelude::Unsigned9Bit::new::<{ $n }>()
    };
}

#[test]
fn test_u36() {
    use prelude::Unsigned36Bit;
    let m: Unsigned36Bit = u36!(40_u64);
    let n: Unsigned36Bit = Unsigned36Bit::from(40_u32);
    assert_eq!(m, n);

    let p: Unsigned36Bit = u36!(1u64 << 34);
    let q: Unsigned36Bit =
        Unsigned36Bit::try_from(1u64 << 34).expect("test data should be in range");
    assert_eq!(p, q);
}

#[test]
fn test_u18() {
    use prelude::Unsigned18Bit;
    let p: Unsigned18Bit = u18!(1 << 17);
    let q: Unsigned18Bit =
        Unsigned18Bit::try_from(1u32 << 17).expect("test data should be in range");
    assert_eq!(p, q);
}

#[test]
fn test_u5() {
    assert_eq!(u5!(0o00), Unsigned5Bit::try_from(0o00_u8).unwrap());
    assert_eq!(u5!(0o01), Unsigned5Bit::try_from(0o01_u8).unwrap());
    assert_eq!(u5!(0o02), Unsigned5Bit::try_from(0o02_u8).unwrap());
    assert_eq!(u5!(0o03), Unsigned5Bit::try_from(0o03_u8).unwrap());
    assert_eq!(u5!(0o04), Unsigned5Bit::try_from(0o04_u8).unwrap());
    assert_eq!(u5!(0o04), Unsigned5Bit::try_from(0o04_u8).unwrap());
    assert_eq!(u5!(0o05), Unsigned5Bit::try_from(0o05_u8).unwrap());
    assert_eq!(u5!(0o06), Unsigned5Bit::try_from(0o06_u8).unwrap());
    assert_eq!(u5!(0o07), Unsigned5Bit::try_from(0o07_u8).unwrap());

    assert_eq!(u5!(0o10), Unsigned5Bit::try_from(0o10_u8).unwrap());
    assert_eq!(u5!(0o11), Unsigned5Bit::try_from(0o11_u8).unwrap());
    assert_eq!(u5!(0o12), Unsigned5Bit::try_from(0o12_u8).unwrap());
    assert_eq!(u5!(0o13), Unsigned5Bit::try_from(0o13_u8).unwrap());
    assert_eq!(u5!(0o14), Unsigned5Bit::try_from(0o14_u8).unwrap());
    assert_eq!(u5!(0o14), Unsigned5Bit::try_from(0o14_u8).unwrap());
    assert_eq!(u5!(0o15), Unsigned5Bit::try_from(0o15_u8).unwrap());
    assert_eq!(u5!(0o16), Unsigned5Bit::try_from(0o16_u8).unwrap());
    assert_eq!(u5!(0o17), Unsigned5Bit::try_from(0o17_u8).unwrap());

    assert_eq!(u5!(0o20), Unsigned5Bit::try_from(0o20_u8).unwrap());
    assert_eq!(u5!(0o21), Unsigned5Bit::try_from(0o21_u8).unwrap());
    assert_eq!(u5!(0o22), Unsigned5Bit::try_from(0o22_u8).unwrap());
    assert_eq!(u5!(0o23), Unsigned5Bit::try_from(0o23_u8).unwrap());
    assert_eq!(u5!(0o24), Unsigned5Bit::try_from(0o24_u8).unwrap());
    assert_eq!(u5!(0o24), Unsigned5Bit::try_from(0o24_u8).unwrap());
    assert_eq!(u5!(0o25), Unsigned5Bit::try_from(0o25_u8).unwrap());
    assert_eq!(u5!(0o26), Unsigned5Bit::try_from(0o26_u8).unwrap());
    assert_eq!(u5!(0o27), Unsigned5Bit::try_from(0o27_u8).unwrap());
}

#[test]
fn test_u6() {
    assert_eq!(u6!(0o00), Unsigned6Bit::try_from(0o00_u8).unwrap());
    assert_eq!(u6!(0o01), Unsigned6Bit::try_from(0o01_u8).unwrap());
    assert_eq!(u6!(0o27), Unsigned6Bit::try_from(0o27_u8).unwrap());
    assert_eq!(u6!(0o30), Unsigned6Bit::try_from(0o30_u8).unwrap());
    assert_eq!(u6!(0o70), Unsigned6Bit::try_from(0o70_u8).unwrap());
    assert_eq!(u6!(0o77), Unsigned6Bit::try_from(0o77_u8).unwrap());
}

#[test]
fn test_u9() {
    assert_eq!(u9!(0o750), Unsigned9Bit::try_from(0o750_u16).unwrap());
}
