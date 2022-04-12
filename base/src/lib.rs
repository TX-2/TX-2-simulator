//! The `base` crate defines the TX2-related things which are useful
//! in both a simulator and other associated tools.  The idea is that
//! if you want to write an assembler, it would depend on the base
//! crate but would not need to depend on the simulator library
//! itself.

mod onescomplement;
mod types;

pub mod charset;
pub mod instruction;
pub mod prelude;
pub mod subword;
pub use crate::onescomplement::unsigned::*;

#[macro_export]
macro_rules! u36 {
    ($n:expr) => {
        $crate::prelude::Unsigned36Bit::new::<{ $n }>()
    };
}

#[macro_export]
macro_rules! u18 {
    ($n:expr) => {
        $crate::prelude::Unsigned18Bit::new::<{ $n }>()
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
