/// The TX-2 uses 36-bit words.  We use Unsigned36Bit (defined in
/// onescomplement/unsigned.rs) to represent this.  As stored in
/// memory, there are two additional bits; these are implemented in
/// the CPU emulation, not here.
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Error, Formatter, Octal};
use std::hash::{Hash, Hasher};

#[cfg(test)]
use test_strategy::Arbitrary;

use super::onescomplement::error::ConversionFailed;
use super::onescomplement::signed::{Signed18Bit, Signed5Bit, Signed6Bit};
use super::onescomplement::unsigned::{Unsigned18Bit, Unsigned36Bit, Unsigned6Bit};
use super::onescomplement::{Signum, WordCommon};

/// The `IndexBy` trait implements address arithmetic (adding a signed
/// or unsigned value to an address).
///
/// On page 12-9, Volume 2 of the Technical Manual contains some
/// wording that I interpret to mean that address indexation arithmetic
/// wraps:
///
/// > While the sum of a base address in N₂,₁ and an index register in
/// > X is being formed betweek PK¹³ and PK²², the X Adder carry
/// > circuit is forced into a "set" condition.  This causes the sum
/// > of an 18 bit number and its 18 bit ONE's complement to be all
/// > ZEROS, rather than all ONES, if this sum should be formed.  The
/// > comuted address of an operand, deferred address, or next
/// > instruction then becomes the first register of the S Memory
/// > (address 0) rather than the last register of the V mMemory
/// > (address 377 777 (octal)), when, for example, the base address
/// > is 000 004 and the index is 777 773.  The logic for obtaining
/// > this result simply uses the PK¹³ᵝ 0.4 microsecond time level to
/// > set the X Adder carry circuit at the time that XAC would
/// > ordinarily have been used to clear it.
///
/// IndexBy is also used to increment the program counter, and on the
/// real TX2 this was done by a special circuit, not an adder.
/// Volume 2 of the Technical Manual (section 12-2.3 "P REGISTER
/// DRIVER LOGIC") states,
///
/// > Information can be transferred into the P register only from the
/// > X Adder.  In addition to this single transfer path, ther P
/// > register has a counter which can index the contents of the P
/// > register by one.  Note that count circuit does not alter the
/// > contents of P₂.₉
pub trait IndexBy<T> {
    fn index_by(&self, delta: T) -> Address;
}

/// An address has 17 normal value bits.  There are 18 bits for the
/// operand base address in the instruction word, but the topmost bit
/// signals a deferred (i.e. indirect) access, so we should never see
/// a memory access to an address with the 0o400_000 bit set.
///
/// The program counter can also have its top bit set.  This signals
/// that in the TX-2 hardware, the associated sequence should be
/// traced via Trap 42.
///
/// The Xj (index) registers form an 18-bit ring and are described on
/// page 3-68 of the User Handbook (section 3-3.1) as being signed
/// integers.  Yet P (which also holds an address) is described on the
/// same page as being a positive integer.  Therefore when performing
/// address arithmetic, we sometimes need to convert index register
/// values to the [`Signed18Bit`] type.
#[cfg_attr(test, derive(Arbitrary))]
#[derive(Clone, Copy)]
pub struct Address(Unsigned18Bit);

/// Placeholders (saved sequence instruction pointers in the index
/// registers) use bit 2.9 to indicate that sequence switches to
/// marked sequences should trap to sequence 42.  This means that the
/// mark bit needs to be retained in the program counter (P register)
/// so that the sequence is still "marked" after it has run.
pub const PLACEHOLDER_MARK_BIT: Unsigned18Bit = Unsigned18Bit::MAX.and(1u32 << 17); // bit 2.9

impl Address {
    pub const ZERO: Address = Address(Unsigned18Bit::ZERO);
    pub const MAX: Address = Address(Unsigned18Bit::MAX);

    pub const fn new(a: Unsigned18Bit) -> Address {
        Address(a)
    }

    /// Apply a bitmask to an address.  This could also be done via
    /// [`std::ops::BitAnd`], but trait implementations cannot be
    /// const.  Implementing this const methods allows us to form
    /// address constants at compile time with code like `Address::MAX
    /// & 0o03400`.
    pub const fn and(&self, mask: u32) -> Address {
        Address(self.0.and(mask)) // use same hack in Unsigned18Bit.
    }

    /// Extract the placeholder mark bit.
    pub fn mark_bit(&self) -> Unsigned18Bit {
        self.0 & PLACEHOLDER_MARK_BIT
    }

    /// The placeholder phrasing here comes from the "TRAP 42"
    /// features.  But the high bit in the operand address field in an
    /// instruction also marks the operand as using deferred
    /// addressing.  We should choose more neutral naming to avoid
    /// confusion.
    pub fn is_marked_placeholder(&self) -> bool {
        self.0 & PLACEHOLDER_MARK_BIT != 0_u16
    }

    /// Split an address into its bottom 17 bits (which corresponds to
    /// an actual memory register on the TX-2) and a "mark" bit.  The
    /// "mark" bit is variously used to signal deferred addressing
    /// when fetching operands, and to flag a sequence for tracing
    /// with trap 42 (in this context is is called a "placeholder mark
    /// bit").  The `split` method is the opposite of `join`.
    pub fn split(&self) -> (Unsigned18Bit, bool) {
        let without_mark: Unsigned18Bit = self.0 & !PLACEHOLDER_MARK_BIT;
        (without_mark, self.is_marked_placeholder())
    }

    /// Form an address from the bottom 17 bits of `addr` and a
    /// possilbe mark bit, `mark`.  If `mark` is false, the resulting
    /// address will have a zero-valued top bit, no matter what is in
    /// `addr`.  This is the opposite of `split`.
    pub fn join(addr: Unsigned18Bit, mark: bool) -> Address {
        let markbit: Unsigned18Bit = if mark {
            PLACEHOLDER_MARK_BIT
        } else {
            Unsigned18Bit::ZERO
        };
        let addr_without_mark: Unsigned18Bit = addr & !PLACEHOLDER_MARK_BIT;
        Address::from(markbit | addr_without_mark)
    }

    /// Computes the address following the current address.  Used,
    /// among other things, to increment the program counter.
    ///
    /// The simulator relies on the fact that (as in the hardware TX-2
    /// P register) this calculation will wrap from 0o377_777 to 0.
    pub fn successor(&self) -> Address {
        self.index_by(1_u8)
    }
}

impl From<Unsigned18Bit> for Address {
    fn from(a: Unsigned18Bit) -> Address {
        Address(a)
    }
}

impl From<Address> for Unsigned18Bit {
    fn from(addr: Address) -> Self {
        addr.0
    }
}

impl From<&Address> for Unsigned18Bit {
    fn from(addr: &Address) -> Self {
        addr.0
    }
}

impl From<&Address> for Unsigned36Bit {
    fn from(addr: &Address) -> Self {
        addr.0.into()
    }
}

impl From<Address> for Unsigned36Bit {
    fn from(addr: Address) -> Self {
        Unsigned36Bit::from(u32::from(addr))
    }
}

impl TryFrom<Unsigned36Bit> for Address {
    type Error = ConversionFailed;
    fn try_from(n: Unsigned36Bit) -> Result<Address, ConversionFailed> {
        let a: Unsigned18Bit = Unsigned18Bit::try_from(n)?;
        Ok(Address::from(a))
    }
}

impl IndexBy<u8> for Address {
    fn index_by(&self, index: u8) -> Address {
        let offset: Unsigned18Bit = index.into();
        let (address, mark) = self.split();
        Address::join(address.wrapping_add(offset) & !PLACEHOLDER_MARK_BIT, mark)
    }
}

fn unsigned_idx_impl(base: Address, delta: Unsigned18Bit) -> Result<Address, ConversionFailed> {
    let (current, mark) = base.split();
    let physical = current.wrapping_add(delta) & !PLACEHOLDER_MARK_BIT;
    Ok(Address::join(physical, mark))
}

fn signed_idx_impl(base: Address, delta: Signed18Bit) -> Result<Address, ConversionFailed> {
    let (current, mark) = base.split();
    let abs_delta: Unsigned18Bit = Unsigned18Bit::try_from(i32::from(delta.abs()))?;
    let physical = match delta.signum() {
        Signum::Zero => current,
        Signum::Positive => current.wrapping_add(abs_delta),
        Signum::Negative => current.wrapping_sub(abs_delta),
    } & !PLACEHOLDER_MARK_BIT;
    Ok(Address::join(physical, mark))
}

impl IndexBy<Signed5Bit> for Address {
    fn index_by(&self, delta: Signed5Bit) -> Address {
        signed_idx_impl(*self, Signed18Bit::from(delta)).unwrap()
    }
}

impl IndexBy<Signed6Bit> for Address {
    fn index_by(&self, delta: Signed6Bit) -> Address {
        signed_idx_impl(*self, Signed18Bit::from(delta)).unwrap()
    }
}

impl IndexBy<Signed18Bit> for Address {
    fn index_by(&self, delta: Signed18Bit) -> Address {
        signed_idx_impl(*self, delta).unwrap()
    }
}

impl IndexBy<Unsigned18Bit> for Address {
    fn index_by(&self, delta: Unsigned18Bit) -> Address {
        unsigned_idx_impl(*self, delta).unwrap()
    }
}

#[test]
fn index_by_5bit_quantity() {
    let start: Address = Address::from(Unsigned18Bit::from(0o4000_u16));
    let up: Signed5Bit = Signed5Bit::try_from(6_i8).unwrap();
    assert_eq!(
        start.index_by(up),
        Address::from(Unsigned18Bit::from(0o4006_u16))
    );

    let down: Signed5Bit = Signed5Bit::try_from(-4_i8).unwrap();
    assert_eq!(
        start.index_by(down),
        Address::from(Unsigned18Bit::from(0o3774_u16))
    );
}

impl TryFrom<u32> for Address {
    type Error = ConversionFailed;
    fn try_from(n: u32) -> Result<Address, ConversionFailed> {
        let value = Unsigned18Bit::try_from(n)?;
        Ok(Address::from(value))
    }
}

impl From<Address> for u32 {
    fn from(a: Address) -> u32 {
        u32::from(Unsigned18Bit::from(a))
    }
}

impl From<&Address> for u32 {
    fn from(a: &Address) -> u32 {
        u32::from(Unsigned18Bit::from(*a))
    }
}

impl Default for Address {
    fn default() -> Address {
        Address::from(Unsigned18Bit::from(0_u8))
    }
}

impl Display for Address {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        // Always display as octal.
        write!(f, "{:>08o}", self.0)
    }
}

impl Octal for Address {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let val = self.0;
        Octal::fmt(&val, f) // delegate to u32's implementation
    }
}

impl Debug for Address {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        // Always display as octal.
        write!(f, "{:>08o}", self.0)
    }
}

impl Ord for Address {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Address {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl Hash for Address {
    fn hash<H>(&self, h: &mut H)
    where
        H: Hasher,
    {
        self.0.hash(h)
    }
}

impl PartialEq<u32> for Address {
    fn eq(&self, other: &u32) -> bool {
        let v: u32 = self.0.into();
        v.eq(other)
    }
}
impl Eq for Address {}

pub type SequenceNumber = Unsigned6Bit;

#[test]
fn test_sequence_numnber() {
    const ZERO: SequenceNumber = SequenceNumber::ZERO;
    const ONE: SequenceNumber = SequenceNumber::ONE;

    // Verify that left-shift works (becauise we will need it when
    // handling flag raise/lower operations).
    assert_eq!(SequenceNumber::try_from(2_u8).unwrap(), ONE << ONE);

    // Verify that comparisons work (because we will need those when
    // figuring out whether a raised flag should cause a sequence
    // change).
    assert!(ONE > ZERO);
    assert!(ZERO < ONE);
    assert_eq!(ONE, ONE);
    assert_eq!(ZERO, ZERO);
    assert!(ONE != ZERO);
    assert!(ZERO != ONE);

    // When SequenceNumber is Unsigned6Bit, SequenceNumber::MAX should be 0o77.
    // assert_eq!(SequenceNumber::MAX, SequenceNumber::try_from(0o77_u8).unwrap());
}
