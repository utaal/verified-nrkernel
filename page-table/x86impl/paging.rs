// https://github.com/gz/rust-x86/blob/6763f4192f2e7533e349a91d1e0745fc22aeca69/src/bits64/paging.rs

//! Description of the data-structures for IA-32e paging mode.

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[macro_use]
use crate::pervasive::*;

//use super::bitflags::*;
use core::convert::{From, Into};
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops;

/// Align address downwards.
///
/// Returns the greatest x with alignment `align` so that x <= addr.
/// The alignment must be a power of 2.
//#[inline(always)]
fn align_down(addr: u64, align: u64) -> u64 {
    requires([align > 0]);

    addr & !(align - 1)
}

pub const fn next_multiple_of(addr: u64, rhs: u64) -> u64 {
    requires([rhs > 0, addr < MAXPHYADDR, rhs <= HUGE_PAGE_SIZE as u64]);

    let r = addr % rhs;
    let m = if (r > 0 && rhs < 0) || (r < 0 && rhs > 0) {
        r + rhs
    } else {
        r
    };

    if m == 0 {
        addr
    } else {
        addr + (rhs - m)
    }
}

#[proof]
fn next_multiple_of_no_overflow() {
    // blabla
}

/// Align address upwards.
///
/// Returns the smallest x with alignment `align` so that x >= addr.
/// The alignment must be a power of 2.
//#[inline(always)]
fn align_up(addr: u64, align: u64) -> u64 {
    requires([align > 0, align <= HUGE_PAGE_SIZE as u64, addr < MAXPHYADDR]);
    // DISABLED(verus panic): requires([align.is_power_of_two()]);

    let align_mask = align - 1;
    if addr & align_mask == 0 {
        addr
    } else {
        (addr | align_mask) + 1
    }
}

#[proof]
fn align_up_no_overflow() {
    // blabla
}

/// A wrapper for a physical address.
#[repr(transparent)]
#[derive(Copy, Eq, PartialEq)]
pub struct PAddr(pub u64); // well this probably shouldn't be pub

impl Clone for PAddr {
    fn clone(&self) -> Self {
        PAddr(self.0)
    }
}

#[proof]
fn paddr_is_valid(p: PAddr) {
    requires(p.inv());
    ensures(p.0 < MAXPHYADDR);
}

impl PAddr {
    pub fn new(v: u64) -> Self {
        requires(v < MAXPHYADDR);
        //QUESTION how to put ensure here? ensures(self.inv());
        PAddr(v)
    }

    // QUESTION: How to enforce this globally?
    #[spec]
    pub fn inv(self) -> bool {
        self.0 < MAXPHYADDR
    }

    /// Convert to `u64`
    pub fn as_u64(self) -> u64 {
        self.0
    }
    /// Convert to `usize`
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
    /// Physical Address zero.
    pub const fn zero() -> Self {
        PAddr(0)
    }

    // DISABLED(verus):
    // Is zero?
    //pub fn is_zero(self) -> bool {
    //    self == PAddr::zero()
    //}

    /// Split `PAddr` into lower and higher 32-bits.
    pub fn split(&self) -> (u32, u32) {
        (self.0 as u32, (self.0 >> 32) as u32)
    }

    // DISABLED(verus):
    //fn align_up<U>(self, align: U) -> Self
    //where
    //    U: Into<u64>,
    //{
    //    PAddr(align_up(self.0, align.into()))
    //}
    fn align_up(self, align: u64) -> Self {
        // TODO(as u64) what if this overflows?
        requires([align > 0, align < HUGE_PAGE_SIZE as u64]);
        PAddr(align_up(self.0, align))
    }

    // DISABLED(verus):
    //fn align_down<U>(self, align: U) -> Self
    //where
    //    U: Into<u64>,
    //{
    //    PAddr(align_down(self.0, align.into()))
    //}
    fn align_down(self, align: u64) -> Self {
        requires([align > 0]);
        PAddr(align_down(self.0, align))
    }

    /// Offset within the 4 KiB page.
    pub fn base_page_offset(self) -> u64 {
        self.0 & (BASE_PAGE_SIZE as u64 - 1)
    }

    /// Offset within the 2 MiB page.
    pub fn large_page_offset(self) -> u64 {
        self.0 & (LARGE_PAGE_SIZE as u64 - 1)
    }

    /// Offset within the 1 GiB page.
    pub fn huge_page_offset(self) -> u64 {
        self.0 & (HUGE_PAGE_SIZE as u64 - 1)
    }

    /// Return address of nearest 4 KiB page (lower or equal than self).
    pub fn align_down_to_base_page(self) -> Self {
        self.align_down(BASE_PAGE_SIZE as u64)
    }

    /// Return address of nearest 2 MiB page (lower or equal than self).
    pub fn align_down_to_large_page(self) -> Self {
        self.align_down(LARGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 1 GiB page (lower or equal than self).
    pub fn align_down_to_huge_page(self) -> Self {
        self.align_down(HUGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 4 KiB page (higher or equal than self).
    pub fn align_up_to_base_page(self) -> Self {
        self.align_up(BASE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 2 MiB page (higher or equal than self).
    pub fn align_up_to_large_page(self) -> Self {
        self.align_up(LARGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 1 GiB page (higher or equal than self).
    pub fn align_up_to_huge_page(self) -> Self {
        self.align_up(HUGE_PAGE_SIZE as u64)
    }

    // DISABLED(verus):
    /// Is this address aligned to a 4 KiB page?
    pub fn is_base_page_aligned(self) -> bool {
        self.align_down(BASE_PAGE_SIZE as u64).0 == self.0
    }

    // DISABLED(verus):
    /// Is this address aligned to a 2 MiB page?
    pub fn is_large_page_aligned(self) -> bool {
        self.align_down(LARGE_PAGE_SIZE as u64).0 == self.0
    }

    // DISABLED(verus):
    /// Is this address aligned to a 1 GiB page?
    pub fn is_huge_page_aligned(self) -> bool {
        self.align_down(HUGE_PAGE_SIZE as u64).0 == self.0
    }

    // DISABLED(verus): thread 'rustc' panicked at 'fn def for method in hir', rust_verify/src/rust_to_vir_expr.rs:1850:53
    // /// Is this address aligned to `align`?
    // ///
    // /// # Note
    // /// `align` must be a power of two.
    // pub fn is_aligned(self, align: u64) -> bool {
    // if !align.is_power_of_two() {
    // return false;
    // }
    // self.align_down(align) == self
    // }
}

// DISABLED(verus):
//impl From<u64> for PAddr {
//    fn from(num: u64) -> Self {
//        PAddr(num)
//    }
//}

// DISABLED(verus):
// impl From<usize> for PAddr {
//     fn from(num: usize) -> Self {
//         PAddr(num as u64)
//     }
// }
//
// DISABLED(verus):
// impl From<i32> for PAddr {
//     fn from(num: i32) -> Self {
//         PAddr(num as u64)
//     }
// }

#[allow(clippy::clippy::from_over_into)]
impl Into<u64> for PAddr {
    fn into(self) -> u64 {
        self.0
    }
}

// DISABLED(verus):
/*
#[allow(clippy::clippy::from_over_into)]
impl Into<usize> for PAddr {
    fn into(self) -> usize {
        self.0 as usize
    }
}
*/

/*
impl ops::Add for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn add(self, rhs: PAddr) -> Self::Output {
        PAddr(self.0 + rhs.0)
    }
}

impl ops::Add<u64> for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn add(self, rhs: u64) -> Self::Output {
        PAddr(self.0 + rhs)
    }
}

impl ops::Add<usize> for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn add(self, rhs: usize) -> Self::Output {
        PAddr(self.0 + rhs as u64)
    }
}
*/

impl ops::AddAssign for PAddr {
    // MODIFIED(verus+transitive)
    fn add_assign(&mut self, other: PAddr) {
        *self = PAddr(self.0 + other.0);
    }
}

// DISABLED(verus):
/*
impl ops::AddAssign<u64> for PAddr {
    // MODIFIED(verus+transitive)
    fn add_assign(&mut self, offset: u64) {
        *self = PAddr(self.0 + offset);
    }
}

impl ops::Sub for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn sub(self, rhs: PAddr) -> Self::Output {
        PAddr(self.0 - rhs.0)
    }
}
impl ops::Sub<u64> for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn sub(self, rhs: u64) -> Self::Output {
        PAddr(self.0 - rhs)
    }
}
impl ops::Sub<usize> for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn sub(self, rhs: usize) -> Self::Output {
        PAddr(self.0 - rhs as u64)
    }
}
impl ops::Rem for PAddr {
    type Output = PAddr;
    fn rem(self, rhs: PAddr) -> Self::Output {
        PAddr(self.0 % rhs.0)
    }
}
impl ops::Rem<u64> for PAddr {
    type Output = u64;
    fn rem(self, rhs: u64) -> Self::Output {
        self.0 % rhs
    }
}
impl ops::Rem<usize> for PAddr {
    type Output = u64;
    fn rem(self, rhs: usize) -> Self::Output {
        self.0 % (rhs as u64)
    }
}
impl ops::BitAnd for PAddr {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        PAddr(self.0 & rhs.0)
    }
}
impl ops::BitAnd<u64> for PAddr {
    type Output = u64;
    fn bitand(self, rhs: u64) -> Self::Output {
        Into::<u64>::into(self) & rhs
    }
}
impl ops::BitOr for PAddr {
    type Output = PAddr;
    fn bitor(self, rhs: PAddr) -> Self::Output {
        PAddr(self.0 | rhs.0)
    }
}
impl ops::BitOr<u64> for PAddr {
    type Output = u64;
    fn bitor(self, rhs: u64) -> Self::Output {
        self.0 | rhs
    }
}
impl ops::Shr<u64> for PAddr {
    type Output = u64;
    fn shr(self, rhs: u64) -> Self::Output {
        self.0 >> rhs
    }
}
impl fmt::Binary for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl fmt::Display for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Debug for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:#x}", self.0)
    }
}

impl fmt::LowerHex for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl fmt::Octal for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::UpperHex for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl fmt::Pointer for PAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use core::fmt::LowerHex;
        self.0.fmt(f)
    }
}

#[allow(clippy::clippy::derive_hash_xor_eq)]
impl Hash for PAddr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
*/

/// Log2 of base page size (12 bits).
pub const BASE_PAGE_SHIFT: usize = 12;

/// Size of a base page (4 KiB)
pub const BASE_PAGE_SIZE: usize = 4096;

/// Size of a large page (2 MiB)
pub const LARGE_PAGE_SIZE: usize = 1024 * 1024 * 2;

/// Size of a huge page (1 GiB)
pub const HUGE_PAGE_SIZE: usize = 1024 * 1024 * 1024;

/// Size of a region covered by a PML4 Entry (512 GiB)
#[cfg(target_arch = "x86_64")]
pub const PML4_SLOT_SIZE: usize = HUGE_PAGE_SIZE * 512;

/// Size of a cache-line
pub const CACHE_LINE_SIZE: usize = 64;

/// A type wrapping a base page with a 4 KiB buffer.
// DISABLED(verus):
//pub struct Page([u8; BASE_PAGE_SIZE]);

/// A type wrapping a large page with a 2 MiB buffer.
// DISABLED(verus):
//pub struct LargePage([u8; LARGE_PAGE_SIZE]);

/// A type wrapping a huge page with a 1 GiB buffer.
// DISABLED(verus):
//pub struct HugePage([u8; HUGE_PAGE_SIZE]);

/// MAXPHYADDR, which is at most 52; (use CPUID for finding system value).
pub const MAXPHYADDR_BITS: u64 = 52;

pub const MAXPHYADDR: u64 = 1 << MAXPHYADDR_BITS;

/// Mask to find the physical address of an entry in a page-table.
const ADDRESS_MASK: u64 = ((1 << MAXPHYADDR) - 1) & !0xfff;

#[proof]
fn address_mask_no_overunderflow() {
    // well why do I have to do this, it's const :(
}

/// Page tables have 512 = 4096 / 64 entries.
pub const PAGE_SIZE_ENTRIES: usize = 512;
