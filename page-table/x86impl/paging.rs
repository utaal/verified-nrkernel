// https://github.com/gz/rust-x86/blob/6763f4192f2e7533e349a91d1e0745fc22aeca69/src/bits64/paging.rs

//! Description of the data-structures for IA-32e paging mode.

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
#[macro_use]
use crate::pervasive::*;

//use super::bitflags::*;
use core::convert::Into;

/// Align address downwards.
///
/// Returns the greatest x with alignment `align` so that x <= addr.
/// The alignment must be a power of 2.
//#[inline(always)]
fn align_down(addr: u64, align: u64) -> u64 {
    requires([
        align == HUGE_PAGE_SIZE as u64
            || align == LARGE_PAGE_SIZE as u64
            || align == BASE_PAGE_SIZE as u64,
        addr <= MAXPHYADDR,
    ]);
    // TODO: actual ensure clause we'd like to enforce:
    //ensures(|res: u64| {
    //    res <= addr
    //        && if align == BASE_PAGE_SIZE as u64 {
    //            res % BASE_PAGE_SIZE as u64 == 0
    //        } else if align == LARGE_PAGE_SIZE as u64 {
    //            res % LARGE_PAGE_SIZE as u64 == 0
    //        } else if align == HUGE_PAGE_SIZE as u64 {
    //            res % HUGE_PAGE_SIZE as u64 == 0
    //        } else {
    //            arbitrary()
    //        }
    //});

    addr & !(align - 1)
}

/// Align address upwards.
///
/// Returns the smallest x with alignment `align` so that x >= addr.
/// The alignment must be a power of 2.
//#[inline(always)]
fn align_up(addr: u64, align: u64) -> u64 {
    requires([
        align == HUGE_PAGE_SIZE as u64
            || align == LARGE_PAGE_SIZE as u64
            || align == BASE_PAGE_SIZE as u64,
        addr <= MAXPHYADDR,
    ]);
    ensures(|res: u64| res <= MAXPHYADDR);

    // TODO: actual ensure clause we'd like to enforce:
    //ensures(|res: u64| {
    //    res >= addr
    //        && res <= MAXPHYADDR
    //        && if align == BASE_PAGE_SIZE as u64 {
    //            res % BASE_PAGE_SIZE as u64 == 0
    //        } else if align == LARGE_PAGE_SIZE as u64 {
    //            res % LARGE_PAGE_SIZE as u64 == 0
    //        } else if align == HUGE_PAGE_SIZE as u64 {
    //            res % HUGE_PAGE_SIZE as u64 == 0
    //        } else {
    //            arbitrary()
    //        }
    //});

    let align_mask = align - 1;
    if addr & align_mask == 0 {
        addr
    } else {
        assume(addr < MAXPHYADDR); // TODO: otherwise addr & align_mask is 0
        assume(addr | align_mask < MAXPHYADDR); // TODO show max we can go is MAXPHYADDR-1
                                                // assert((MAXPHYADDR | (HUGE_PAGE_SIZE as u64 - 1)) < MAXPHYADDR);

        (addr | align_mask) + 1
    }
}

#[proof]
fn align_up_no_overflow() {}

/// A wrapper for a physical address.
#[repr(transparent)]
#[derive(Copy, Eq, PartialEq)]
pub struct PAddr(u64);

impl Clone for PAddr {
    fn clone(&self) -> Self {
        PAddr(self.0)
    }
}

#[proof]
fn paddr_is_valid(p: PAddr) {
    requires(p.inv());
    ensures(p.0 <= MAXPHYADDR);
}

impl PAddr {
    pub fn new(v: u64) -> Self {
        requires(v <= MAXPHYADDR);
        ensures(|res: PAddr| res.inv());
        PAddr(v)
    }

    #[spec]
    pub fn inv(self) -> bool {
        self.0 <= MAXPHYADDR
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

    pub fn is_zero(self) -> bool {
        requires([self.inv()]);
        self.0 == 0
    }

    /// Split `PAddr` into lower and higher 32-bits.
    pub fn split(&self) -> (u32, u32) {
        (self.0 as u32, (self.0 >> 32) as u32)
    }

    fn align_up(self, align: u64) -> Self {
        // TODO(as u64) what if this overflows?
        requires([
            self.inv(),
            align == HUGE_PAGE_SIZE as u64
                || align == LARGE_PAGE_SIZE as u64
                || align == BASE_PAGE_SIZE as u64,
        ]);
        ensures(|res: PAddr| self.inv());
        PAddr(align_up(self.0, align))
    }

    fn align_down(self, align: u64) -> Self {
        requires([
            self.inv(),
            align == HUGE_PAGE_SIZE as u64
                || align == LARGE_PAGE_SIZE as u64
                || align == BASE_PAGE_SIZE as u64,
        ]);
        ensures(|res: PAddr| self.inv());
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
        requires([self.inv()]);
        ensures(|res: PAddr| self.inv());
        self.align_down(BASE_PAGE_SIZE as u64)
    }

    /// Return address of nearest 2 MiB page (lower or equal than self).
    pub fn align_down_to_large_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: PAddr| self.inv());
        self.align_down(LARGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 1 GiB page (lower or equal than self).
    pub fn align_down_to_huge_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: PAddr| self.inv());
        self.align_down(HUGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 4 KiB page (higher or equal than self).
    pub fn align_up_to_base_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: PAddr| self.inv());
        self.align_up(BASE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 2 MiB page (higher or equal than self).
    pub fn align_up_to_large_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: PAddr| self.inv());
        self.align_up(LARGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 1 GiB page (higher or equal than self).
    pub fn align_up_to_huge_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: PAddr| self.inv());
        self.align_up(HUGE_PAGE_SIZE as u64)
    }

    /// Is this address aligned to a 4 KiB page?
    pub fn is_base_page_aligned(self) -> bool {
        requires([self.inv()]);
        self.align_down(BASE_PAGE_SIZE as u64).0 == self.0
    }

    /// Is this address aligned to a 2 MiB page?
    pub fn is_large_page_aligned(self) -> bool {
        requires([self.inv()]);
        self.align_down(LARGE_PAGE_SIZE as u64).0 == self.0
    }

    /// Is this address aligned to a 1 GiB page?
    pub fn is_huge_page_aligned(self) -> bool {
        requires([self.inv()]);
        self.align_down(HUGE_PAGE_SIZE as u64).0 == self.0
    }
}

#[allow(clippy::clippy::from_over_into)]
impl Into<u64> for PAddr {
    fn into(self) -> u64 {
        self.0
    }
}

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

pub const MAXPHYADDR: u64 = 0x10_0000_0000_0000; // 1<<MAXPHYADDR_BITS but detection is weird

// Mask to find the physical address of an entry in a page-table.
//const ADDRESS_MASK: u64 = ((1 <<= MAXPHYADDR) - 1) & !0xfff;

/// Page tables have 512 = 4096 / 64 entries.
pub const PAGE_SIZE_ENTRIES: usize = 512;
