// https://github.com/gz/rust-x86/blob/6763f4192f2e7533e349a91d1e0745fc22aeca69/src/bits64/paging.rs

//! Description of the data-structures for IA-32e paging mode.

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
#[macro_use]
use crate::pervasive::*;
use seq::*;

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

/// A wrapper for a physical address.
#[repr(transparent)]
#[derive(Copy, Eq, PartialEq)]
pub struct PAddr(pub u64);

impl Clone for PAddr {
    fn clone(&self) -> Self {
        PAddr(self.0)
    }
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

/// MAXPHYADDR, which is at most 52; (use CPUID for finding system value).
pub const MAXPHYADDR_BITS: u64 = 52;

pub const MAXPHYADDR: u64 = 0x10_0000_0000_0000; // 1<<MAXPHYADDR_BITS but verus overflow detection is weird

pub const ADDRESS_MASK: u64 = 0xf_ffff_ffff_f000;

pub const MAXVADDR_BITS: u64 = 57; // with 5-level paging

pub const MAXVADDR: u64 = 0x200_0000_0000_0000; // 1 << MAXVADDR but verus overflow detection is weird

/// Page tables have 512 = 4096 / 64 entries.
pub const PAGE_SIZE_ENTRIES: usize = 512;

/// A wrapper for a virtual address.
#[repr(transparent)]
#[derive(Copy, Eq, PartialEq)]
pub struct VAddr(pub u64);

impl Clone for VAddr {
    fn clone(&self) -> Self {
        VAddr(self.0)
    }
}

impl VAddr {
    pub fn new(v: u64) -> Self {
        requires(v <= MAXPHYADDR);
        ensures(|res: VAddr| res.inv());
        VAddr(v)
    }

    #[spec]
    pub fn inv(self) -> bool {
        self.0 <= MAXPHYADDR // TODO: should be MAXVADDR (1<<57) but for now lets keep one align_up, align_down
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
        VAddr(0)
    }

    pub fn is_zero(self) -> bool {
        requires([self.inv()]);
        self.0 == 0
    }

    /// Split `VAddr` into lower and higher 32-bits.
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
        ensures(|res: VAddr| self.inv());
        VAddr(align_up(self.0, align))
    }

    fn align_down(self, align: u64) -> Self {
        requires([
            self.inv(),
            align == HUGE_PAGE_SIZE as u64
                || align == LARGE_PAGE_SIZE as u64
                || align == BASE_PAGE_SIZE as u64,
        ]);
        ensures(|res: VAddr| self.inv());
        VAddr(align_down(self.0, align))
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
        ensures(|res: VAddr| self.inv());
        self.align_down(BASE_PAGE_SIZE as u64)
    }

    /// Return address of nearest 2 MiB page (lower or equal than self).
    pub fn align_down_to_large_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: VAddr| self.inv());
        self.align_down(LARGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 1 GiB page (lower or equal than self).
    pub fn align_down_to_huge_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: VAddr| self.inv());
        self.align_down(HUGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 4 KiB page (higher or equal than self).
    pub fn align_up_to_base_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: VAddr| self.inv());
        self.align_up(BASE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 2 MiB page (higher or equal than self).
    pub fn align_up_to_large_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: VAddr| self.inv());
        self.align_up(LARGE_PAGE_SIZE as u64)
    }
    /// Return address of nearest 1 GiB page (higher or equal than self).
    pub fn align_up_to_huge_page(self) -> Self {
        requires([self.inv()]);
        ensures(|res: VAddr| self.inv());
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
impl Into<u64> for VAddr {
    fn into(self) -> u64 {
        self.0
    }
}

/// Given virtual address calculate corresponding entry in PML4.
#[cfg(target_arch = "x86_64")]
#[inline]
pub fn pml4_index(addr: VAddr) -> usize {
    //TODO: ensures(|res: usize| res < 512);
    ((addr.0 >> 39usize) & 0b111111111) as usize
}

/// Given virtual address calculate corresponding entry in PML5.
#[cfg(target_arch = "x86_64")]
#[inline]
pub fn pml5_index(addr: VAddr) -> usize {
    //TODO(question): if we make addr.0 `pub` we should prob. require addr.inv() here too, no?
    //TODO(verus+bitstuff): ensures(|res: usize| res < 512);
    ((addr.0 >> 48usize) & 0b111111111) as usize
}

/// Given virtual address calculate corresponding entry in PDPT.
#[inline]
pub fn pdpt_index(addr: VAddr) -> usize {
    //TODO(verus+bitstuff): ensures(|res: usize| res < 512);
    ((addr.0 >> 30usize) & 0b111111111) as usize
}

/// Given virtual address calculate corresponding entry in PD.
#[inline]
pub fn pd_index(addr: VAddr) -> usize {
    //TODO(verus+bitstuff): ensures(|res: usize| res < 512);
    ((addr.0 >> 21usize) & 0b111111111) as usize
}

/// Given virtual address calculate corresponding entry in PT.
#[inline]
pub fn pt_index(addr: VAddr) -> usize {
    //TODO(verus+bitstuff): ensures(|res: usize| res < 512);
    ((addr.0 >> 12usize) & 0b111111111) as usize
}

/// PML4 configuration bit description.
#[derive(Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PML4Flags {
    bits: u64,
}

impl Clone for PML4Flags {
    fn clone(&self) -> Self {
        PML4Flags { bits: self.bits }
    }
}

/// Present; must be 1 to reference a page-directory-pointer table
#[spec] // TODO: not spec
pub const PML4_P: u64 = 1 << 0;

/// Read/write; if 0, writes may not be allowed to the 512-GByte region
/// controlled by this entry (see Section 4.6)
#[spec] // TODO: not spec
pub const PML4_RW: u64 = 1 << 1;

/// User/supervisor; if 0, user-mode accesses are not allowed
/// to the 512-GByte region controlled by this entry.
#[spec] // TODO: not spec
pub const PML4_US: u64 = 1 << 2;

/// Page-level write-through; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PML4_PWT: u64 = 1 << 3;

/// Page-level cache disable; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PML4_PCD: u64 = 1 << 4;

/// Accessed; indicates whether this entry has been used for linear-address translation.
#[spec] // TODO: not spec
pub const PML4_A: u64 = 1 << 5;

/// If IA32_EFER.NXE = 1, execute-disable
/// If 1, instruction fetches are not allowed from the 512-GByte region.
#[spec] // TODO: not spec
pub const PML4_XD: u64 = 1 << 63;

impl PML4Flags {
    #[inline]
    pub const fn empty() -> Self {
        PML4Flags { bits: 0 }
    }

    /// Returns the set containing all flags.
    #[inline]
    pub const fn all() -> Self {
        PML4Flags {
            bits: (1 << 63) | 0b111111,
        }
    }
}

#[repr(transparent)]
#[derive(Copy, PartialEq, Eq, Structural)]
pub struct PML4Entry(pub u64);

impl Clone for PML4Entry {
    fn clone(&self) -> Self {
        PML4Entry(self.0)
    }
}

impl PML4Entry {
    pub fn new(pml4: PAddr, flags: u64) -> Self {
        PML4Entry(pml4.0 | flags)
    }

    pub fn address(self) -> PAddr {
        PAddr(self.0 & ADDRESS_MASK)
    }

    #[spec]
    pub fn is_present(self) -> bool {
        self.0 & PML4_P != 0
    }
}

// TODO(blocker?): No array support
//pub type PML4 = [PML4Entry; 512];

#[verifier(external_body)]
pub struct Directory<#[verifier(strictly_positive)] T> {
    storage: [T; 512]
}

impl<T: Clone+Copy> Directory<T> {
    fndecl!(pub fn view(&self) -> Seq<T>);

    #[spec]
    pub fn inv(&self) -> bool {
        self.view().len() == 512
    }

    #[verifier(external_body)]
    #[inline(always)]
    pub fn index(&self, i: usize) -> T {
        requires(i < self.view().len());
        ensures(|r: T| equal(r, self.view().index(i as int)));

        self.storage[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, v: T) {
        requires(i < old(self).view().len());
        ensures(equal(self.view(), old(self).view().update(i, v)));

        self.storage[i] = v;
    }
}

// pub type PML4 = Directory<PML4Entry>;
// Gerd: you're going to have to use the full type name for now: `Directory<PML4Entry>`

/// Present; must be 1 to reference a page-directory-pointer table
#[spec] // TODO: not spec
pub const PDPT_P: u64 = 1 << 0;

/// Read/write; if 0, writes may not be allowed to the 512-GByte region
/// controlled by this entry (see Section 4.6)
#[spec] // TODO: not spec
pub const PDPT_RW: u64 = 1 << 1;

/// User/supervisor; if 0, user-mode accesses are not allowed
/// to the 512-GByte region controlled by this entry.
#[spec] // TODO: not spec
pub const PDPT_US: u64 = 1 << 2;

/// Page-level write-through; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PDPT_PWT: u64 = 1 << 3;

/// Page-level cache disable; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PDPT_PCD: u64 = 1 << 4;

/// Accessed; indicates whether this entry has been used for linear-address translation.
#[spec] // TODO: not spec
pub const PDPT_A: u64 = 1 << 5;

/// If IA32_EFER.NXE = 1, execute-disable
/// If 1, instruction fetches are not allowed from the 512-GByte region.
#[spec] // TODO: not spec
pub const PDPT_XD: u64 = 1 << 63;

#[derive(Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PDPTFlags {
    bits: u64,
}

impl Clone for PDPTFlags {
    fn clone(&self) -> Self {
        PDPTFlags { bits: self.bits }
    }
}

#[repr(transparent)]
pub struct PDPTEntry(pub u64);

impl PDPTEntry {
    pub fn new(pdpt: PAddr, flags: u64) -> Self {
        PDPTEntry(pdpt.0 | flags)
    }

    pub fn address(self) -> PAddr {
        PAddr(self.0 & ADDRESS_MASK)
    }

    #[spec]
    pub fn is_present(self) -> bool {
        self.0 & PDPT_P != 0
    }
}

// TODO(blocker?): No array support
//pub type PDPT = [PDPTEntry; 512];

/// Present; must be 1 to reference a page-directory-pointer table
#[spec] // TODO: not spec
pub const PD_P: u64 = 1 << 0;

/// Read/write; if 0, writes may not be allowed to the 512-GByte region
/// controlled by this entry (see Section 4.6)
#[spec] // TODO: not spec
pub const PD_RW: u64 = 1 << 1;

/// User/supervisor; if 0, user-mode accesses are not allowed
/// to the 512-GByte region controlled by this entry.
#[spec] // TODO: not spec
pub const PD_US: u64 = 1 << 2;

/// Page-level write-through; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PD_PWT: u64 = 1 << 3;

/// Page-level cache disable; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PD_PCD: u64 = 1 << 4;

/// Accessed; indicates whether this entry has been used for linear-address translation.
#[spec] // TODO: not spec
pub const PD_A: u64 = 1 << 5;

/// If IA32_EFER.NXE = 1, execute-disable
/// If 1, instruction fetches are not allowed from the 512-GByte region.
#[spec] // TODO: not spec
pub const PD_XD: u64 = 1 << 63;

#[derive(Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PDFlags {
    bits: u64,
}

impl Clone for PDFlags {
    fn clone(&self) -> Self {
        PDFlags { bits: self.bits }
    }
}

#[repr(transparent)]
pub struct PDEntry(pub u64);

impl PDEntry {
    pub fn new(pd: PAddr, flags: u64) -> Self {
        PDEntry(pd.0 | flags)
    }

    pub fn address(self) -> PAddr {
        PAddr(self.0 & ADDRESS_MASK)
    }

    #[spec]
    pub fn is_present(self) -> bool {
        self.0 & PD_P != 0
    }
}

// TODO(blocker?): No array support
//pub type PD = [PDEntry; 512];

/// Present; must be 1 to reference a page-directory-pointer table
#[spec] // TODO: not spec
pub const PT_P: u64 = 1 << 0;

/// Read/write; if 0, writes may not be allowed to the 512-GByte region
/// controlled by this entry (see Section 4.6)
#[spec] // TODO: not spec
pub const PT_RW: u64 = 1 << 1;

/// User/supervisor; if 0, user-mode accesses are not allowed
/// to the 512-GByte region controlled by this entry.
#[spec] // TODO: not spec
pub const PT_US: u64 = 1 << 2;

/// Page-level write-through; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PT_PWT: u64 = 1 << 3;

/// Page-level cache disable; indirectly determines the memory type used to
/// access the page-directory-pointer table referenced by this entry.
#[spec] // TODO: not spec
pub const PT_PCD: u64 = 1 << 4;

/// Accessed; indicates whether this entry has been used for linear-address translation.
#[spec] // TODO: not spec
pub const PT_A: u64 = 1 << 5;

/// If IA32_EFER.NXE = 1, execute-disable
/// If 1, instruction fetches are not allowed from the 512-GByte region.
#[spec] // TODO: not spec
pub const PT_XD: u64 = 1 << 63;

#[derive(Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PTFlags {
    bits: u64,
}

impl Clone for PTFlags {
    fn clone(&self) -> Self {
        PTFlags { bits: self.bits }
    }
}

#[repr(transparent)]
pub struct PTEntry(pub u64);

impl PTEntry {
    pub fn new(pt: PAddr, flags: u64) -> Self {
        PTEntry(pt.0 | flags)
    }

    pub fn address(self) -> PAddr {
        PAddr(self.0 & ADDRESS_MASK)
    }

    #[spec]
    pub fn is_present(self) -> bool {
        self.0 & PT_P != 0
    }
}

// TODO(blocker?): No array support
//pub type PT = [PTEntry; 512];
