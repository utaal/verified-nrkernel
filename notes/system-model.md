* [ ] Question: is the resolve operation used by NrOS or processes?

    - dereference user-space buffer inside the kernel
    - kernel resolving a mapping in a NUMA node that hasn't caught up, to catch it up
    - system-call `identify`: give it a vaddr, returns the paddr and access rights
        need to know the paddr of the buffer for DMA
        may want to set up IOMMU instead to match the device address space with process address space

* [ ] How is the first page table set up? Do we need to worry about that?

    - initial -- bootloader sets up identity mapping of physical memory
    -                               second identity mapping offseted by KERNEL_BASE
    - a process, make a new address space
        first identity mapping gone, second identity mapping offseted by KERNEL_BASE patched in
                                     a few entries in the PML4 table
    - physical identity mappings are immutable, except for dynamic memory allocation in the kernel
      address space -- create mapping above the identity mappings
    * consider sanitizing the initial mappings and abort if it doesn't satisfy the invariant

--- 

* [ ] Use a single type for the entries
