## verified nrkernel

How to use:

```bash
git clone git@github.com:utaal/verified-nrkernel.git
git clone git@github.com:secure-foundations/verus.git
# Follow steps in verus/README.md to install verus

cd verus/source
./tools/rust-verify.sh ../../verified-nrkernel/page-table/main.rs
```

You should see output similar to this:

```bash
Verifying root module
Verifying module memory_types
Verifying module spec
Verifying module lib
<... skipped lines ...>
Verification results:: verified: 15 errors: 0
```

### "Bugs" detected in page-table implementation :satisfied:

* Arithmetic overflow/underflow issues:

```log
error: possible arithmetic underflow/overflow
  --> ../../verified-nrkernel/page-table/x86impl/paging.rs:17:13
   |
17 |     addr & !(align - 1)
   |             ^^^^^^^^^^^
```

```log
error: possible arithmetic underflow/overflow
  --> ../../verified-nrkernel/page-table/x86impl/paging.rs:25:22
   |
25 |     let align_mask = align - 1;
   |                      ^^^^^^^^^

```log
error: possible arithmetic underflow/overflow
  --> ../../verified-nrkernel/page-table/x86impl/paging.rs:29:9
   |
29 |         (addr | align_mask) + 1
   |         ^^^^^^^^^^^^^^^^^^^^^^^
```

* Not really a bug since it should statically infer overflow

```log
error: possible arithmetic underflow/overflow
   --> ../../verified-nrkernel/page-table/x86impl/paging.rs:356:27
    |
356 | const ADDRESS_MASK: u64 = ((1 << MAXPHYADDR) - 1) & !0xfff;
    |                           ^^^^^^^^^^^^^^^^^^^^^^^
```

* `fn kernel_vaddr_to_paddr(va: VAddr) -> PAddr` is buggy (doesn't check for PAddr max range)
