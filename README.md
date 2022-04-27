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

### Work arounds / unsupported features

* CRITICAL(rustc panic) thread 'rustc' panicked at 'The verifier does not yet support the following Rust feature: type Path(

```log
) ../../verified-nrkernel/page-table/x86impl/paging.rs:200:33: 200:45 (#0)', rust_verify/src/rust_to_vir_base.rs:396:13
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
warning: 1 warning emitted
```

```rustc
impl ops::Add for PAddr {
    type Output = PAddr;
    // MODIFIED(verus+transitive)
    fn add(self, rhs: PAddr) -> Self::Output {
        PAddr(self.0 + rhs.0)
    }
}
```

unfortunately there are many of those...

* CRITICAL(rustc panic) thread 'rustc' panicked at 'fn def for method in hir', rust_verify/src/rust_to_vir_expr.rs:1850:53

```rustc
 /// Is this address aligned to `align`?
 ///
 /// # Note
 /// `align` must be a power of two.
 pub fn is_aligned(self, align: u64) -> bool {
 if !align.is_power_of_two() {
 return false;
 }
 self.align_down(align) == self
 }
```

and

```rustc
impl Hash for PAddr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
```

* error: not supported: multiple definitions of same function

```log
   --> ../../verified-nrkernel/page-table/x86impl/paging.rs:192:5
    |
186 |     fn into(self) -> u64 {
    |     --------------------
...
192 |     fn into(self) -> usize {
    |     ^^^^^^^^^^^^^^^^^^^^^^
```

and

```log
228 |     fn add_assign(&mut self, other: PAddr) {
    |     --------------------------------------
...
234 |     fn add_assign(&mut self, offset: u64) {
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

* CRITICAL(prevents From<>, odd Into<> works?) error: The verifier does not yet support the following Rust feature: method without self

```log
   --> ../../verified-nrkernel/page-table/x86impl/paging.rs:164:5
    |
164 |     fn from(num: u64) -> Self {
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
```

* CRITICAL(dervice clone not working) error: let-pattern declaration must have an initializer

```log
  --> ../../verified-nrkernel/page-table/x86impl/paging.rs:36:18
   |
35 | #[derive(Copy, Clone, Eq, PartialEq)]
   |                ----- in this derive macro expansion
36 | pub struct PAddr(pub u64);
   |                  ^^^^^^^
```

Workaround: implement clone yourself

* error: The verifier does not yet support the following Rust feature: trait generic bounds

```log
[rust_verify/src/rust_to_vir.rs:350]
  --> ../../verified-nrkernel/page-table/x86impl/bitflags/bitflags_trait.rs:9:1
   |
9  | / pub trait BitFlags: ImplementedByBitFlagsMacro {
10 | |     type Bits;
11 | |     /// Returns an empty set of flags.
12 | |     fn empty() -> Self;
...  |
52 | |     fn set(&mut self, other: Self, value: bool);
53 | | }
   | |_^
```

* error: The verifier does not yet support the following Rust feature: unsupported item

```log
  --> ../../verified-nrkernel/page-table/x86impl/bitflags/bitflags_trait.rs:9:1
   |
9  | / pub trait BitFlags {
10 | |     type Bits;
11 | |     /// Returns an empty set of flags.
12 | |     fn empty() -> Self;
...  |
52 | |     fn set(&mut self, other: Self, value: bool);
53 | | }
   | |_^
```

* The verifier does not yet support the following Rust feature: ==/!= for non smt equality types

```log
[rust_verify/src/rust_to_vir_expr.rs:1452]
error: The verifier does not yet support the following Rust feature: ==/!= for non smt equality types
  --> ../../verified-nrkernel/page-table/x86impl/paging.rs:53:9
   |
53 |         self == PAddr::zero()
   |         ^^^^^^^^^^^^^^^^^^^^^

```

* The verifier does not yet support the following Rust feature: where clause

```log
error: The verifier does not yet support the following Rust feature: where clause
  --> ../../verified-nrkernel/page-table/x86impl/paging.rs:62:16
   |
62 |     fn align_up<U>(self, align: U) -> Self
   |                ^^^

error: aborting due to previous error
```

* error: The verifier does not yet support the following Rust feature: ==/!= for non smt equality types

```log
   --> ../../verified-nrkernel/page-table/x86impl/paging.rs:123:9
    |
123 |         self.align_down(BASE_PAGE_SIZE as u64) == self
    |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

* thread 'rustc' panicked at 'The verifier does not yet support the following Rust feature: type Array(

* error: The verifier does not yet support the following Rust feature: complex pattern

```log
   |
35 | #[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
   |                           --- in this derive macro expansion
36 | pub struct PAddr(pub u64);
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

* thread 'rustc' panicked at 'fn def for method in hir', rust_verify/src/rust_to_vir_expr.rs:1850:53
