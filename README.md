# Verified Page Table for NrOS

## Overview

This repo contains a verified implementation, (currently) single-threaded, of an OS' page table management code,
and proofs that it behaves according to a userspace process' expectations when combined with a model of the hardware's
memory management (memory translation) subsystem.

## Verification

Install Verus as described [in the official documentation](https://github.com/verus-lang/verus/blob/main/INSTALL.md).

```bash
# Replace $verus with the path to the verus binary
git clone git@github.com:utaal/verified-nrkernel.git
$verus ./verified-nrkernel/page-table/main.rs --cfg feature=\"impl\" --rlimit 30
```

Verification may take around a minute. You should see output similar to this:

```bash
[...]
verification results:: 288 verified, 0 errors
```

The `impl` feature flag can be omitted to check only the state machine modeling, not the
implementation.

## Structure

The page table code and corresponding proofs are in the `page-table` directory. We use the
convention that files and directories with `_t` (e.g. `definitions_t.rs` or `spec_t`) need to be
trusted, while those with `_u` do not need to be trusted. Trusted files contain for example
specifications and the axiomatized memory interface. Untrusted files include the implementation,
whose correctness is verified.

The directory structure is as follows:

- `main.rs`
- `definitions_t.rs` -- Definitions used in trusted files
- `definitions_u.rs` -- Definitions used *only* in untrusted files
- `extra.rs` -- Helper lemmas
- `impl_u` -- Implementations and proofs. The interface to the page table is in `l2_refinement.rs` (`impl impl_spec::InterfaceSpec ..`) and the main implementation is in `l2_impl.rs` (e.g. `fn map_frame`).
- `spec_t` -- Specifications. The high-level specification is in `hlspec.rs` and the hardware model in `hardware.rs`.
