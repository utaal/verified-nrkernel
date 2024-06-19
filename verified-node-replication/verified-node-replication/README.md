# Verified Node Replication

This directory contains the verified node replication crate.

## Running Verification

To run verification, invoke Verus with the crate-type library on the `src/lib.rs` file:

```
$ verus --crate-type=lib src/lib.rs
```

You can also run verification with the `tools/verify-node-replication.sh` script in the root
directory of this repository.


## Building

You can build the crate using standard `cargo` commands.

```
$ cargo build [--release]
```


## Examples

The crate provides a few examples that demonstrate how we can use the verified node-replication
implementation. To build them, simply run:

```
$ cargo build --examples
```
