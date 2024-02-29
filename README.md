# Verified Node Replication in Verus

This repository contains the port of [IronSync's Node Replication proofs](https://github.com/secure-foundations/ironsync-osdi2023/tree/osdi2023-artifact/concurrency/node-replication) to [Verus](https://github.com/verus-lang/verus). The proof uses the
IronSync methodology that was ported to Verus. The toolchain will produce a library crate that
then can be used in rust programs.


## Verifying

Before you can verify the node-replication crate, you will need to obtain and build Verus.


## Usage

Simply add a dependency to `verus-nr` and Verus `builtin` to your `Cargo.toml`:

```toml
builtin = { path = "../../../verus/source/builtin" }
verus-nr = { path = "../../verus-nr" }
```

## License

See the LICENSE file.
