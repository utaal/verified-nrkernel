# Verified Node Replication in Verus

This repository contains the port of [IronSync's Node Replication proofs](https://github.com/secure-foundations/ironsync-osdi2023/tree/osdi2023-artifact/concurrency/node-replication) to [Verus](https://github.com/verus-lang/verus).
The proof uses the IronSync methodology that was ported to Verus. The toolchain will produce a library
crate that then can be used in Rust programs.


## License

See the LICENSE file.


## Preparation

**Obtaining Verus**

Before you can verify the node-replication crate, you will need to obtain and build Verus.
You can do that by initializing the Verus submodule with

```
$ bash tools/setup-verus.sh
```

Alternatively, you can initialize the Verus git submodule manually.


**Building Verus**

Then to build Verus, you can follow the instructions in the [Verus](https://github.com/verus-lang/verus)
repository. Alternatively, you can also build Verus using the provided script:

```
bash tools/build-verus.sh
```

The script obtains the dependencies and builds Verus.


## Verifying

To verify the node-replication crate, you can use the following command:

```
$ bash tools/verify-node-replication.sh
```

If you see an output like the following, then this means that verification was successful:

```
Verifying 'verified-node-replication/src/lib.rs' ...
verification results:: 254 verified, 0 errors
```


## Using

Simply add a dependency to `verified-node-replication` and Verus `builtin` to your `Cargo.toml`:

```toml
builtin = { path = "verus/source/builtin" }
verified-node-replication = { path = "verified-node-replication" }
```

Paths relative to the repository root. See the [examples](verified-node-replication/examples)
directory for some examples on how to use NR.


## Benchmarks

We implemented a few benchmarks that compare the verified implementation with upstream (unverified)
node replication, and IronSync's Dafny-based node replication. See the [benchmarks](benchmarks)
directory for more information.


