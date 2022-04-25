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