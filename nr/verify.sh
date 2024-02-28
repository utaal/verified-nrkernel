#!/bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
VERUS_ROOT="${REPOSITORY_ROOT}/verus"
NR_ROOT="${REPOSITORY_ROOT}/nr/verus-nr"

# check if verus has been initialized
if [[ ! -f "${VERUS_ROOT}/source/target-verus/release/verus" ]]; then
    echo "Verus not initialized. Updating..."
    git submodule init
    git submodule update

    pushd ${VERUS_ROOT}/source > /dev/null
    ./tools/get-z3.sh
    source ../tools/activate
    vargo build --release
    popd > /dev/null
fi

# now verify the main osmosis model
pushd ${VERUS_ROOT}/source > /dev/null
echo "Verifying '${OSMOSIS_ROOT}/src/main.rs' ... "
 ./target-verus/release/verus --crate-type=lib $@ ${NR_ROOT}/src/lib.rs
#./target-verus/release/verus --crate-type=lib $@ ${REPOSITORY_ROOT}/nr/test.rs
popd > /dev/null
