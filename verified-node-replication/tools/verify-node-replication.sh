#!/bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
VERUS_ROOT="${REPOSITORY_ROOT}/verus"
NR_ROOT="${REPOSITORY_ROOT}/verified-node-replication/src/lib.rs"

# check if verus has been initialized
if [[ ! -f "${VERUS_ROOT}/source/target-verus/release/verus" ]]; then
    echo 'Verus not initialized. Execute `tools/build-verus.sh` first.'
    exit 1
fi

# now verify the main osmosis model
pushd ${VERUS_ROOT}/source > /dev/null
echo "Verifying '${NR_ROOT}' ... "
./target-verus/release/verus --crate-type=lib $@ ${NR_ROOT}

popd > /dev/null
