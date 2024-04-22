#!/bin/bash

####################################################################################################
#
# Script to obtain dependencies and build Verus.
#
####################################################################################################


set -eu

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
VERUS_ROOT="${REPOSITORY_ROOT}/verus"

echo "Repository root: ${REPOSITORY_ROOT}"
echo "Verus root:      ${VERUS_ROOT}"

if [ ! -d ${VERUS_ROOT}/source ]; then
    echo "Verus not initialized. Execute 'tools/setup-verus.sh' first."
    exit 1
fi

pushd ${VERUS_ROOT}/source > /dev/null

# check if we need to get Z3
if [ -f z3 ]; then
    echo "Z3 already exists"
else
    echo "Downloading Z3..."
    ./tools/get-z3.sh > /dev/null
fi

# activate & build vargo
source ../tools/activate

# build verus
env VERUS_Z3_PATH="$PWD/z3" vargo build --release

popd > /dev/null

# make verus binary accessible
if [[ -v GITHUB_PATH ]]; then
    echo "${VERUS_ROOT}/source/target-verus/release" >>"$GITHUB_PATH"
fi

echo "Verus ready."
