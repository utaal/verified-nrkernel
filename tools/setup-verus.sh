#!/bin/bash

set -eu

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
VERUS_ROOT="${REPOSITORY_ROOT}/verus"

echo "Repository root: ${REPOSITORY_ROOT}"
echo "Verus root:      ${VERUS_ROOT}"


# make sure we're in the repository root and initialize submodule
pushd ${REPOSITORY_ROOT} > /dev/null

git submodule init
git submodule update verus

popd > /dev/null

# go into the verus source directory and trigger toolchain installation
pushd ${VERUS_ROOT}/source > /dev/null

echo "Verus version:   $(git rev-parse HEAD)"

rustc --version

popd > /dev/null
