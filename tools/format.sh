#!/bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
NR_ROOT="${REPOSITORY_ROOT}/verified-node-replication/src/"

# check if verusfmt is installed
if ! command -v verusfmt &> /dev/null
then
    cargo install verusfmt
fi

pushd ${NR_ROOT} > /dev/null
find . -type f -name '*.rs' -exec verusfmt {} \;
popd > /dev/null
