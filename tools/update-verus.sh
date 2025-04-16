#! /bin/bash

# the verus repository url
VERUS_REPO="git@github.com:verus-lang/verus.git"

# where to clone the repository into
VERUS_DIR=".verus"

# the verus release to be used
VERUS_RELEASE="release/0.2025.04.12.04a69f9"

# check if verus repo exists, clone it if needed
if [ ! -d .verus ]; then
    git clone $VERUS_REPO $VERUS_DIR
fi

# cd into the verus directory
pushd $VERUS_DIR/source

# update repository
git fetch

# checkout the verus release we want
git checkout $VERUS_RELEASE

# update z3
./tools/get-z3.sh

# activate building
source ../tools/activate       # for bash and zsh

# we need to build for no std
vargo build --release --vstd-no-std --vstd-no-alloc

popd
