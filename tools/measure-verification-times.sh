#! /bin/bash

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

# run verus
verus --crate-type=lib page-table/src/lib.rs --rlimit 50 --cfg feature=\"impl\" --no-auto-recommends-check --time-expanded --output-json --num-threads 32
