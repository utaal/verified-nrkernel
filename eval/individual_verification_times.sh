#!/usr/bin/env bash

# can't set these options because i don't know how to check for error code then
# set -euo pipefail
# set -x

RUST_VERIFY=/st/verus/verif/verus_main_new/source/tools/rust-verify.sh
PT_PATH=/st/verus/verified-nrkernel/page-table/
NUM_RUNS=1


# exclamation mark ignores return code for that command
modules=$(! "$RUST_VERIFY" --arch-word-bits 64 --rlimit 200 $PT_PATH/main.rs --verify-module xxxxx 2>&1 | grep '    -' | tr -s ' ' | cut -d ' ' -f 3 | awk '/prelude/,EOF { print $0 }' | tail -n+2)


for module in $modules; do
  functions=$(! "$RUST_VERIFY" --arch-word-bits 64 --rlimit 200 $PT_PATH/main.rs --verify-module "$module" --verify-function xxxxx 2>&1 | grep '    -' | tr -s ' ' | cut -d ' ' -f 3)

  for function in $functions; do
    output=$(strace -f -s99999 -e trace=execve "$RUST_VERIFY" --arch-word-bits 64 --rlimit 200 $PT_PATH/main.rs --time --verify-module "$module" --verify-function "$function" 2>&1)
    if [[ $? -gt 0 ]]; then
      echo "$module,$function,failed"
      continue
    fi
    # Check whether there even was a z3 query, if not we do not want to report 0ms
    if [[ "$output" =~ .*z3.* ]]; then
      time_acc1=0
      time_acc2=0
      time_acc3=0
      time_acc4=0
      time_acc5=0
      # rerun the query to avoid slowdown due to strace
      for i in $(seq 1 $NUM_RUNS); do
        output=$("$RUST_VERIFY" --arch-word-bits 64 --rlimit 200 $PT_PATH/main.rs --time --verify-module "$module" --verify-function "$function" 2>&1)
        time1=$(echo "$output" | grep total-time | tr -s ' ' | cut -d ' ' -f 2)
        time2=$(echo "$output" | grep rust-time | tr -s ' ' | cut -d ' ' -f 3)
        time3=$(echo "$output" | grep vir-time | tr -s ' ' | cut -d ' ' -f 3)
        time4=$(echo "$output" | grep air-time | tr -s ' ' | cut -d ' ' -f 3)
        time5=$(echo "$output" | grep smt-time | tr -s ' ' | cut -d ' ' -f 3)
        time_acc1=$((time_acc1+time1))
        time_acc2=$((time_acc2+time2))
        time_acc3=$((time_acc3+time3))
        time_acc4=$((time_acc4+time4))
        time_acc5=$((time_acc5+time5))
      done
      time_acc1=$((time_acc1/$NUM_RUNS))
      time_acc2=$((time_acc2/$NUM_RUNS))
      time_acc3=$((time_acc3/$NUM_RUNS))
      time_acc4=$((time_acc4/$NUM_RUNS))
      time_acc5=$((time_acc5/$NUM_RUNS))
      echo "$module,$function,total,$time_acc1"
      echo "$module,$function,rust,$time_acc2"
      echo "$module,$function,vir,$time_acc3"
      echo "$module,$function,air,$time_acc4"
      echo "$module,$function,smt,$time_acc5"
    else
      echo "$module,$function,X"
    fi
  done

done
