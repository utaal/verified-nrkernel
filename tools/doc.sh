#! /bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)

# where to clone the repository into
VERUS_DIR="${REPOSITORY_ROOT}/.verus"

OPEN=

for i in "$@"; do
  case $i in
    --open)
      OPEN=--open
      shift
      ;;
    -*|--*)
      echo "Unknown option $i"
      exit 1
      ;;
    *)
      ;;
  esac
done

# check if verus repo exists, clone it if needed
if [ ! -d "${VERUS_DIR}" ]; then
    "${REPOSITORY_ROOT}"/tools/update-verus.sh
fi

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
else
    echo "unsupported OS"
    exit 1
fi


# disable the default rustdoc generation
# pushd "${REPOSITORY_ROOT}/allocator"
# cargo doc --no-deps --document-private-items
# popd

source ${VERUS_DIR}/tools/activate

pushd ${VERUS_DIR}/source

if [ ! -f ${VERUS_DIR}/source/target/debug/verusdoc ]; then
  echo "Building verusdoc..."
  vargo build -p verusdoc
fi

if [ ! -f ${VERUS_DIR}/source/target-verus/debug/libvstd.rlib ]; then
  echo "Building vstd..."
  vargo build --vstd-no-verify
fi

popd

echo "Running rustdoc..."
RUSTC_BOOTSTRAP=1 eval ""VERUSDOC=1 VERUS_Z3_PATH="$(pwd)/z3" rustdoc \
  --extern builtin=${VERUS_DIR}/source/target-verus/debug/libbuiltin.rlib \
  --extern builtin_macros=${VERUS_DIR}/source/target-verus/debug/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros=${VERUS_DIR}/source/target-verus/debug/libstate_machines_macros.$DYN_LIB_EXT \
  --extern vstd=${VERUS_DIR}/source/target-verus/debug/libvstd.rlib \
  --edition=2021 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature=\"linux\"' \
  --document-private-items \
  -Zcrate-attr=feature\\\(stmt_expr_attributes\\\) \
  -Zcrate-attr=feature\\\(negative_impls\\\) \
  -Zcrate-attr=feature\\\(register_tool\\\) \
  -Zcrate-attr=feature\\\(rustc_attrs\\\) \
  -Zcrate-attr=feature\\\(unboxed_closures\\\) \
  -Zcrate-attr=register_tool\\\(verus\\\) \
  -Zcrate-attr=register_tool\\\(verifier\\\) \
  -Zcrate-attr=register_tool\\\(verusfmt\\\) \
  -Zcrate-attr=allow\\\(internal_features\\\) \
  -Zcrate-attr=allow\\\(unused_braces\\\) \
  -Zproc-macro-backtrace \
  ${REPOSITORY_ROOT}/page-table/src/lib.rs""


echo "Running post-processor..."
${VERUS_DIR}/source/target/debug/verusdoc --help

if [ "$OPEN" = '--open' ]; then
  echo "Opening documentation..."
  open "${REPOSITORY_ROOT}"/doc/lib/index.html
fi

