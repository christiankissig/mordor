#!/usr/bin/env bash
# The browser build's SMT solver (W4, #180; WS2, #176, route 2): Z3 built
# single-threaded with emscripten, linked into z3.js + z3.wasm that export the
# Z3 C API functions z3_shim.js calls.
#
#   [Z3_VERSION=x.y.z] wasm/z3/build.sh WORK [JOBS]
#
# WORK is a directory for the downloads and the build (about 3.5 GB: emsdk
# 1.7 GB, Z3's objects ~1.5 GB; not a tmpfs). Everything is fetched into it at
# fixed versions, and a second run reuses what is there. JOBS defaults to 4.
# The result is WORK/out/z3.{js,wasm} (16 MB, 5.3 MB gzipped), and
# WORK/out/VERSIONS. It needs git, cmake, ninja and python >= 3.10.
set -euo pipefail

WORK=$(realpath -m "$1")
JOBS=${2:-4}
HERE=$(cd "$(dirname "$0")" && pwd)
# The Z3 version: the native build's, so that both answer alike (opam's z3
# 5.1.0 here; CI's native build has 4.15.2, and sets Z3_VERSION to match).
Z3_TAG=z3-${Z3_VERSION:-5.1.0}
EMSDK_VERSION=6.0.13     # the version WS2 measured with; also in WORK/out/VERSIONS
PY=${PYTHON:-/usr/bin/python3}   # emsdk needs python >= 3.10

mkdir -p "$WORK" && cd "$WORK"

# 1. emsdk
if [ ! -d emsdk ]; then
  git clone -q --depth 1 https://github.com/emscripten-core/emsdk.git emsdk
fi
if [ ! -x emsdk/upstream/emscripten/emcc ]; then
  EMSDK_PYTHON=$PY emsdk/emsdk install "$EMSDK_VERSION"
  EMSDK_PYTHON=$PY emsdk/emsdk activate "$EMSDK_VERSION"
fi
export EMSDK_PYTHON=$PY EMSDK_QUIET=1
# shellcheck disable=SC1091
. "$WORK/emsdk/emsdk_env.sh"
export EMSDK_PYTHON=$PY

# 2. Z3 sources
if [ ! -d z3-src ]; then
  git clone -q --depth 1 --branch "$Z3_TAG" https://github.com/Z3Prover/z3 z3-src
fi
# A fix for Z3_POLLING_TIMER (see z3-polling-timer.patch and the README):
# without it, a timer's deadline outlives the timer, and a later check in the
# same context answers unknown ("max. resource limit exceeded").
if ! git -C z3-src apply --reverse --check "$HERE/z3-polling-timer.patch" 2>/dev/null; then
  git -C z3-src apply "$HERE/z3-polling-timer.patch"
fi

# 3. libz3.a: single-threaded, polling timer (no timer thread), no pthreads.
#    Native wasm exceptions (-fwasm-exceptions): Z3 throws C++ exceptions for
#    errors and cancellation; wasm exceptions are smaller and faster than
#    emscripten's JS-based ones and are supported by every current browser
#    and node >= 17.
FLAGS="-O3 -fwasm-exceptions"
emcmake cmake -S z3-src -B build-st -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_FLAGS="$FLAGS" -DCMAKE_CXX_FLAGS="$FLAGS" \
  -DZ3_SINGLE_THREADED=ON -DZ3_POLLING_TIMER=ON \
  -DZ3_BUILD_LIBZ3_SHARED=OFF -DZ3_BUILD_EXECUTABLE=OFF \
  -DZ3_BUILD_TEST_EXECUTABLES=OFF -DZ3_ENABLE_EXAMPLE_TARGETS=OFF \
  -DZ3_BUILD_DOCUMENTATION=OFF -DZ3_INCLUDE_GIT_HASH=OFF \
  -DZ3_USE_LIB_GMP=OFF
cmake --build build-st -j "$JOBS" --target libz3

# 4. link: no glue code, just the Z3 C API functions z3_shim.js calls
#    (its "// export:" lines). Z3 handles cross into JS as integers.
FNS=$(sed -n 's/^ *\/\/ export: //p' "$HERE/z3_shim.js" | tr -s ' \n' ',' | sed 's/,$//')
mkdir -p out
em++ -O3 -fwasm-exceptions build-st/libz3.a -o out/z3.js \
  -sMODULARIZE=1 -sEXPORT_NAME=initMordorZ3 \
  -sENVIRONMENT=web,worker,node \
  -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB -sINITIAL_MEMORY=64MB \
  -sSTACK_SIZE=16MB \
  -sEXPORTED_FUNCTIONS="$FNS,_malloc,_free" \
  -sEXPORTED_RUNTIME_METHODS=UTF8ToString,HEAPU8,HEAP32

{
  echo "z3 $Z3_TAG"
  echo "emcc $(emcc --version | head -1)"
} > out/VERSIONS
ls -l out
