#!/usr/bin/env bash
# The browser build's files, together in one directory a page can load the
# worker from (W4, #180):
#
#   wasm/dist.sh Z3DIR OUT
#
# Z3DIR is wasm/z3/build.sh's out/; worker.bc.js must be built first:
#
#   dune build --profile browser --build-dir _build-js ./wasm/worker.bc.js
#
# OUT gets worker_boot.js (what a page starts: new Worker('worker_boot.js')),
# z3_shim.js, z3.js, z3.wasm and worker.bc.js.
set -euo pipefail
Z3DIR=$1 OUT=$2
HERE=$(cd "$(dirname "$0")" && pwd)
WORKER=$HERE/../_build-js/default/wasm/worker.bc.js
[ -f "$WORKER" ] || { echo "dist.sh: no $WORKER; build it first" >&2; exit 1; }
mkdir -p "$OUT"
cp "$HERE/worker_boot.js" "$HERE/z3/z3_shim.js" "$Z3DIR/z3.js" "$Z3DIR/z3.wasm" "$WORKER" "$OUT/"
chmod u+w "$OUT"/*
ls -l "$OUT"
