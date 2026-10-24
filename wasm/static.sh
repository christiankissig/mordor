#!/usr/bin/env bash
# The static playground (W5, #181): the web UI (web/frontend/) with the
# browser build's worker instead of the server, as plain files.
#
#   wasm/static.sh Z3DIR OUT
#
# Z3DIR is wasm/z3/build.sh's out/. Build first, from the repository's root:
#
#   dune build ./web/export_static.exe
#   dune build --profile browser --build-dir _build-js ./wasm/worker.bc.js
#
# OUT gets index.html, manual.html and static/ from web/frontend/, with
# static/js/config.js naming the worker; mordor/ (wasm/dist.sh's files); and
# data/ (examples.json and tests.json, what the server's GET endpoints would
# serve). Any static file server will do: python3 -m http.server -d OUT.
set -euo pipefail
Z3DIR=$1 OUT=$2
ROOT=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$OUT/data"
cp -r "$ROOT/web/frontend/index.html" "$ROOT/web/frontend/manual.html" "$ROOT/web/frontend/static" "$OUT/"
chmod -R u+w "$OUT"
cat > "$OUT/static/js/config.js" <<'JS'
// The static build (wasm/static.sh): runs go to the browser build's worker.
window.MORDOR_CONFIG = { transport: 'worker', worker: 'mordor/worker_boot.js', data: 'data/' };
JS
"$ROOT/wasm/dist.sh" "$Z3DIR" "$OUT/mordor" > /dev/null
(cd "$ROOT" && ./_build/default/web/export_static.exe "$OUT/data")
du -sh "$OUT"
