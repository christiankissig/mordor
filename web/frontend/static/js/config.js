// Where the frontend sends its runs (W5, #181; see transport.js). Served by
// mordor-web as it is here; the static build (wasm/static.sh) replaces this
// file with one that names the Web Worker instead.
window.MORDOR_CONFIG = { transport: 'server' };
