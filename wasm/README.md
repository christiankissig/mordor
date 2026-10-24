# The browser build

MoRDor compiled with js_of_ocaml to run in a Web Worker (W3, #179). It links
`mordor_lib` with the browser platform in `platform/` instead of
`mordor.native`: one domain, no profiling, and **no SMT solver yet** (W4,
#180). So it parses any program, and interprets programs whose conditions
are decided without a solver. Everything else ends with an error that says so.

## Building

The two JavaScript executables are built only in the `browser` profile, so the
native build needs no js_of_ocaml:

```bash
opam install js_of_ocaml-compiler js_of_ocaml zarith_stubs_js
dune build --profile browser --build-dir _build-js ./wasm/worker.bc.js ./wasm/node_main.bc.js \
  ./wasm/test/hashes.bc.js
```

A separate build directory keeps the browser profile's build apart from the
native one. The worker is about 820 KB, 177 KB gzipped.

## The worker's protocol

The page posts a request: the JSON body that the web server's
`/api/<pipeline>/stream` endpoints take (`program`, `loop_semantics`, `steps`,
`memory_model`, `compare_models`), as a string, with the pipeline named in a
`pipeline` field: `parse`, `interpret`, `episodicity`, `assertions` or
`visualize`.

The worker posts back each JSON message of the answer, as a string, exactly
as the server sends them over SSE. Then it posts `null` to say the answer is
complete. The server and the worker run the same pipelines (`src/streaming.ml`).

## Testing

```bash
dune build ./wasm/test/session_native.exe ./wasm/test/hashes_native.exe
python3 -I wasm/test/compare.py _build/default/wasm/test/session_native.exe \
  _build-js/default/wasm/node_main.bc.js "$PWD/_build-js/default/wasm/worker.bc.js"
```

`compare.py` first checks that the browser build hashes as the native one does:
`wasm/test/hash_probe.ml` prints the hashes of fixed values, and the orders
they put sets in, and both builds must print the same. A hash that overflows
depends on the width of `int` (63 bits natively, 32 in JavaScript), and once
reordered the browser build's executions (#193); MoRDor's hashes keep their
low 30 bits.

Then it asks every pipeline about a fixed set of programs, natively (Z3)
and under node, and checks the browser build's answers:

- parse: identical for every program;
- interpret: identical for every program whose conditions need no solver;
- everything else: identical, or the native answer up to a message, followed
  by the no-solver error.

`node_main.bc.js` and the native `session_native.exe` read a request body on
stdin and print the answer as SSE frames. `wasm/test/worker_test.mjs` drives
the worker itself, through a shim that gives it a browser worker's globals.
