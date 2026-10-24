# The browser build

MoRDor compiled with js_of_ocaml to run in a Web Worker (W3, #179), with Z3
compiled to wasm as its SMT solver (W4, #180). It links `mordor_lib` with the
browser platform in `platform/` instead of `mordor.native`: Z3 through
`z3/z3_shim.js`, one domain, no profiling. It answers every pipeline the web
server does, with the same messages, byte for byte.

What differs from native:

- **One thread.** A Web Worker runs one domain, and Z3 is built without
  threads.
- **Slower.** A median of 9 times as long as native on the litmus tests,
  which take well under a second natively, so mostly starting up; 1.2 to 1.5
  times on seqlock-1. See [Timing](#timing).
- **Memory.** Z3's wasm heap is capped at 4 GB, and the shim keeps at most 64
  Z3 solvers alive (MoRDor drops solvers rather than closing them, and the
  JavaScript garbage collector cannot see Z3's memory). Programs that need
  more than a few GB natively, such as rcu-2 at step counter 2, do not fit.
- **No files.** The worker answers requests; there is no CLI and no file
  output.

## Building

### Z3

```bash
wasm/z3/build.sh WORK [JOBS]
```

fetches emsdk and Z3 5.1.0 (the version MoRDor's native build uses) at fixed
versions into `WORK` (about 3.5 GB; not a tmpfs), applies
`z3/z3-polling-timer.patch`, builds Z3 single-threaded and links
`WORK/out/z3.js` and `WORK/out/z3.wasm` (16 MB, 5.3 MB gzipped). It takes
about 20 minutes at 4 jobs, and a second run reuses what it can. It needs git,
cmake, ninja and python >= 3.10.

The patch fixes Z3's polling timer, which a build without threads uses: without
it, a timer's deadline outlives the timer, and a later check in the same
context answers `unknown`. MoRDor sets no timers itself, but the W1 corpus
checks do.

### MoRDor

The JavaScript executables, and the browser platform, are built only in the
`browser` profile, so the native build needs no js_of_ocaml:

```bash
opam install js_of_ocaml-compiler js_of_ocaml zarith_stubs_js
dune build --profile browser --build-dir _build-js ./wasm/worker.bc.js ./wasm/node_main.bc.js \
  ./wasm/test/hashes.bc.js ./wasm/test/corpus_run.bc.js
wasm/dist.sh WORK/out DIST
```

A separate build directory keeps the browser profile's build apart from the
native one. `dist.sh` puts what a page needs in `DIST`: `worker_boot.js`,
`z3_shim.js`, `z3.js`, `z3.wasm` and `worker.bc.js` (about 830 KB, 180 KB
gzipped).

## The worker

A page starts the worker with `new Worker('DIST/worker_boot.js')`. It loads Z3,
the one asynchronous step, then `worker.bc.js`. A request posted meanwhile
waits; if Z3 cannot load, every request is answered with an error message.
Plain static files are enough: no special headers (COOP/COEP) are needed, as
Z3 is built without threads and so without shared memory.

The page posts a request: the JSON body that the web server's
`/api/<pipeline>/stream` endpoints take (`program`, `loop_semantics`, `steps`,
`memory_model`, `compare_models`), as a string, with the pipeline named in a
`pipeline` field: `parse`, `interpret`, `episodicity`, `assertions` or
`visualize`.

The worker posts back each JSON message of the answer, as a string, exactly
as the server sends them over SSE. Then it posts `null` to say the answer is
complete. The server and the worker run the same pipelines (`src/streaming.ml`).
Each answer runs to completion before the worker takes the next request; to
cancel one, terminate the worker and start another.

Under node, `node wasm/node_run.js WORK/out _build-js/default/wasm/node_main.bc.js PIPELINE < request.json`
loads Z3 and prints the answer as SSE frames.

## Testing

```bash
dune build ./wasm/test/session_native.exe ./wasm/test/hashes_native.exe ./cli/main.exe
# every pipeline on 7 programs, byte for byte; the worker; the hashes
python3 -I wasm/test/compare.py _build/default/wasm/test/session_native.exe \
  _build-js/default/wasm/node_main.bc.js WORK/out DIST
# verdicts against the CLI's, and timing: the samples and wasm/test/litmus_subset.txt
python3 -I wasm/test/verdicts.py _build/default/cli/main.exe \
  _build/default/wasm/test/session_native.exe _build-js/default/wasm/node_main.bc.js WORK/out
# the W1 corpus (evaluation/w1_smt_corpus/) through Z3 in wasm
python3 -I wasm/test/corpus.py CORPUS WORK/out \
  "$PWD/_build-js/default/wasm/test/corpus_run.bc.js" OUT_DIR 3
```

- `compare.py` first checks that the browser build hashes as the native one
  does: `test/hash_probe.ml` prints the hashes of fixed values, and the orders
  they put sets in, and both builds must print the same. A hash that overflows
  depends on the width of `int` (63 bits natively, 32 in JavaScript), and once
  reordered the browser build's executions (#193); MoRDor's hashes keep their
  low 30 bits. Then it asks every pipeline about 7 programs, natively and under
  node, and requires identical answers; `test/worker_test.mjs` drives the
  worker itself, through a shim that gives it a browser worker's globals.
- `verdicts.py` compares the browser build's verdict with `mordor run`'s, and
  its whole `assertions` answer with the native session's, for the CLI's
  samples and a fixed litmus subset (`all` for every litmus test), and prints
  the time each took.
- `corpus.py` solves every distinct query of a W1 corpus with Z3 in wasm and
  compares each answer with native Z3's.

## Timing

Measured under node 22 on a shared, loaded machine (load average 10–15 on 20
cores), wall clock, the browser build against the native session
(`session_native.exe`) on the same request (W4, #180). Information, not a
benchmark.

| what | native | browser build | ratio |
|---|---:|---:|---:|
| all 459 litmus tests and the CLI's 3 samples, `assertions` (`verdicts.py all`) | | | median 9.0×, max 31.5× |
| seqlock-1, `assertions`, step counter 1 | 3.6 s | 5.4 s | 1.5× |
| seqlock-1, `assertions`, step counter 2 | 17.9 s | 21.1 s | 1.2× |
| seqlock-1, `visualize`, step counter 2 | 17.9 s | 26.4 s | 1.5× |
| the W1 corpus, per `check` (`corpus.py`) | | | median 5.9× |

A litmus test takes well under a second natively, so the ratio there is
mostly the browser build starting: node, and compiling Z3's 16 MB of wasm. In
a page the worker starts once and answers every run after. Memory: seqlock-1
peaked at 240 MB against 73 MB natively. Every answer above was byte-identical
to native's, and the corpus's 107,242 distinct queries got native Z3's answer
every time.
