# S7: Z3 push/pop against fresh solvers and the cache (#19)

**Verdict: keep plan item 3d, in its simplest form.** One long-lived Z3 solver
per domain, with each query pushed, checked and popped, answers every query
exactly as a fresh solver does. It saves 0.5 to 0.95 ms per query that reaches
Z3: 2% of the run on the large litmus tests, 12 to 17% on 3.2W and Upd-Stuck,
and 25 to 44% on the small RCU and UAF programs. Nothing finer pays. Keeping
the assertions consecutive queries share gains nothing over a push per query,
and the syntactic shortcuts avoid 3% of Z3 calls and save no measurable time.
The cache has to stay: without it the same streams take 10 to 50 times as
long. That decides R12 (#33): a win.

## What was built

- **Capture.** With `MORDOR_S7_TRACE=<file>`, `Solver.quick_check_cached`,
  which `is_sat_cached`, `is_unsat_cached`, `exeq` and `expoteq` go through,
  writes every query in the order asked. Each record holds the function it was
  asked from (the first frame in `src/` outside `solver.ml`), whether the cache
  answered it, and the conjunction as the caller built it.
- **Replay** (`s7_solver_scopes.ml`). Each trace is replayed against:
  - **fresh**: today's. The cache, then the syntactic shortcuts, then a fresh
    Z3 solver in the domain's context.
  - **pushpop**: the cache and the shortcuts, then one long-lived solver, the
    query pushed, checked and popped.
  - **pushpop-raw**: as pushpop, without the shortcuts.
  - **prefix**: one long-lived solver that keeps what consecutive queries
    share, in their callers' order. The stack is popped back to the longest
    shared prefix and the rest pushed one assertion at a time.
  - **fresh-nocache**: fresh without the cache (`S7_NOCACHE=1`).
  - **fresh-again**: fresh, last, to show what a warm Z3 context is worth
    (nothing measurable).

  The cache is the harness's own, the same for every strategy. So the
  differences between strategies are the cost of the queries that miss it.

Solver gained `trivially` (the shortcuts, split out of `check`) and
`check_asserted` (Z3 on what is asserted, nothing added), so that the replay
can take the shortcuts away.

## Results

Traces of `mordor run --single` on seven programs. The untraced run time is
the pipeline's. The last two columns compare the solver time saved with it.

| program | run | queries | cache hits | Z3 calls | fresh | pushpop | saved | of run |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| 3.2W | 22.0s | 352,724 | 98.9% | 4,014 | 5.70s | 1.90s | 3.80s | 17% |
| JCTC11 | 14.8s | 340,020 | 99.9% | 423 | 1.64s | 1.35s | 0.30s | 2% |
| avoidoota/listing15 | 18.9s | 407,899 | 99.9% | 487 | 1.94s | 1.58s | 0.36s | 2% |
| promising/Upd-Stuck | 1.51s | 22,418 | 98.6% | 303 | 0.261s | 0.082s | 0.18s | 12% |
| uaf-bug-extended | 0.41s | 2,932 | 94.9% | 137 | 0.119s | 0.015s | 0.10s | 25% |
| rcu-1 | 0.61s | 5,128 | 92.5% | 347 | 0.320s | 0.049s | 0.27s | 44% |
| cas-increment-race | 0.21s | 895 | 84.7% | 126 | 0.070s | 0.006s | 0.064s | 30% |

Against pushpop, pushpop-raw ranges from 10% faster to 2% slower and prefix
from 6% faster to 20% slower, on differences of hundredths of a second: no
signal either way. Every strategy agrees with fresh on every answer, with no
`unknown`. Without the cache, Upd-Stuck's stream takes 15.9s instead of 0.26s
and rcu-1's 3.7s instead of 0.32s.

What a fresh solver costs is building one: `Z3.Solver.mk_solver` and its
finalisation, about 0.8 ms each. The queries themselves are easy.

### Per call site

Totals over the seven traces (fresh → pushpop). Attribution is by the first
frame in `src/`, so a closure run by a library function can be reported under
that function's name:

| site | queries | fresh | pushpop |
|---|--:|--:|--:|
| `Coherence.check_for_coherence` (location equality, `exeq`) | 375,681 | 4.34s | 1.97s |
| rf: `compute_path_rf`'s partial check, run by `ListMapCombinationBuilder.build_combinations` | 122,755 | 2.02s | 0.69s |
| final: `Freeze.instantiate_execution` | 59,273 | 1.05s | 0.32s |
| `Hashtbl.filteri` closures (caller not resolved) | 94,483 | 1.00s | 0.45s |
| rf: `compute_path_rf`'s location filter (`expoteq`) | 221,826 | 0.73s | 0.73s |
| freeze: `Freeze.freeze`'s combined predicates | 48,208 | 0.31s | 0.22s |

The issue's three sites (rf, freeze, final) all gain, rf most. The largest
gain is at a site the issue did not name: coherence's location equality.
Every site gains or is unchanged, so there is nothing to choose between. The
change belongs in `quick_check_cached`, below all of them.

## Answers

1. **Streams captured:** seven, 1.13 million queries, from `quick_check_cached`
   in the order asked.
2. **Replayed against three harnesses and two more:** wall time and Z3 calls
   above; 0 disagreements.
3. **Per-site benefit:** every site gains or is unchanged; see the table above.
4. **Decision:** keep 3d. The scope is a single query: push, check, pop, on one
   solver per domain, with the cache and shortcuts in front as today. A
   longer-lived scope that shares assertions between queries gains nothing on
   these streams. R12 (#33) takes the "win" branch.
