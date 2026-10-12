# Evaluation results: V1 (#97) and V2 (#98)

Measured 2026-10-11/12 on branch `v1-v2-evaluation` (b8eb12d), on an
Intel i7-13700H (20 hardware threads, 62 GB). The baseline is 6f2eef0, built
from its own worktree. `rcu-2.lit` here is the rcu-2 program as measured: the
counter `C` is a global holding a pointer, and `fadd`/`cas` take `&C`.

## V1: equivalence of the bounded paths

`dune exec test/golden/equivalence.exe -- [--flags-off] [--timeout SECS]` runs
each program under the enumeration and under each bounded path, and compares
what is reported:

- the futures from witnesses (R13) against the futures from the enumeration;
- the verdict asked by query (R16) against the enumeration's verdict;
- every execution a bounded path returns against the enumeration's executions,
  matched canonically: syntactically, else semantically (the predicates entail
  each other, checked by Z3), else divergent.

Corpus: `litmus-tests`, `litmus-tests-review`, `litmus-tests-jmm` and
`programs` (517 programs), with a 300 s timeout per program.

| mode | agree | differ | timed out | errors | matches (syntactic / semantic / divergent) |
|---|---|---|---|---|---|
| flags off (baseline against itself) | 512 | 0 | 5 | 0 | 30,688 / 0 / 0 |
| flags on (witnesses, by query) | 513 | 0 | 4 | 0 | 6,411 / 94 / 0 |

- With the flags on, 403 of the 513 programs were answered by query. The rest
  have no assertion the query can ask.
- **The first flags-on run found 7 differences.** The futures from witnesses
  missed futures for paper112F, paper112F-unstrengthened, paper108,
  FWD-STRENGTHEN-LIFT, LB+UB+data+z, LB+UB+data+z-memory and JCTC17-left.
  - Cause: the witness stage pruned combinations with S14's dominator rule,
    which does not check predicate entailment.
  - Fix: it now uses the same exact rejection as the query stage. The table
    above is after the fix.
- **The harness detects a planted bug.** With `query.holds` negated, it
  reported differences. The source was then restored.
- **Timeouts, rerun at 3600 s:**
  - `programs/cas_aba.lit` agrees in both modes (492 syntactic matches with
    the flags off, 6 with them on).
  - `programs/episodicity/hp-1.lit`, `programs/episodicity/rcu-1.lit`,
    `programs/episodicity/seqlock-1.lit` and `programs/rcu-3.lit` time out at
    3600 s even with the flags off. The enumeration itself does not finish, so
    these are not compared.

## V2: cost

### Corpus wall time

The baseline's own `litmus-tests` (303 files), single thread,
`run --all-litmus-tests -r --allow-unknown-model`, three runs each:

| build | runs (s) | median (s) | peak RSS |
|---|---|---|---|
| baseline 6f2eef0 | 22.1, 19.4, 20.6 | 20.6 | 338 MB |
| new (disjoint regions, default) | 12.1, 11.8, 10.7 | 11.8 | 176 MB |
| new, `--overlapping-regions` | 11.7, 12.5, 10.7 | 11.7 | 179 MB |

- The target was within 10% of the baseline. The new build takes 57% of the
  baseline's time.
- Region disjointness costs nothing measurable on this corpus.
- Both region modes give the same verdict on all 303 tests.
- 20 verdicts differ from the baseline's. These come from fixes merged since
  6f2eef0, which the golden gate tracks. Several test files changed in that
  time too, for example IRIW+Fsc+Fsc and coproductReorder.

### rcu-2

16 threads, `--step-counter-per-loop N`; time and peak RSS from
`/usr/bin/time -v`.

| measurement | baseline | new |
|---|---|---|
| futures, N = 1 | > 20 min (killed), 3.2 GB | 1 min 45 s, 3.3 GB; 64 futures |
| futures, N = 2 | > 20 min (killed), 6.2 GB | 38 min 10 s, 18.2 GB; 432 futures |
| assertion by query, N = 1 | — | 3 min 48 s, 3.6 GB |
| assertion by query, N = 2 | — | > 60 min (killed), 13.2 GB |

- **By query at N = 1:** 256 kinds of justification combination, all 256 shown
  to have no witness, none undecided. So Valid is true and there is no
  undefined behaviour: no use after free at one iteration per loop.
- **By query at N = 2:** no verdict within the hour. To show that no use
  after free exists, every kind must be refuted. A witness, if one exists,
  ends the search early.
  - An earlier fixture found a witness at N = 2 in 57 s. That witness relied on
    overlapping allocations, which region disjointness (R17) now rules out.
- To reproduce the futures list, run:

  ```
  mordor futures --single evaluation/rcu-2.lit --step-counter-per-loop N --threads 16
  ```

  The output is 0.5 MB at N = 1 and 4 MB at N = 2, so it is not committed.
