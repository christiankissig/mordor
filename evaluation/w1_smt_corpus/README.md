# W1: a corpus of MoRDor's SMT queries (#175)

The queries MoRDor actually sends to Z3, in SMT-LIB 2, so that WS2 (#176, Z3 in
the browser) and WS3 (#177, an alternative solver) can be measured on real
workload.

## Recording queries

With `MORDOR_SMT_DUMP` set to a directory, every query that reaches Z3 is
written there (`Solver.Dump`, called from `Solver.check_asserted`, which all of
MoRDor's satisfiability checks go through):

- `<digest>.smt2`: one file per distinct query. It holds the solver's
  assertions across every pushed scope, as asserted
  (`Z3.Solver.get_assertions`), printed with their declarations and
  `(check-sat)` by `Z3.SMT.benchmark_to_smtstring`, so each file can be solved
  on its own. Not `Z3.Solver.to_string`: on a solver that has been checked
  before, that prints the preprocessed assertions and the model converter's
  state (`model-add`, `model-del`), which is not SMT-LIB.
- `index.tsv`: one line per query asked, in the order asked: digest, caller (the
  first function outside `solver.ml`), Z3's answer, and seconds in
  `Z3.Solver.check`.
- `calls.tsv`, written at exit: scope pushes and model reads, by caller. A
  model read is counted even when Z3 was not asked: `Solver.solve` reads one
  off a query that `Solver.trivially` already answered.

Queries that the conjunction cache or `Solver.trivially` answer never reach Z3,
so they are not recorded. The variable is unset by default, and then nothing is
written.

## Building the corpus

```bash
dune build
evaluation/w1_smt_corpus/generate.sh OUT [MORDOR] [TIMEOUT] [THREADS]
python3 -I evaluation/w1_smt_corpus/recheck.py OUT [WORKERS] [SECONDS]
python3 -I evaluation/w1_smt_corpus/analyze.py OUT > summary.md
```

`generate.sh` runs a fixed set of tracked programs, one dump directory per
run, and records how each run ended in `OUT/jobs.tsv`:

- every litmus test under `run`;
- `programs/*.lit` under `run` and under `run --by-query`;
- the episodicity programs under `episodicity`;
- `evaluation/rcu-2.lit` by query at one iteration per loop.

`recheck.py` solves each distinct query from its file with the standalone `z3`
and compares the result with every answer MoRDor's Z3 gave. `analyze.py`
reports query counts, solve times, callers, and the fragment: every operator
that occurs, and which queries are non-linear.

The corpus itself is not committed: it is regenerated from these scripts.
