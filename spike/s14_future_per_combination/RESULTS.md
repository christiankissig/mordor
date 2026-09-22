# S14: one future per justification combination (#91)

**Verdict: go for R13 (#99), with one rule the issue did not anticipate.**
Every execution of a justification combination has the same future — by
construction, and confirmed on all 375 programs. But taking one coherent
witness per combination over-reports: minimality removes 16% of the futures
such witnesses would give. The rule that reproduces the tool's futures exactly,
on every program, is:

> A combination's future is reported iff the combination has a **coherent**
> execution whose read-from relation is **not also a valid read-from of any
> combination that dominates it** — same events, `dp` and `ppo` contained in
> its own, not both equal.

On rcu-2 no combination dominates another (S11), so there the rule reduces to
"has a coherent execution".

Run from the repo root (the hook is off by default):

    tr '\n' '\0' < spike/s14_future_per_combination/programs.txt \
      | S14_EXTRA=--allow-unknown-model xargs -0 -P 8 -I{} \
          spike/s14_future_per_combination/run_one.sh {} > out.tsv
    python3 spike/s14_future_per_combination/analyze.py out.tsv

`MORDOR_S14=1` makes `generate_executions` also run every freeze result
through coherence with no deduplication or minimality, apply the rule above,
and push the same results through each stage in turn, printing three `S14`
lines per program. `run_output.tsv` is the run reported here.

## 1. By reading: the future cannot depend on `rf`

A future is `identity(e) ∪ ((dp ∪ ppo) ∩ e×e)` (`Futures.calculate_future_set`,
`src/futures.ml`); `rf` is excluded on purpose, so futures split per thread.

- `Freeze.frame` computes `e`, `dp` and `ppo` from the path, the
  combination's `dp` and `ppo` and its elided events. It is called once per
  combination, from `Freeze.prepare`, before any read-from choice.
- `instantiate_execution` builds every result of the combination with exactly
  that `e`, `dp` and `ppo`; only `rf`, `pp` and `rmw` vary per result.
- `freeze_to_execution` copies `e`, `dp` and `ppo` into the execution
  unchanged.
- Nothing downstream rewrites them. The coherence stage sets `co` and nothing
  else. The models' `compute_dependencies` is defined but has no caller.

## 2. Measured: 375 programs

litmus-tests, litmus-tests-promising and litmus-tests-review (the 333 the
golden gate covers) plus litmus-tests-cpp and litmus-tests-jmm, 42 more.
60 of them name a model MoRDor does not implement (Promising, and the C++ and
Java ones); they were run with `--allow-unknown-model`, so under the model in
effect. That only changes which coherence check applies, not the question.

| | |
|---|--:|
| combinations with at least one valid execution | 38,409 |
| freeze results | 64,092 |
| **distinct futures among one combination's results, max over all** | **1** |
| futures of every coherent result, unminimised (what one witness each gives) | 10,483 |
| futures the tool reports | 8,814 |
| reported futures missing from the unminimised set | 0 |
| **futures from the rule above** | **8,814 — equal to reported on all 375 programs** |

### Which stage removes futures

The same results pushed through each stage in turn, counting distinct futures
after each:

| stage | programs losing futures | futures lost |
|---|--:|--:|
| freeze-result deduplication | 0 | 0 |
| **freeze-result minimality** | **53** | **1,669** |
| execution deduplication | 0 | 0 |
| execution minimality | 0 | 0 |
| coherence | 9 | 23 |

Deduplication cannot remove a future (it merges identical results). Execution
minimality could in principle and never does here. Freeze-result minimality
drops a result when another has the same events and the same `rf` and
strictly smaller `dp`/`ppo` — across combinations. Since each combination has
one `(e, dp, ppo)`, that is a relation between combinations lifted to their
read-from sets: A loses the result with `rf` r iff some combination dominating
A also has r. That is the rule's second clause.

| corpus | programs | with a minimality loss | futures: unminimised → reported |
|---|--:|--:|--:|
| litmus-tests | 303 | 44 | 7,192 → 5,966 |
| litmus-tests-cpp | 18 | 0 | 356 → 356 |
| litmus-tests-jmm | 24 | 5 | 1,672 → 1,636 |
| litmus-tests-promising | 20 | 1 | 487 → 377 |
| litmus-tests-review | 10 | 3 | 776 → 479 |

Largest: `avoidoota/listing15` 1,329 → 675, `popl_grounding/FADD` 227 → 84,
`Upd-Stuck` 286 → 176. The 53 programs with a minimality loss are exactly the
53 with a dominated combination (7,049 dominated combinations in all).

### The coherence caveat

31 of the 38,409 combinations (9 programs) have valid executions but no
coherent one, and contribute no future: `Coh-CYC`, JCTC17–20, the two
`mp-rs-add-est` release-sequence tests, `pldi_repairing/LB`. 23 futures in all.
A witness search must look for a *coherent* witness, and treat exhausting the
combination as "no future from here".

## 3. What this means for R13

- **Sound:** one witness per combination, under the rule, gives the tool's
  futures exactly on every program measured.
- **The witness search has two conditions, not one.** For combination A, find
  the first read-from r that is valid for A, gives a coherent execution, and
  is not a valid read-from of any combination dominating A. Domination is
  decided per combination, from `prepare`'s output, before anything is
  enumerated; testing r against a dominating B means running B's own checks
  on r, not enumerating B.
- **"Valid for B" must mean what B's enumeration would keep**, including the
  per-location coherence prune, which is gated per combination by
  `coherence_prune_min`. A read-from B's prune would drop is not in B's list,
  so it does not remove A's result. R13 has to replicate that gate.
- **rcu-2:** S11 found no dominated combination (0 of 4,374, in 2,916 event
  sets), so the second condition never applies. rcu-2's futures are the
  futures of its combinations with a coherent execution: at most 2,916. How
  fast one coherent witness can be found per combination is S15 (#92).
- Execution minimality is an unexercised path: the rule ignores it and the
  measurement shows it never removed a future. V1 (#97) should keep checking.
