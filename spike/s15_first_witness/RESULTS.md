# S15: the cost of the first coherent execution (#92)

**Verdict: a first-witness search makes rcu-2's futures mostly reachable, but
not decidable; read order matters by 3×; and S19's solver is the better tool.**
At step counter 1, stopping each justification combination at its first
coherent execution finds witnesses for 216 of 256 kinds in 6 minutes on 16
threads with the best ordering, against 124 with today's. What no ordering can
do is show that a kind has *no* coherent execution without exhausting it:
32 kinds stayed undecided at a 60-second budget, and 24 of them have no
coherent execution at all (S19), so no budget would have settled them. S19
decides all 256 in 50 seconds on 3 threads.

Run from the repo root (off by default):

    MORDOR_S15=1 MORDOR_S15_ORDER=mrv-latest MORDOR_S15_SECS=60 \
      dune exec mordor -- futures --threads 16 --step-counter-per-loop 1 \
      --single programs/rcu-2.lit
    spike/s15_first_witness/run.sh SC SECS ORDER...   # one run per ordering

`MORDOR_S15` makes `Freeze.enumerate` stop a combination at its first read-from
relation that passes validation and the coherence model (smrd here), and
`generate_executions` carries on with those witnesses. `MORDOR_S15_ORDER`
chooses the order reads are decided in and writes tried in;
`MORDOR_S15_STEPS`/`MORDOR_S15_SECS` bound each combination's search. Each
combination prints its outcome — `witness`, `exhausted` (searched to the end,
no witness: it has none), `budget` — and a summary follows the freeze stage.
The `sc1_*.txt` files are the per-combination lines of the runs below;
`sc1_mrv-latest_keyed.txt` repeats the best run with each combination's
`duplicate_key`, for matching against S19.

## The orderings

| ordering | reads decided | writes tried |
|---|---|---|
| label | by label (today's) | as `rf_search` lists them (today's) |
| mrv | fewest candidate writes first | as listed |
| latest | by label | latest label first, Init last |
| mrv-latest | fewest candidates first | latest label first |
| loc | grouped by location expression | as listed |

## rcu-2, step counter 1: 256 kinds of combination, 16 threads, 60 s each

| ordering | witness | exhausted | budget | witness s, median / p90 / max | witness steps, median / p90 | wall | peak |
|---|--:|--:|--:|--:|--:|--:|--:|
| label | 124 | 0 | 132 | 7.5 / 45 / 60 | 4,010 / 22,497 | 12m22 | 2.28 GB |
| mrv | 198 | 7 | 51 | 4.3 / 38 / 61 | 2,048 / 15,706 | 8m06 | 2.24 GB |
| latest | 71 | 0 | 185 | 6.0 / 39 / 59 | 3,227 / 29,955 | 14m47 | 2.34 GB |
| **mrv-latest** | **216** | **8** | **32** | **2.9 / 24 / 46** | **933 / 12,672** | **5m57** | 2.27 GB |
| loc | 55 | 0 | 201 | 14.0 / 52 / 60 | 6,607 / 28,673 | 15m55 | 2.61 GB |

- **Deciding the most constrained read first** is what pays: it prunes a bad
  prefix before the search has invested in it. Trying the latest write first
  helps only on top of it — on its own it is worse than today's order, as is
  grouping by location.
- The search runs at 450–700 extension steps a second per thread; a combination
  out of budget had covered about 42,000.
- Memory is flat at 2.2–2.6 GB whatever the ordering: nothing is kept but the
  witnesses.
- The mrv, latest and mrv-latest runs shared the machine with other probes at
  low priority (3 threads). The keyed rerun of mrv-latest ran alone and gave
  the same counts, 216 / 8 / 32, and a median witness time of 2.8 s, so the
  contention did not change the comparison.

## Checked against S19, combination by combination

The mrv-latest run was repeated with each combination's key and matched
against S19's solver verdicts for the same keys:

| S15 | S19 | combinations |
|---|---|--:|
| witness | sat | 216 |
| exhausted | unsat | 8 |
| budget | sat | 8 |
| budget | unsat | 24 |

No contradiction: every witness S15 found is a combination S19 calls
satisfiable, and every combination S15 searched to the end without a witness is
one S19 calls unsatisfiable — independent confirmation of those eight solver
verdicts. The 32 out of budget are 8 combinations whose witnesses are deeper
than 60 seconds of search, and 24 that have no coherent execution. Those 24
can only be settled by exhausting them — S17's branching factor says whether
that is ever affordable — or by a solver.

## What this means for R13

- **The witness should come from the solver, not the search.** S19 finds a
  checked witness per combination in 0.2–0.3 s and proves absence where there
  is none; the search needs a budget and still leaves 12% of kinds undecided.
- If the search is used at all — as a fallback, or for models S19 does not
  encode — use **mrv-latest**: 1.7× the witnesses of today's order in half the
  time.
- S14's second clause (a witness's read-from must not be valid for a
  dominating combination) fits either: find a witness, check it against the
  dominating combinations, block it and ask again if it fails. On rcu-2 no
  combination is dominated.
