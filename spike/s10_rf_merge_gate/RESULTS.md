# S10: is per-thread read-from enumeration worth building? (step 0)

**Verdict: the prune the plan needs exists, but it is per location, not per
thread.** On rcu-2's futures no sampled execution was coherent: smrd rejected
all 283 checked. Every one of the 251 examined for locality was rejected by a
single location on its own, with every other location left unordered. Most
read-from choices cross threads, so enumerating per thread and merging leaves
almost all of the product to the merge. Nothing recurs across justification
combinations, so there is nothing to reuse. The lever is a per-location
coherence check made while read-from relations are enumerated, once a
location's reads have their writes. Plan steps 1-3 as written (per-thread
fragments, merge, reuse) would not reach it.

Run from the repo root (the hook is off by default):

    MORDOR_S4_COUNTERS=1 MORDOR_S10_RF_SAMPLES=5 MORDOR_S10_COMBO_STRIDE=100 \
      dune exec mordor -- futures --info --threads 4 --step-counter-per-loop 2 \
      --single programs/rcu-2.lit 2> run.err
    python3 spike/s10_rf_merge_gate/analyze_s10.py run.err

`MORDOR_S10_RF_SAMPLES=k` makes `Freeze.freeze` keep k valid read-from
relations per justification combination instead of all of them. Each one is the
first valid relation of a depth-first search in a random order. Each try gets
`MORDOR_S10_BUDGET` extension steps (default 2,000) and is restarted with a
new order when it runs out. `MORDOR_S10_COMBO_STRIDE=n` freezes every n-th
combination only. The rest of the pipeline, coherence included, runs on that
sample.

## The runs

| run | combinations | relations each | executions | coherence checked | stopped by |
|---|--:|--:|--:|--:|---|
| 2 | 219 of 4,374 | 20 | 4,380 | 4 | Claude Code, low system memory (10 threads) |
| 3 | 44 of 4,374 | 5 | 220 | 32 | watchdog, 30.7GB (4 threads) |
| 4 | 44 of 4,374 | 5 | 220 | 31 | watchdog, 36.6GB (4 threads), with the locality check |
| 5 | 44 of 4,374 | 5 | 220 | 220 | completed, 1.4GB (4 threads), after the fix in (f) |

Runs 2-4 did not get through coherence. The co search then took a median 6s
per execution and several GB (see (e)), so four at once exhausted memory
within two minutes.

## (a) Where the read-from choices are (run 2)

| | |
|---|--:|
| reads per combination | 16-29 |
| log10 of the product of choices, median (max) | 24.1 (29.7) |
| the same over same-thread and pre-fork writes only | 8.0 (10.1) |
| a read's choices from the other thread | 78.1% |
| from its own thread | 20.6% |
| from before the fork (Init, initialisers) | 1.2% |

The reads with the most choices, 13-18 each, are the polls of `rrcu[i]`, the
reads of `rC`, and reads through pointers read from them. A per-thread split
leaves about 10^16 of the 10^24 to the merge.

## (b) Reuse across justification combinations (run 2)

| thread | combinations | distinct keys: alternatives | alternatives + predicates |
|--:|--:|--:|--:|
| 1 | 219 | 219 | 219 |
| 2 | 219 | 219 | 219 |

The key is a thread's reads with their candidate writes. No two combinations
share one, even before predicates are counted: each combination is on a
different path, with different events. Dedup and minimality kept all 4,380
sampled results, so they collapse nothing either.

## (c) Coherence (runs 3 and 4, smrd)

| | run 3 | run 4 |
|---|--:|--:|
| checked | 32 | 31 |
| admitted | 0 | 0 |
| rejected by thin-air | 0 | 0 |
| rejected by the co search | 32 | 31 |
| median ms: setup / thin-air / co search | 170 / 0 / 5,996 | 227 / 0 / 5,807 |

## (d) Is the rejection local? (run 4)

For each location's group of writes: how many of its po-respecting orders
pass the axioms with every other location unordered. smrd's violations only
grow with co (S6), so a location with none rejects the execution whatever the
other locations do.

| | executions |
|---|--:|
| rejected with co empty everywhere | 0 |
| rejected by one location on its own | **31** |
| rejected only by orders at several locations together | 0 |

Rejecting locations per execution: 2 in 13 executions, 3 in 13, 4 in 5.

By number of orders a location has:

| orders | locations seen | rejecting on their own |
|--:|--:|--:|
| 1 | 35 | 25 |
| 2 | 29 | 3 |
| 3 | 2 | 0 |
| 5 | 22 | 21 |
| 7 | 5 | 5 |
| 10 | 8 | 8 |
| 15 | 1 | 0 |
| 20 | 1 | 1 |
| 28 | 22 | 22 |

Most of the locations with a single possible order (25 of 35) still reject.
There the failure depends on no co choice at all: it is the read-from edges and
hb at that one location, a stale read against a write that happens before it.

## (e) The co search's memory

The search itself is small: its leaves number a median 250 per execution
(max 1,176). The memory goes into `try_all_coherence_orders` building every
permutation of a location's writes before it filters them by po: for 10 writes
that is 3.6 million lists, of which 28 respect po. This is separate from
read-from enumeration, and cheap to fix by generating only the linear
extensions of po.

## (f) After the fix to the co search (run 5)

`Algorithms.linear_extensions` (eee1ee4) builds only the po-respecting orders.
Run 5 is run 3's sample (44 combinations, 5 relations each, 4 threads) with
the locality measurement on, and it ran to the end:

| | runs 3-4 | run 5 |
|---|--:|--:|
| peak memory | stopped at 30.7 / 36.6GB | 1.4GB |
| coherence checks completed | 32 / 31 | 220 |
| ms per check, median (p90) | 6,020 (13,608) | 408 (1,428) |
| admitted by smrd | 0 | 0 |
| rejected by one location on its own | 31 of 31 | 220 of 220 |

## (g) A per-location check during enumeration (run 5)

`Coherence.rejected_by_one_location` holds of an execution when its thin-air
check fails, or some location has no po-respecting order the axioms accept
with every other location unordered. For each sampled relation,
`MORDOR_S10_LOCALITY` finds, by bisection, the fewest of its reads, in
enumeration order, whose edges alone already make it hold. It uses two sets
of predicates for grouping locations: the combination's plus those the
chosen edges add (what a check during enumeration has), and the
combination's alone (which could be computed once per combination).

| | edges' predicates | combination's only |
|---|--:|--:|
| relations rejected before every read has its write | 220 of 220 | 220 of 220 |
| reads needed, median (of a median 23) | 3 | 4 |
| as a fraction of the reads, median (max) | 0.12 (0.60) | 0.16 (0.80) |
| log10 of the choices below that point, median (of 24.1) | 20.0 | 19.2 |

One check costs a median 160ms, most of it the location-equality relation:
one solver query per pair of events. With the combination's predicates only,
that relation is the same for every relation of the combination and can be
computed once.

**Soundness.** Over the four litmus corpora (`MORDOR_S10_LOCALITY=1 mordor run
--all-litmus-tests DIR -r`), the check was run on every execution reaching
coherence and compared with the model's verdict. It never rejects what the
model admits:

| model | admitted, not local | rejected, local | rejected, not local | admitted, local |
|---|--:|--:|--:|--:|
| cc | 136 | 44 | 0 | 0 |
| coherence | 274 | 0 | 0 | 0 |
| imm | 8,176 | 1,905 | 2 | 0 |
| local | 15 | 3 | 0 | 0 |
| rc11 | 5,471 | 328 | 5 | 0 |
| ryw | 5 | 0 | 0 | 0 |
| smrd | 1,354 | 83 | 0 | 0 |
| tso | 18 | 0 | 0 | 0 |
| wra | 55 | 12 | 0 | 0 |

It catches 2,382 of the corpus's 2,389 rejections. The other 7 need orders at
several locations together. od-lso, whose violations do not only grow with co
(S6), does not appear in the corpus runs and would have to be excluded.

## What this means for the plan

1. **Per-thread fragments and merge (plan steps 1-2):** not the lever. The
   choices are cross-thread, so a merge would do nearly all the enumeration.
2. **Reuse (step 3):** nothing to reuse on rcu-2.
3. **Per-location coherence while enumerating read-from:** now measured,
   in (g): every sampled relation is rejected after a median 3-4 of 23 reads,
   cutting a median 10^19-10^20 of the 10^24 choices below that point. Every rejection
   seen needs one location only. A check in `fold_path_rf`, once all reads of
   a location have their writes, prunes the relation at that point instead of
   after 16-29 reads. It is sound for locations known to be equal under the
   combination's predicates (a must-alias grouping only grows as predicates
   are added, and the axioms' violations only grow with rf and co). Grouping
   by the combination's predicates alone costs one reject in (g) a read
   later, and makes the grouping a once-per-combination cost.
4. **Linear extensions in the co search:** done (eee1ee4); see (f).

Caveats: no sampled rcu-2 execution was admitted, so how many
relations survive the per-location check at each depth, which decides whether
rcu-2 then finishes, is not measured here. 283 executions checked in all, from 44 and 219 of the 4,374 combinations.
The sampler is not uniform, since it takes the first valid relation under a
random order. smrd only, the default model, as rcu-2 names none.
