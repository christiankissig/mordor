# S5: incremental cycle detection at MoRDor's sizes (#17)

**Verdict: Phase 3b does not need incremental closure.** The relations MoRDor
asks about acyclicity are tiny: at most 25 events and 263 edges, and a median
of 7 edges. At those sizes Pearce and Kelly's dynamic topological order is no
faster than the simpler thing the issue suggests: when a merge adds edges, a
search from each new edge's target for its source. Both beat re-checking the
whole relation per edge by 8 to 25 times. At merge batches of 64 edges a
from-scratch depth-first search is within 40% of them. And acyclicity is a
small cost today: at most 0.9s, 4% of the slowest run measured.

One thing turned up on the way. `URelation.acyclic` decides acyclicity by
closing the relation transitively, by naive fixpoint iteration, and looking
for a loop. A depth-first search gives the same answer 3 to 11 times faster on
these relations. That is worth up to 4% of a run today.

Run from the repo root, on traces captured with `MORDOR_S5_TRACE=<file>`:

    dune exec spike/s5_acyclicity/s5_acyclicity.exe -- TRACE ...

## What was built

- **Capture.** With `MORDOR_S5_TRACE=<file>`, `URelation.acyclic` writes every
  relation it is asked about, with the function that asked (`uset.ml`).
- **From scratch.** Each relation is checked by `URelation.acyclic` as it is
  and by a three-colour depth-first search. The answers are compared.
- **Merges.** Each relation is rebuilt as a merge would build it: its edges
  shuffled (seeded), added in batches of 1, 8 or 64, and acyclicity asked after
  each batch by:
  - **dfs**: a depth-first search over everything added so far, which is
    per-merge re-checking;
  - **bounded**: for each new edge `(u, v)`, a search from `v` for `u` over the
    graph so far, since only a cycle through a new edge can be new;
  - **pk**: Pearce and Kelly (JEA 2006), which keeps a topological order and
    searches only between the ends of an edge that goes against it.

  All three must agree on the first batch after which the relation is cyclic.

## Results

Seven runs (`mordor run --single`), the same programs as S7 (#19): 195,201
relations. The sizes, which S4 could only estimate from execution counts:

| | p50 | p95 | max |
|---|--:|--:|--:|
| edges | 7 | 55 | 263 |
| events | 10 | 20 | 25 |

Who asks, on the three largest runs: `Validation.rhb_acyclic` (15–24k calls,
up to 72 edges), `JustValidation.check_final` (48–78k calls, up to 10 edges)
and coherence (1–3k calls, up to 71 edges). rcu-1 alone reaches 263 edges, in
coherence and in rhb.

From scratch:

| run | relations | `URelation.acyclic` | dfs | |
|---|--:|--:|--:|--:|
| 3.2W | 19,180 | 0.899s | 0.135s | 7× |
| JCTC11 | 73,677 | 0.452s | 0.137s | 3× |
| listing15 | 99,828 | 0.606s | 0.149s | 4× |
| uaf-bug-extended | 108 | 0.038s | 0.001s | 30× |
| rcu-1 | 20 | 0.014s | 0.001s | 11× |

Disagreements: 0.

Merges, the three largest runs (the four small ones take milliseconds and
order the same way):

| run | batch | dfs | bounded | pk |
|---|--:|--:|--:|--:|
| 3.2W | 1 | 4.97s | 0.197s | 0.209s |
| | 8 | 0.856s | 0.192s | 0.197s |
| | 64 | 0.262s | 0.190s | 0.196s |
| JCTC11 | 1 | 1.63s | 0.179s | 0.201s |
| | 8 | 0.390s | 0.173s | 0.194s |
| | 64 | 0.233s | 0.171s | 0.190s |
| listing15 | 1 | 1.64s | 0.199s | 0.222s |
| | 8 | 0.418s | 0.194s | 0.214s |
| | 64 | 0.265s | 0.189s | 0.211s |

Disagreements: 0. Bounded search is as fast as Pearce–Kelly or slightly faster
everywhere, and needs no order kept alongside the relation.

## Answers

1. **Real relation sizes:** above. At most 25 events and 263 edges; median 7
   edges.
2. **Incremental against full recomputation:** Pearce–Kelly and bounded search
   are 8–25× faster than re-checking per added edge. Their lead shrinks as
   batches grow, to about 1.4× at 64 edges. There is no crossover at which
   Pearce–Kelly beats bounded search at these sizes.
3. **Decision for Phase 3b:** re-check per merge, by bounded search from the
   new edges (the `_delta` forms R11, #32, stubbed). Do not implement
   incremental closure. If merges in the bottom-up pipeline come in large
   batches, a plain depth-first search per merge is within 40% of both.

Separately, and with no merge in sight: replacing `URelation.acyclic`'s
closure with a depth-first search is a safe standalone win of up to 4% of a
run. The same fixpoint also implements `URelation.transitive_closure`, which
coherence uses for `eco` and `hb` on every candidate order, and was not
measured here.
