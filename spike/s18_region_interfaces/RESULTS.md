# S18: interfaces of syntactic region decompositions (#95)

**Verdict: no-go for R15 (#101).** No syntactic decomposition keeps rcu-2's
read-from choices local. Cut by thread — the coarsest cut there is — a merge of
the regions would still face 10^15.5 of the 10^16.8 choices of a median
combination; every finer cut leaves it more, up to all of them. No two regions
have the same shape, so there is nothing to build once and reuse. What bounds
rcu-2 is not a region cut but a solver: S19 (#96) decides each combination
whole, in a third of a second.

This measured *code* regions. The other reading of "region-bounded" — memory
regions, i.e. allocations that do not overlap — is R17 (#103), a semantic
decision measured on 2026-09-19 as cutting the product from ~10^24 to ~10^13.

Run from the repo root (the hook is off by default; with it on nothing is
enumerated, so a dump takes seconds):

    MORDOR_S18_DUMP=rcu2.jsonl dune exec mordor -- futures --threads 3 \
      --step-counter-per-loop 1 --single programs/rcu-2.lit
    python3 spike/s18_region_interfaces/analyze.py rcu2.jsonl

`MORDOR_S18_DUMP=<file>` makes `Freeze.enumerate` append, per justification
combination, the path's events (thread, type, mode, volatility, location,
value, loop indices, elided or not), program order among them, and each read's
candidate writes after `rf_search`'s static filters (location satisfiable, not
po-after, not shadowed). `run_output.txt` is the analysis reported here.

## The decompositions

Paths carry no branch events — a branch's condition lives in the events'
`restrict` — so blocks cannot be cut at branches. The cuts compared, from
coarsest to finest:

| cut | a region is |
|---|---|
| thread | one thread (plus the pre-fork code and Init as their own) |
| loop-iteration | a thread's events with the same loop indices |
| segment | a maximal run of a thread's events with the same loop indices |
| rcu-section | a thread's events between two volatile writes — rcu-2's `*(rrcu+rtid)` enter/exit markers |
| event | one event: every choice crosses, the baseline a merge cannot beat |

## rcu-2, step counter 1 (256 combinations, medians)

| cut | choices inside the read's region | crossing edges | open reads / region | exported writes / region | log10 choices | log10 left to a merge | regions | distinct shapes |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| thread | 0.26 | 0.76 | 4.38 | 5.88 | 16.77 | **15.47** | 4 | 4 |
| loop-iteration | 0.17 | 0.85 | 2.19 | 2.94 | 16.77 | 16.13 | 8 | 8 |
| segment | 0.14 | 0.88 | 1.46 | 1.96 | 16.77 | 16.27 | 12 | 12 |
| rcu-section | 0.13 | 0.88 | 1.46 | 1.96 | 16.77 | 16.47 | 12 | 12 |
| event | 0 | 1 | 0.34 | 0.45 | 16.77 | 16.77 | 52 | 40 |

"Left to a merge" counts, per read, its candidate writes outside its region
plus one option standing for "some write inside", resolved within the region.
A cut that bounded the problem would drive that column towards 0; the best cut
removes 1.3 of 16.8 orders of magnitude. The thread row agrees with S10's
measurement at step counter 2 (78% of choices cross threads there, 74% here).

rcu-2's reads look outside their region because its shared state is what the
threads communicate through: the RCU counters `rrcu[i]`, the pointer `rC`, and
the nodes read through it. Cutting finer only moves more of that to the
interface.

## The other programs

| program | combinations | best cut | inside | log10 all → merge |
|---|--:|---|--:|--:|
| rcu-1 | 4 | thread | 0.94 | 0.48 → 0.30 |
| seqlock-1 | 10 | thread or rcu-section | 1.00 | 0 → 0 |
| avoidoota/listing15 | 2,200 | none | 0.00 | 0.30 → 0.30 |
| jctc/JCTC11 | 864 | none | 0.00 | 0.30 → 0.30 |

The single-threaded-reader programs keep their choices local, and have almost
nothing to choose. The litmus tests are the opposite by construction: a read
exists to read another thread's write.

## Recurrence

Within a combination no two regions have the same shape (their events' types,
locations, values and volatility in order) under any cut: the two rcu-2 threads
differ in `rtid`, and everything downstream of it. Across combinations S10
already found that no two share a thread's reads and candidate writes. There is
nothing a bottom-up construction could build once and reuse.

## What this means

- **R15 (#101): do not build it.** Its premise, that a syntactic region has a
  small interface, fails on the program it was meant for.
- R10's scope parameter and R11's `_delta` checks, built for R15, have no
  caller in sight. They stay, cheaply, as the only production code that
  anticipated a merge.
- The measurement that does bound rcu-2 is S19: one solver query per
  combination, deciding existence exactly, in 0.2–0.3 s.
