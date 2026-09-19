# S11: can a justification combination be skipped before it is frozen?

**Verdict: skip duplicates, not dominated combinations.** Many combinations
differ only in their forwarding and elision edges. Everything freeze reads of
them is then equal, so they freeze to the same results, which deduplication
merged afterwards. Freezing each kind once is exact, and is now what the
freeze stage does (`Freeze.duplicate_key`; `MORDOR_FREEZE_NO_MERGE` turns it
off). Dominance, where one combination's results would all be removed by
minimality in favour of another's, adds little and rests on an argument not
checked for the allocation-disjointness predicates. On rcu-2 it finds nothing.

Run (the hook is off by default; with it on nothing is enumerated):

    MORDOR_S11_DOMINANCE=1 dune exec mordor -- futures --threads 10 \
      --step-counter-per-loop 2 --single programs/rcu-2.lit 2>&1 | grep S11

## What is compared

For each combination: its events, dp and ppo restricted to them (what
minimality compares results by), its predicates, and each read's choice of
writes. A combination C is dominated by C' with the same events at three
levels, each adding to the last:

- **frame:** C' has dp and ppo contained in C's, not both equal;
- **+ predicates:** C' has a subset of C's predicates;
- **+ choices:** each read has a subset of its C' choices in C, and where C
  lets a read take Init because Init is its only write, C' does too (the Init
  rule drops Init where a read has another write).

A **duplicate** has everything equal to an earlier combination.

## rcu-2 (futures, 10 threads, step counter 2)

| | combinations | share of read-from choices |
|---|--:|--:|
| all | 4,374 in 2,916 event sets, at most 2 each | 2.9e32 |
| dominated, any level | 0 | 0 |
| duplicates | 1,458 | 17% |

At most 1.5 times less to freeze. rcu-2's obstacle is how many coherent
executions each combination has (spike/s10_rf_merge_gate, (h)).

## avoidoota/listing15

| | combinations | share of read-from choices |
|---|--:|--:|
| all | 15,960 | 3.2e4 |
| dominated: frame / + predicates / + choices | 8,040 / 8,040 / 7,160 | 53% / 53% / 50% |
| duplicates | 13,760 | 82% |
| either | 14,772 | 90% |

## The merge, over the litmus corpus

With `MORDOR_S4_COUNTERS=1` the freeze stage reports `combinations frozen: F
of N`. Over litmus-tests, litmus-tests-promising, litmus-tests-refinement and
litmus-tests-review (345 programs):

| | |
|---|--:|
| combinations prepared | 37,448 |
| frozen | 12,788 (34%) |
| of which listing15 | 2,234 of 15,960 |
| share skipped per program, median | 14% |
| programs skipping at least half / none | 40 / 153 |

Time: listing15 7.0s to 5.5s; litmus-tests, run with `--all-litmus-tests`,
25.4s to 23.7s; golden check 24.9s to 23.5s. Goldens, loop goldens,
check-order and integration tests agree with the merge on and off.

A first corpus run of the hook reported 2.19 million combinations: its
records were not cleared between programs run in one process, so each report
was a running total. It now reports each program's own.
