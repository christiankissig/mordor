# S17: the branching factor of the pruned read-from search (#94)

**Verdict: sharper pruning alone cannot make rcu-2's enumeration finish.** The
prunes do bite — three quarters of the choices a probe tries are rejected — but
late: the number of partial read-from relations still alive grows with every
read until about the tenth, peaks near 10^5 per combination at step counter 1 and
10^6 at step counter 2 in today's order (10^4 in the best), and the complete
relations that remain number about 10^4 to 10^5 per combination. That count is the obstacle, not the pruning. It is
exactly what S19's solver avoids: it needs one of them, or a proof there are
none. Deciding the most constrained read first cuts the tree about 10× at step
counter 1 and 100× at step counter 2, and is worth taking wherever enumeration
remains (S15).

Run from the repo root (off by default; with it on nothing is enumerated):

    MORDOR_S17_PROBES=50 MORDOR_S15_ORDER=mrv-latest dune exec mordor -- \
      futures --threads 16 --step-counter-per-loop 1 \
      --single programs/rcu-2.lit 2> s17.err
    python3 spike/s17_branching_factor/analyze.py s17.err

`MORDOR_S17_PROBES=k` sends k random descents through each combination's
read-from search. At each depth a descent records how many candidate writes
pass `check_partial` and, for each that does not, why: unsatisfiable
predicates, an rhb cycle, the Init rule, or the coherence prune — with the axiom
and location `Coherence.explain_rejection` names. Knuth's estimator turns a
descent's product of passing choices into the expected number of partial
relations alive at each depth. `MORDOR_S15_ORDER` sets the order (S15's). The
`*_label.txt` and `*_mrv-latest.txt` files are the analyses reported here.

## rcu-2, step counter 1: 256 kinds of combination, 50 descents each

Median over combinations of log10 of the partial relations alive at each depth
(the read-from choice product is 10^16.8):

| depth | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| label (today's) | 1.0 | 2.0 | 2.6 | 3.2 | 3.8 | 4.2 | 4.6 | 5.0 | 5.1 | 5.1 | 5.2 | 5.2 | 5.2 | 5.1 | 5.0 | 5.0 | 4.9 | 4.5 |
| mrv-latest | 0.6 | 1.2 | 1.6 | 2.0 | 2.4 | 2.8 | 3.1 | 3.4 | 3.7 | 3.7 | 3.7 | 3.8 | 3.9 | 4.0 | 4.2 | 4.2 | 4.2 | 3.9 |

| | label | mrv-latest |
|---|--:|--:|
| peak, log10 alive (median) | 5.2 | 4.2 |
| depth of the peak (median) | 11 | 15 |
| branching per read, first reads | 9–10 | 3.5–4 |
| branching falls below 1 from depth | 10 | 11 |
| combinations where a descent reached a valid leaf | 97 of 256 | 179 of 256 |
| log10 complete relations where reached (median) | 4.7 | 4.2 |
| seconds per combination (50 descents) | 27 | 15 |

The branching factor stays above 1 for the first ten reads in either order: the
checks that prune — predicates, cycles, coherence at a location — need several
reads decided before they can fail. By then 10^4–10^5 partial relations are
alive, and after it the tree narrows only slowly. The complete relations
remaining are almost all coherent (S10: 139 of 139 sampled), so the count is
roughly rcu-2's executions per combination: 10^4–10^5, matching S13's estimate
of 4.9×10^4.

### Why choices are rejected

| reason | label | mrv-latest |
|---|--:|--:|
| predicates unsatisfiable | 56.0% | 59.1% |
| rhb cycle | 16.1% | 21.5% |
| coherence prune | 25.4% | 19.2% |
|   of which `hb;eco ∪ hb` irreflexive | 22.3% | 16.6% |
|   of which rmw atomicity | 3.1% | 2.6% |
| Init when another write exists | 2.5% | 0.3% |
| rejections counted | 882,793 | 773,662 |

Where the coherence prune fires (share of all rejections, label order):
`rrcu[1]` 19.5%, `rC` 2.1%, `rrcu[0]` 1.6%, every other location under 1%.
In mrv-latest order `rrcu[0]` and `rrcu[1]` take 6.1% and 8.0%. It is the RCU counters: their writes are release stores and
their reads the polls of `sync`, and a read of a counter value that `hb`
already orders past is the stale read smrd forbids (S10(d) found the same).

## rcu-2, step counter 2: every tenth combination, 438 kinds, 30 descents each

The read-from choice product is 10^24.0 here.

| | label | mrv-latest |
|---|--:|--:|
| peak, log10 alive (median) | **6.1** | **3.9** |
| depth of the peak (median) | 12 | 12 |
| branching per read, first reads | 13 | 3.2 |
| combinations where a descent reached a valid leaf | 26 of 438 | 77 of 438 |
| log10 complete relations where reached (median) | 5.2 | 4.2 |
| seconds per combination | 125 | 33 |

Median log10 alive, every other depth:

| depth | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| label | 2.2 | 3.5 | 4.6 | 5.5 | 5.9 | 6.1 | 5.9 | 5.6 | 5.1 | 4.7 | 4.7 |
| mrv-latest | 1.1 | 2.1 | 2.7 | 3.3 | 3.7 | 3.9 | 3.8 | 3.7 | 3.8 | 4.0 | 3.6 |

Few descents reach a leaf at this depth — the tree is deep (median 24 reads)
and most descents die late — so the leaf estimate rests on 26 and 77
combinations. The label run shared the machine with a 16-thread S19 run for
most of its 2h09, which inflates its seconds but not its counts.

## The corpus's largest

| program | combinations | log10 choice product | peak log10 alive | valid leaves |
|---|--:|--:|--:|--:|
| 3.2W | 27 | 2.9 | 2.2 at depth 6 | 10^2.2 |
| jctc/JCTC11 | 864 | 0.3 | 0.3 | ~1 |
| avoidoota/listing15 | 2,200 | 0.3 | 0 | ~1 |

The litmus tests' searches are a handful of nodes: their cost is in the number
of combinations (S4, S11), not in any one combination's search. rcu-2 is the
other way round, which is why S19's per-combination query is what changes it.

## What this means

- **Enumerating rcu-2's executions is bounded by how many there are**, about
  10^4–10^5 per combination at step counter 1, not by the pruning. Sharper
  checks move the peak by an order of magnitude at most; they cannot remove
  the executions themselves.
- **For the futures, enumeration is the wrong question:** each combination
  needs one witness or a proof of none (S14), which S19 gives in a median
  of under a second.
- **Where enumeration is still used** — listing executions, other models —
  decide the most constrained read first (mrv-latest): 10–100× fewer nodes.
