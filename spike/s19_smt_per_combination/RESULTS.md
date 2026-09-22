# S19: one SMT query instead of a combination's enumeration (#96)

**Verdict: go for R16 (#102) — and it is what R13 (#99) should be built on.**
One solver query per justification combination decides whether it has a
coherent execution, exactly where the answer is yes (the witness is checked by
the real validation and smrd) and soundly where it is no. It agrees with
enumeration on all 15,106 combinations of the corpus. On rcu-2 it computes
what nothing else could: at step counter 1 every one of the 256 kinds in 50
seconds, and **at step counter 2 — the program as written — 2,860 of 2,916 in
18 minutes on 16 threads, giving 1,956 futures.** The remaining 56 are
undecided, not wrong: every failed attempt on them fails for the one part of
smrd the encoding leaves out, its release/acquire edges.

Run from the repo root (off by default):

    MORDOR_S19=1 dune exec mordor -- futures --threads 16 \
      --step-counter-per-loop 2 --single programs/rcu-2.lit \
      --output-mode json --output-file futures.json
    # also return k checked witnesses per combination, so later stages run:
    MORDOR_S19_WITNESSES=1 ...
    # compare with enumeration, per combination (only for small programs):
    MORDOR_S19_COMPARE=1 ...

`MORDOR_S19` makes `Freeze.enumerate` decide each combination by asking the
solver instead of enumerating. With `MORDOR_S19_WITNESSES=k` it returns up to k
distinct checked witnesses, and the rest of the pipeline — deduplication,
coherence, futures — runs on them; with `k = 0` (the default) it returns none.
`MORDOR_S19_ROUNDS` bounds the refinement loop (default 20);
`MORDOR_S19_ONLY=<file>` restricts it to the combinations whose key prefixes the
file lists. Each combination prints its key, verdict, rounds, time and why
failed rounds failed. The coherence model is smrd on both sides: the witness
check and the enumeration's prune use smrd whatever the program names, since
the encoding is smrd's.

## The encoding

For one combination, over its reads R and each read's candidate writes W(r)
after `rf_search`'s static filters, as MoRDor expressions handed to
`Solver.quick_solve`:

| part | constraint |
|---|---|
| choice | a selector `s_r` per read, one of W(r); Init only when it is the only candidate (`check_partial`'s rule) |
| values and locations | `s_r = w ⇒ val(w) = val(r) ∧ loc(w) = loc(r)` — `ReadFromValidation.env_rf` and `check_rf` for that one edge |
| predicates | the combination's `p_combined` |
| rhb acyclic | a rank per event: `rank(a) < rank(b)` for `dp ∪ ppo`, `s_r = w ⇒ rank(w) < rank(r)` |
| co | a position per write, distinct among writes to the same location, Init at 0; a read's position is its write's |
| coherence | for every `(a, b)` in `hb₀ = (dp ∪ ppo)⁺` at the same location: not `eco(b, a)`, where `eco(x, y)` is `pos(x) < pos(y)`, or `x` is the write `y` reads |
| atomicity | for every rmw `(r, w)` and write `x` at `r`'s location: not `pos(r) < pos(x) < pos(w)` |

With `co` a total order on each location's writes, `eco = (rf ∪ co ∪ rb)⁺`
has exactly that positional form, so the coherence and atomicity constraints
are smrd's axioms. `hb₀` leaves out smrd's release/acquire edges
(`[W_rel];rf;[R_acq]`), so it is a subset of smrd's `hb`: the constraints are
weaker than smrd's, never stronger. Allocation atomicity and disjointness,
which `instantiate_execution` adds, are left out for the same reason.

**The whole encoding is therefore a necessary condition** for a coherent
execution: every coherent execution satisfies it. So:

- **unsatisfiable ⇒ the combination has no coherent execution;**
- satisfiable ⇒ decode the selectors into a read-from, and check it exactly —
  `instantiate_execution`, then smrd. If it passes, that is a witness. If not,
  block that read-from and ask again: a counterexample-guided loop, up to
  `MORDOR_S19_ROUNDS` times, after which the combination is *unknown*.

## The corpus: 375 programs, compared with enumeration

Every combination of the 333 golden programs plus litmus-tests-cpp and -jmm
(`--allow-unknown-model`), each decided both by the solver and by a
first-witness enumeration under smrd:

| solver / enumeration | combinations |
|---|--:|
| sat / exists | 10,616 |
| unsat / none | 4,490 |
| **disagreements** | **0** |
| unknown | 0 |

- 15,022 were decided in one round, 11 needed two or three; 73 at round 0
  (a read with no candidate write).
- Solver 5 ms a combination (median; p99 13 ms, max 0.64 s); enumeration is
  faster still on these, where there is almost nothing to enumerate.
- A first run compared the solver's smrd against each program's own model and
  found 3 disagreements, all under the model `coherence`, which has no
  atomicity axiom (`CAS-both+rel+acq`, `RS17`): the encoding is smrd's, and
  stronger than a model without atomicity. Under smrd on both sides, none.

## rcu-2

| | step counter 1 | step counter 2 |
|---|--:|--:|
| kinds of combination | 256 | 2,916 |
| **coherent execution (checked witness)** | **224** | **1,956** |
| **no coherent execution** | **32** | **904** |
| undecided after 50 rounds | 0 | 56 (34 after 200 rounds, below) |
| solver seconds per kind: median / p90 / max | 0.21 / 0.66 / 1.5 | 0.83 / 6.2 / 44 |
| unsat, median | 0.06 | 0.25 |
| constraints per kind, median | 2,005 | 3,168 |
| threads | 3 | 16 |
| wall, including elaboration | 50 s | 18m15 |
| peak memory | 0.76 GB | 6.6 GB |
| futures | 224 | **1,956 (1,966 with the rerun below)** |

The step-counter-1 verdicts match S15 combination by combination: all 216 of
S15's witnesses are satisfiable here, and all 8 combinations S15 searched to
the end without one are unsatisfiable here, confirmed independently. Of the 32
S15 left out of budget, 8 are satisfiable and 24 have no coherent execution —
beyond reach of any search short of exhausting them.

Most satisfiable kinds need more than one round: at step counter 2, 780 in one,
399 in two, 224 in three, a long tail beyond. A decoded read-from can pass the
encoding and fail the exact check, because the encoding leaves out what the
check adds.

### The 56 undecided kinds: smrd's release/acquire edges

Rerunning only the 56 (`MORDOR_S19_ONLY`), with each failed round's reason
recorded (`rcu2_sc2_undecided.txt`):

| failed rounds | reason |
|--:|---|
| 2,537 | incoherent: `hb;eco ∪ hb is irreflexive`, at `rrcu[0]` or `rrcu[1]` |
| 0 | invalid (rejected by `instantiate_execution`) |

Every failed round fails the same axiom at the RCU counters. Those are written
with release stores (`:vrel=`) and read around the acquire/release `fadd` and
`cas` on `rC`, so smrd's `hb` gains release/acquire edges there that `hb₀`
leaves out. The solver keeps proposing read-froms that are coherent without
those edges and incoherent with them. 7 of the 56 found a passing witness on
this rerun (the solver's models differ from run to run), leaving 49.

Closing them means putting `sw = [W_rel];rf;[R_acq]` into the encoding's `hb`.
Its edges depend on the selectors, so `hb` becomes a closure over conditional
edges; with the few candidate `sw` edges rcu-2 has, a reachability relation
between them (K×K Booleans for K candidate edges) is enough. That is R16's
work, and it would also cut the rounds the satisfiable kinds need.

A third run of the 56 with 200 rounds and witnesses returned
(`rcu2_sc2_undecided_witnesses.txt`) settled 22 more: 10 satisfiable, each a
new future, and 12 unsatisfiable. Those 12 became unsatisfiable only once every
read-from the solver proposed had been checked, failed and blocked — sound,
since a read-from is blocked only after the real validation or smrd rejects it.
34 remain undecided, at a median 190 s each (45 minutes on 16 threads, shared
with S17).

**rcu-2 at step counter 2 therefore has between 1,966 and 2,000 futures under
smrd.** The 1,966 found, all distinct, are in `rcu2_sc2_futures_all.txt.gz`
(one per line, in the CLI's tuple notation; not committed, 3.7 MB, regenerated
by the runs above). `rcu2_sc2_futures.json.gz` is the first run's own output,
1,956 of them.

## What this means

- **R16 (#102): build it.** The encoding above is the prototype; it lives in
  `Freeze.enumerate` behind `MORDOR_S19`, about 250 lines.
- **R13 (#99): take witnesses from the solver.** With S14's rule — a witness's
  read-from must not also be valid for a dominating combination, checked
  after decoding and blocked if it is — this gives the futures directly. On
  rcu-2 no combination is dominated, and the 1,956 futures above are that
  computation.
- **The undecided kinds are the encoding's to close**, by adding what it
  leaves out, rather than by more rounds.
- **R14 (#100)** can list a checked witness per future, and more per future by
  blocking and asking again (S16 did that at 5 per kind).
