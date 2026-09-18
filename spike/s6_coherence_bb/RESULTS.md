# S6: branch and bound over coherence orders (#18)

**Verdict: sound where expected, and slower everywhere. Do not productize as
R9b.** Pruning partial coherence orders gives the exhaustive search's answers
exactly, for every model whose violations grow with `co`. That is 28 of the 29
registered models, and the 29th, od-lso, is the one the argument predicts
fails. But it costs more than it saves at every threshold tried. MoRDor's
per-location write sets are too small for a prune to save more leaves than the
partial check costs.

Run from the repo root, one litmus file at a time:

    dune exec spike/s6_coherence_bb/s6_coherence_bb.exe -- FILE

## What was built

`try_all_coherence_orders` (`coherence.ml`) chooses a permutation of the writes
at each location, one location at a time, and checks the model once per
complete choice, at a leaf. Behind `MORDOR_S6_PRUNE`, it also checks the model
on the partial order built so far, at the root (no edges) and after each
location but the last. When the model rejects a partial order, the subtree is
dropped. An order is admitted only at a leaf, on all of it, as the issue's
note asks. With `MORDOR_S6_MIN_LEAVES=K`, a partial order is checked only when
at least `K` complete orders extend it.

The harness runs the pipeline to its executions once. It then asks every
registered model about every execution three times: exhaustive, pruned,
exhaustive again. It compares the pruned answers with the exhaustive ones, the
verdict and the admitting coherence order both, and times the pruned pass
against the second exhaustive pass, when the solver's caches are equally warm.

## Soundness: violations grow with co

Pruning is sound for a model when rejecting a partial order means rejecting
every order that extends it: the model's violations only grow as `co` grows.
Reading the axioms:

- **Monotone.** Every axiom that is an acyclicity or irreflexivity over
  relations built from `co` by union and composition, including `fr = rf⁻¹;co`
  and `eco`. That covers IMM, RC11/rc11c/rc17/rc11z, sMRD/MRD, undefined, SC,
  VBD and the TSO family, coherence, RA/SRA, POCausal, and PC, whose views must
  respect `co`, so more of it only makes a view harder to find. `Vocab.co` only
  adds edges from the initial write.
- **Not monotone.** od-lso's C++11 release sequence removes `coe;coe` from the
  release sequence's head. More `co` can shrink `rs`, and so `sw` and `hb`, and
  remove a violation.
- **Not searched.** The models with `uses_co = false` (local, slow, PRAM,
  causal, WRA, CC and the session models) are asked once with no `co`.

Measured over 414 programs (the 7 largest time out in the pipeline), 20,050
executions × 29 models:

| | |
|---|--:|
| answers compared | 581,450 |
| differing, 28 monotone models | **0** |
| differing, od-lso | 17 executions in 8 files, all C++ release-sequence tests (`mp-rs-*-est*`, `mp-rs-st-eadd*`, `c20/rs-example`, `RS17`) |

A pruned search visits the leaves the exhaustive one does, in the same order,
less the dropped subtrees. So where it is sound it returns the same first
admitting order, not only the same verdict.

## Speed: slower at every threshold

All models, all executions:

| | exhaustive | pruned | ratio |
|---|--:|--:|--:|
| 414 programs | 239.5s | 310.8s | **1.30** |

The 40 slowest programs (`3.2W` alone is 45% of the time):

| check a partial order when it has at least | exhaustive | pruned | ratio | leaf checks | partial checks | pruned |
|---|--:|--:|--:|--:|--:|--:|
| 1 leaf (every node) | 202.7s | 262.5s | 1.30 | 357,149 → 262,749 | 533,554 | 39,117 |
| 2 leaves | 213.7s | 248.8s | 1.16 | → 269,045 | 308,518 | 32,821 |
| 4 leaves | 220.8s | 236.8s | 1.07 | → 312,469 | 153,447 | 11,170 |
| 16 leaves | 199.4s | 200.7s | 1.01 | unchanged | 0 | 0 |

No subtree on the corpus has 16 leaves. Pruning removes about a quarter of the
leaf checks and adds one or two partial checks for each leaf saved. A partial
check is a whole `check_coherence` on a smaller `co`, so it costs about what a
leaf does. S4 (#13) predicted this: at most 5 writes and 6 permutations at any
one location, and the cost is in the number of locations.

## Answers

1. **Identical verdicts?** Yes, for every model whose violations grow with
   `co`: 0 differences in 561,400 answers. Not for od-lso, whose C++11 release
   sequence makes `hb` shrink as `co` grows. The violation-monotonicity argument
   (plan §2.2) holds on real models, with that one exception, which Phase 3 has
   to carry: a model has to say whether it is monotone, and od-lso is not.
2. **Faster?** No. It is 1.07× to 1.30× slower, depending on how large a
   subtree has to be before it is checked.
3. **R9b?** Not as specified. Replacing the permutation search with this is a
   regression on every corpus measured. Branch and bound pays only when a
   partial check is much cheaper than a leaf, and that needs the axioms
   evaluated incrementally over the edges one location adds: the delta form of
   `INCREMENTAL_MODEL.extend` (R9, #29), which is Phase 3 work, not a
   standalone win for the classic pipeline.

The flag stays in `coherence.ml`, off by default, so the experiment can be
rerun. It costs nothing when off: the leaf table it needs is lazy.
