# C/C++ litmus tests (reference only)

These litmus tests carry `[C11]`, `[C17]` or `[C20]` assertions and encode the
outcome **expected under the corresponding revision of the C/C++ memory model**
(ISO/IEC 14882:2011, :2017, :2020). They are vendored from the Relaxed Memory
Model Zoo — <https://rmm-zoo.kissig.org> — mostly from its
`litmus/cpp_memory_model/rs/` set, which in turn comes from
`gonzalobg/cpp_memory_model`.

## Why they live here and not in the test suite

**MoRDor does not implement the C/C++ memory model.** `ModelRegistry` in
`src/coherence.ml` registers `imm`, `rc11`, `rc11c`, `smrd` and `undefined`, and
`model_options_table` in `src/context.ml` maps the model names a litmus test may
name onto those. `C11`, `C17` and `C20` appear in neither.

An unrecognised name used to warn and carry on, leaving the coherence model at
whatever it already was — the `smrd` default. Running one of these files did
produce a verdict, but it was **sMRD's verdict, not C11's**, and comparing it
against a `[C11]` expectation compares two different models. That is what kept
these tests in the scanned suite: while `forbid` assertions were passing without
being checked at all, the mismatch was invisible.

Since #86 it is a hard error:

```
$ mordor run --single models/cpp-release-sequences/mp-rs-strel.lit
Error: Unknown memory model "c11". MoRDor implements imm, rc11, rc11c and smrd,
and maps a further set of names onto those; this one is in neither, so no
coherence model can be applied. Re-run with --allow-unknown-model to check the
test under the model already in effect instead -- the verdict is then that
model's, not "c11"'s.
```

The `sMRD fallback` column below is measured with `--allow-unknown-model`.

`RC11` *is* implemented (`rc11`, and `rc11c` with consume), and RC11 is the
repaired C11 of Lahav et al. (PLDI 2017). It is close to but not the same as any
of C11/C17/C20 — in particular the release-sequence definitions these tests
discriminate between are exactly where the revisions differ from each other.
Reannotating to `[RC11]` would therefore be a different test, not the same one.

These files are kept here **as reference only**. They are *not* scanned by the
integration suite, which scans `litmus-tests/`. To exercise them, either
implement a C11/C17/C20 coherence model and register it, or use a tool that has
one (cppmem, herd7's C11 model, Cerberus-BMC).

## Files

Reference verdicts are from the zoo and the standards; the `sMRD` column records
what MoRDor reports when the unknown-model fallback puts the file through the
sMRD checker, which is *not* an answer to the question the file asks.

### `models/cpp-release-sequences/`

The release-sequence family. Sources: ISO/IEC 14882:2011, :2017, :2020; Boehm,
Giroux & Vafeiadis P0668R5 (2018); Boehm P0982R1 (2018). The fourteen files cover
the zoo's sixteen upstream tests: two pairs are the same program under opposite
conditions (`mp-rs.cpp11`/`mp-rs.cpp17.undef`, `mp-rs-add-st.cpp11`/`.cpp17.undef`)
and two more differ only in which disjunct they ask about
(`mp-rs-st-eadd-atomics`), plus `RS+cpp20.lit` from the zoo's C++20-vs-C11 edge.

| Test | Asserts | C++11 | C++17 | C++20 | sMRD fallback |
|---|---|---|---|---|---|
| `mp-rs.lit` | allow `r1=2 ∧ r2=0` | forbid | allow* | allow* | allows |
| `mp-rs-strel.lit` | forbid `r1=2 ∧ r2=0` | forbid | forbid | forbid | **forbids** |
| `mp-rs-add.lit` | forbid `r1=2 ∧ r2=0` | forbid | forbid | forbid | allows |
| `mp-rs-eadd.lit` | forbid `r1=2 ∧ r2=0` | forbid | forbid | forbid | allows |
| `mp-rs-est.lit` | allow `r1=2 ∧ r2=0` | allow* | allow* | allow* | allows |
| `mp-rs-add-eadd.lit` | forbid `r1=3 ∧ r2=0` | forbid | forbid | forbid | allows |
| `mp-rs-add-est-atomic.lit` | allow `r1=3 ∧ r2=0` | allow | allow | forbid | allows |
| `mp-rs-add-est.lit` | allow `r1=3 ∧ r2=0` | allow* | allow* | allow* | allows |
| `mp-rs-add-st.lit` | allow `r1=3 ∧ r2=0` | forbid | allow* | allow* | allows |
| `mp-rs-st-eadd-atomics.lit` | allow `(r1=2 ∨ r1=4) ∧ r2=0` | forbid | allow | forbid | allows |
| `mp-rs-st-eadd.lit` | allow `r1=3 ∧ r2=0` | allow* | allow* | allow* | allows |
| `mp-rs-st-est-atomics.lit` | allow `r1=3 ∧ r2=0` | allow | allow | forbid | allows |
| `mp-rs-st-est.lit` | allow `r1=3 ∧ r2=0` | forbid* | allow* | allow* | allows |
| `RS+cpp20.lit` | allow `r0=2 ∧ r1=0` | — | — | allow | allows |

`*` = the allowing model reports the execution as a data race.

The four `forbid` rows are the discriminating ones: a model without
release-sequence semantics allows all of them.

sMRD allowed all four when this table was first measured. It now forbids
`mp-rs-strel`, where both flag stores are releases: `4432a08` gave sMRD's `hb` a
synchronises-with edge, `sw = [W_rel];rf;[R_acq]`, so the acquire load of the
second release store is now ordered after the non-atomic write it publishes.
That is the one row where sMRD and the C++ reference agree, and it is the row
that does not need release *sequences* to decide -- a release store heads its own
sequence. The other three turn on what a *relaxed* store does to a sequence it is
appended to, which sMRD still has nothing to say about.

### Elsewhere in the zoo

| Test | Asserts | Reference verdict |
|---|---|---|
| `properties/atomicity-mca/IRIW+scfences.lit` | allow `r1=1 ∧ r2=0 ∧ r3=1 ∧ r4=0` | C11/C++17 allow; **RC11/C++20/SC forbid** — the SC-fence defect P0668 repaired |
| `properties/global-transformations/thread-inlining/opt.lit` | allow `r1=1 ∧ r2=0` | thread-inlining pair, optimised side |
| `properties/global-transformations/thread-inlining/src.lit` | allow `r1=1 ∧ r2=0` | thread-inlining pair, source side |
| `properties/reasoning-guarantees/external-drf/MP+rlx-race.lit` | allow `r1=1 ∧ r2=0` | the racy witness for external DRF |

The `thread-inlining` and `external-drf` entries are refinement pairs and
property witnesses rather than model-discrimination tests; they moved with the
`[C11]` annotation they were written under. Reannotating them to a model MoRDor
implements would make them runnable again — the shapes themselves are not
C11-specific.

## See also

`litmus-tests/rmm-zoo/README.md` for the coverage analysis these tests were
added for, and `litmus-tests-ra/` for the release-acquire family, which is out of
the suite for the same reason.
