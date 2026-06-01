# Promising-semantics litmus tests (reference only)

These litmus tests are drawn from the Promising-semantics line of work
(Kang et al., *A Promising Semantics for Relaxed-Memory Concurrency*, POPL 2017,
and follow-ups). Their `allow`/`forbid` assertions are annotated `[Promising]`
and encode the outcome **expected under promising semantics**.

## Why they live here and not in the test suite

**MoRDor does not implement promising semantics.** Promising is an *operational*
model: a thread may *promise* a future write, other threads may read from it, and
the promise is only legal if the promising thread can be *certified* to fulfil it
by running thread-locally. Consistency is defined over execution traces with a
message memory plus per-thread timestamp views — not over a static `(rf, co)`
graph.

MoRDor's coherence checker is, by contrast, axiomatic and post-hoc: given one
already-fixed execution and an enumerated coherence order, it checks
irreflexivity/acyclicity predicates (see `src/coherence.ml`). There is no place
in that contract for promise sets, certification, or views, and
`symbolic_execution` carries no such state. MoRDor's dependency/justification
machinery (MRD / Symbolic MRD) is the project's deliberate *alternative* to
promises.

A registry entry once aliased the model name `"promising"` to the IMM checker.
That was misleading — running these tests under that alias verified them under
**IMM, not promising** — so the alias has been removed. A `[Promising]`
annotation is now reported as an unknown model with a warning, and no coherence
model is applied.

These files are therefore kept here **as reference only**. They are *not* scanned
by the integration suite (which scans `litmus-tests/`). To verify them under
their intended semantics, use a tool that implements promising semantics.

## Runnable approximations

Copies of these tests reannotated to `[IMM]` live in
`litmus-tests/popl_promising/` and *are* exercised by the integration suite. IMM
was chosen because it is the closest model MoRDor implements and was the model the
old `"promising"` alias used.

**IMM is not promising semantics.** Where the two models disagree — notably on
thin-air reads and load-buffering shapes with dependencies — the IMM verdict for
the reannotated copy may legitimately differ from the `[Promising]` expectation
recorded here. Treat the IMM copies as an IMM check, and these originals as the
record of the intended promising outcome.

## Files

| File | Promising expectation |
|------|-----------------------|
| `SB.lit`               | allow  `r1=0 ∧ r2=0` |
| `SB+fences.lit`        | forbid `r1=0 ∧ r2=0` |
| `LB.lit`               | allow  `r1=1 ∧ r2=1` |
| `LBa.lit`              | forbid `r1=1` |
| `LBa'.lit`             | allow  `r2=2` |
| `LBaa/LBa'0.lit`       | allow  `r1=2` |
| `LBaa/LBa'1.lit`       | allow  `r1=2` |
| `LBd.lit`              | forbid `r1=1` |
| `LBfd.lit`             | allow  `r1=1 ∧ r2=1` |
| `LBr.lit`              | forbid `r1=1` |
| `MP+fences.lit`        | forbid `r1=1 ∧ r2=0` |
| `COH.lit`              | forbid `r1=2 ∧ r2=1` |
| `CYC.lit`              | forbid `r1=1 ∧ r2=1` |
| `2+2W.lit`             | allow  `r1=2 ∧ r2=2` |
| `ARM-weak.lit`         | allow  `r1=1` |
| `Par-Inc.lit`          | allow  `r1=1 ∨ r2=1` |
| `Upd-Stuck.lit`        | allow  `r1=1 ∧ r2=0` |
| `Page 7 Column 1.lit`  | forbid `r1=1 ∧ r2=0 ∧ r3=1 ∧ r4=0` |
| `Page 7 Column 1b.lit` | forbid `r2=3 ∧ r3=0` (release sequence) |
