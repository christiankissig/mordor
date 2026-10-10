# Promising-semantics litmus tests

These litmus tests are drawn from the Promising-semantics line of work
(Kang et al., *A Promising Semantics for Relaxed-Memory Concurrency*, POPL 2017,
and follow-ups). Their `allow`/`forbid` assertions are annotated `[PS1]` and
encode the outcome **expected under promising semantics 1.0**.

## Running them

MoRDor computes promising semantics 1.0 (POPL 2017) and 2.0 (Lee et al., PLDI
2020); see `src/promising.ml`. A `[PS1]` or `[PS2]` annotation selects its
version the way `[IMM]` selects a coherence model, so these run as they are:

```
dune exec mordor -- run --single "litmus-tests/promising/LB.lit"
```

`--semantics ps1` or `--semantics ps2` chooses a version for a whole run, and
takes precedence over the annotation: `--semantics ps2` checks these tests
under PS2.0. A bare `[Promising]` names no version and is an error unless
`--semantics` chooses one.

Promising is an *operational* model: a thread may *promise* a future write,
other threads may read from it, and the promise is only legal if the promising
thread can be *certified* to fulfil it by running thread-locally.

The integration suite scans this directory as part of `litmus-tests/`, and
`test/test_promising.ml` checks the papers' verdicts for most of these tests
under both versions. All of them hold under both.

A registry entry once aliased the model name `"promising"` to the IMM checker,
which verified these tests under IMM, not promising; that alias is gone.

Two files were left behind in `litmus-tests/popl_grounding/` when the rest moved:
`CYC.lit`, byte-identical to the copy already here and so simply deleted, and
`Coh-CYC (Promising).lit`, moved here. `popl_grounding/` keeps
`Coh-CYC (Soham).lit`, the same shape annotated `[sMRD]`.

## Runnable approximations

Copies of these tests reannotated to `[IMM]` live in
`litmus-tests/popl_promising/` and are exercised by the integration suite too,
all except `Coh-CYC (Promising).lit`, which has none. `Page 7 Column 1b.lit`'s copy
was parked in `litmus-tests-review/` (#61) until IMM stopped letting sMRD elide
the release store its own thread overwrites. IMM
was chosen because it is the closest model MoRDor implements and was the model the
old `"promising"` alias used.

**IMM is not promising semantics.** Where the two models disagree — notably on
thin-air reads and load-buffering shapes with dependencies — the IMM verdict for
the reannotated copy may legitimately differ from the `[PS1]` expectation
recorded here. Treat the IMM copies as an IMM check, and these originals as the
record of the intended promising outcome.

## Files

| File | Promising expectation | PS1.0 | PS2.0 |
|------|-----------------------|-------|-------|
| `SB.lit`               | allow  `r1=0 ∧ r2=0` | allow | allow |
| `SB+fences.lit`        | forbid `r1=0 ∧ r2=0` | forbid | forbid |
| `LB.lit`               | allow  `r1=1 ∧ r2=1` | allow | allow |
| `LBa.lit`              | allow  `r1=1` — **see below** | allow | allow |
| `LBa'.lit`             | allow  `r2=2` | allow | allow |
| `LBaa/LBa'0.lit`       | allow  `r1=2` | allow | allow |
| `LBaa/LBa'1.lit`       | allow  `r1=2` | allow | allow |
| `LBd.lit`              | forbid `r1=1` | forbid | forbid |
| `LBfd.lit`             | allow  `r1=1 ∧ r2=1` | allow | allow |
| `LBr.lit`              | forbid `r1=1` | forbid | forbid |
| `MP+fences.lit`        | forbid `r1=1 ∧ r2=0` | forbid | forbid |
| `COH.lit`              | forbid `r1=2 ∧ r2=1` | forbid | forbid |
| `CYC.lit`              | forbid `r1=1 ∧ r2=1` | forbid | forbid |
| `2+2W.lit`             | allow  `r1=2 ∧ r2=2` | allow | allow |
| `ARM-weak.lit`         | allow  `r1=1` | allow | allow |
| `Par-Inc.lit`          | allow  `r1=2 ∨ r2=2` | allow | allow |
| `Upd-Stuck.lit`        | allow  `r1=1 ∧ r2=1` | allow | allow |
| `Page 7 Column 1.lit`  | forbid `r1=1 ∧ r2=0 ∧ r3=1 ∧ r4=0` | forbid | forbid |
| `Page 7 Column 1b.lit` | forbid `r2=3 ∧ r3=0` (release sequence) | forbid | forbid |
| `Coh-CYC (Promising).lit` | forbid `r1=3 ∧ r2=2 ∧ r3=1`, annotated `[PS1=allow]` — **see below** | forbid | forbid |

**LBa.** The file used to assert `forbid`, but the POPL 2017 paper (section
4.1) allows the outcome: "In the second variant (LBa), we allow the promise of
y := 1 and thus the a = 1 outcome", so that optimizations eliminating an
acquire read remain sound. It now asserts `allow`, which both versions confirm.
The IMM copy in `popl_promising/` still asserts `forbid`, as IMM
should.

**Coh-CYC.** The annotation says promising allows the outcome; both versions
here forbid it. Neither paper discusses this program. The outcome needs T2 to
promise `x := 3` before reading `y = 1` and T1 to promise `y := 1` before
reading `x = 3`; certifying either promise needs the other to be in memory
already, since certification writes `x := 2` after every existing message
(behind the cap) and reads nothing but its own write. Treat this row as open
until checked against another implementation.
