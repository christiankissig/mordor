# Litmus tests parked for review

Tests whose assertion MoRDor does not currently validate, held out of the
integration suite until the divergence is either fixed or explained.

The suite (`dune exec test/test_integration.exe`, and the `Litmus Tests` CI
workflow) scans `litmus-tests/` and fails on any assertion MoRDor does not
validate, so a test that records a known divergence cannot live there. Parking it
here keeps the file, its assertion and its provenance intact while the suite
stays a statement about what MoRDor does today.

This is the same idea as `litmus-tests-promising/`, `litmus-tests-cpp/` and
`litmus-tests-ra/`, but for a different reason: those name a memory model MoRDor
has no implementation of, so their assertions cannot be checked at all. Every
test here names a model MoRDor *does* implement, and gets a different answer from
the one the literature records.

Directory layout mirrors `litmus-tests/`, so a file's origin is its path.

## How these were found

Until 2026-09-06 the suite was green on every one of these. Three
over-approximations in the assertion checker made an assertion pass without being
decided, and each one hid a class of them:

1. `forbid` short-circuited to valid before any execution was looked at, so every
   `forbid` in the repository passed for free.
2. The solver query omitted the execution's own path predicates, so a condition
   an execution's values contradict still came back satisfiable. That made
   `forbid` too strict and `allow` too permissive at once.
3. A set-membership test named an event the execution does not run was answered
   rather than skipped.

With all three fixed the suite decides these assertions for the first time, and
these are the ones it decides against. **Nothing here is a regression** — it is
the first honest reading.

## Contents

### Parked earlier

| Test | Note |
|---|---|
| `jctc/JCTC6.lit` | Needs Lifting to pair justifications under complementary guards; `find_distinguishing_predicate` returns `None` because the else-path predicate carries an extra conjunct. Pending #36. |
| `symmrd/LB+UB+data+z.lit` | Moved here in `a075ff9` ("consider initial event in dslwb"), which records no reason. |
| `avoidoota/listing10.lit` | A stray nested copy asserting `allow ((2,3) ∉ .dp)` — the negation of `avoidoota/listing11.lit` on the same program. It passed only because the membership test was answered for an execution that does not run event 2. |

### MoRDor is too permissive — a `forbid` it finds a witness for

| Test | Assertion | Model |
|---|---|---|
| `avoidoota/additional_nonlb.lit` | forbid `@x=42 ∧ @y=42 ∧ @z=42` | sMRD |
| `avoidoota/listing16.lit` | forbid `r1=17 ∧ r2=17 ∧ r3=17` | sMRD |
| `avoidoota/listing19.lit` | forbid `r1=17 ∧ r3=17 ∧ r5=17` | sMRD |
| `avoidoota/listing27_forbid.lit` | forbid `r1=1 ∧ r2=1` | sMRD |
| `jctc/JCTC12.lit` | forbid `r1=1 ∧ r2=1 ∧ r3=1` | sMRD |
| `own/ORI.lit` | forbid `r3=42 ∧ r1=1` | sMRD |
| `own/ORI2.lit` | forbid `rk=42 ∧ ra=1` | sMRD |
| `on_thin_air_reads19/P5.lit` | forbid `r1=1` | `[JR]` → sMRD |
| `esop_problem/lb+ctrldat+ctrl-single.lit` | forbid `r1=42 ∧ r2=42` | `[Problem]` → sMRD |
| `popl_bubbly/LB+deps.lit` | forbid `r1=42 ∧ r2=42` | `[Bubbly]` → sMRD |
| `popl_bridging/Preserving detour.lit` | forbid `r1=1 ∧ r2=1 ∧ r3=1` | `[Bridging]` → IMM |
| `sevcik_thesis/Skip/LB+locks.lit` | forbid `r1=1 ∧ r2=1` | `[Sevcik]` → sMRD |
| `popl_promising/Page 7 Column 1b.lit` | forbid `r2=3 ∧ r3=0` | `[IMM]` |
| `rmm-zoo/properties/atomicity-mca/MP+fence+addr.lit` | forbid `r1=1 ∧ r2=0` | `[Power]` → IMM |

Most of this group is out-of-thin-air: the `avoidoota` listings, `JCTC12`, `P5`,
`ORI`/`ORI2` and the load-buffering shapes are all asking that a value not be
justified by a cycle through its own dependencies. `no_oota` is the property MRD
exists to deliver, so these are the load-bearing ones.

`MP+fence+addr.lit` is different in kind and is the sharpest single case:
message passing with a fence on the writer and an address dependency on the
reader. Every model with fence ordering forbids it — the zoo carries it as a
*positive control*, the shape only a bare coherence checker allows — and MoRDor
allows it under IMM. The two release-acquire controls with the same character,
`MP+rel+acq` and `WRC+rel+acq`, are in `litmus-tests-ra/` because they also name
an unimplemented model; see that README. Fence and release-acquire ordering in
the checker is the common thread and the place to start.

### MoRDor is too restrictive — an `allow` it finds no witness for

| Test | Assertion | Model |
|---|---|---|
| `jctc/JCTC2.lit` | allow `r1=1 ∧ r2=1 ∧ r3=1` | sMRD |
| `jctc/JCTC3.lit` | allow `r1=1 ∧ r2=1 ∧ r3=1` | sMRD |
| `jctc/JCTC9b.lit` | allow `r1=1 ∧ r3=1` | sMRD |
| `jctc/JCTC19.lit` | allow `r1=42 ∧ r2=42 ∧ r3=42` | sMRD |
| `jctc/JCTC20.lit` | allow `r1=42 ∧ r2=42 ∧ r3=42` | sMRD |
| `esop_problem/RRE.lit` | allow `r1=42 ∧ r2=42 ∧ r3=42` | `[Problem]` → sMRD |
| `popl_grounding/FADD.lit` | allow `r1=1 ∧ r3=1` | `[Grounding]` → IMM |
| `pldi_repairing/LB.lit` | allow `r1=1 ∧ r2=1` | `[RC11]` |
| `popl_promising/Upd-Stuck.lit` | allow `r1=1 ∧ r2=0` | `[IMM]` |

These generate executions — `JCTC19` gets 8, `Upd-Stuck` 248 — but none whose
path predicates admit the asserted values. Before the path predicates were part
of the query the outcome was reported satisfiable against an execution that does
not produce it, which is why the group was invisible.

The `JCTC2`/`JCTC3` and `JCTC19`/`JCTC20` pairs are worth taking together: both
pairs are the same shape asked twice, and both halves fail, so whatever is
missing is in the shape rather than in one file's annotation. Check the step
counter first — it defaults to 2 and is shared by every loop in a program — before
concluding the justification is not derivable.

## Getting one back into the suite

Fix the divergence, or determine that the reference verdict does not apply to
sMRD and rewrite the assertion to say what MoRDor does with the reference verdict
recorded in the header comment — the convention `litmus-tests/rmm-zoo/README.md`
describes as "assertions state what MoRDor does, comments state what the
literature says". Then `git mv` it back under `litmus-tests/` and add it to
`litmus-tests/INDEX.md`.
