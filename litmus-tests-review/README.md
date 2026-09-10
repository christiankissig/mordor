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

Every file here has an issue in the #36, #41-#65 range. Each records the symptom, the model actually in
effect, where the test comes from and what to look at next. Seventeen files
remain; #41, #42, #44, #45, #47, #55, #56, #57 and #59 have been fixed and
their files returned to `litmus-tests/`.

The issues split two ways, and the split decides what is actionable. Only `smrd` and `rc11` are supported
models. Ten tests are checked under one of those, so a divergence is a defect and the issue is labelled
`bug`. The other ten name a model that is not — `[Problem]`, `[JR]`, `[Bubbly]` and `[Sevcik]` have a
`model_options_table` entry with `coherent = None` and so fall through to the `smrd` default, while
`[Bridging]`, `[Grounding]`, `[Power]` and `[IMM]` map to `imm`. Those are labelled `smrd-unsupported` and
carry no `bug` label: they compare one model's expectation against another model's verdict, and the two are
not claimed to agree, so a divergence there may be entirely correct. Each needs triaging as "does sMRD agree
with the reference on this shape?" before it is treated as a defect.

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
| [`jctc/JCTC6.lit`](jctc/JCTC6.lit) #36 | Lifting cannot pair the justifications of thread 2's two writes under complementary guards: `find_distinguishing_predicate` returns `None` because the else-path predicate carries an extra conjunct. |
| [`symmrd/LB+UB+data+z.lit`](symmrd/LB+UB+data+z.lit) #65 | Moved here in `a075ff9` ("consider initial event in dslwb"), which records no reason. |

`avoidoota/listing10.lit` #42 has left this table, and the description it
carried here was wrong on both counts. It is not a stray copy — it dates from
the first litmus commit, `8aa5b1a`, and `c1cdb61` merged it back to a review
path nested inside the scanned tree, which is what `0bca217` mistook for a
duplicate. And it is not the negation of `listing11.lit` on the same program:
`listing11` is the same program with **volatile** accesses, and the pair exists
to separate on exactly that. Both assertions are original and neither has ever
been changed. Volatile is now implemented (#83) and the membership test counts
an event elided by forwarding as run, so the two files disagree where they were
written to disagree.

### MoRDor is too permissive — a `forbid` it finds a witness for

| Test | Assertion | Model |
|---|---|---|
| [`avoidoota/listing16.lit`](avoidoota/listing16.lit) #43 | forbid `r1=17 ∧ r2=17 ∧ r3=17` | sMRD |
| [`jctc/JCTC12.lit`](jctc/JCTC12.lit) #48 | forbid `r1=1 ∧ r2=1 ∧ r3=1` | sMRD |
| [`on_thin_air_reads19/P5.lit`](on_thin_air_reads19/P5.lit) #54 | forbid `r1=1` | `[JR]` → sMRD |
| [`popl_bridging/Preserving detour.lit`](popl_bridging/Preserving detour.lit) #58 | forbid `r1=1 ∧ r2=1 ∧ r3=1` | `[Bridging]` → IMM |
| [`sevcik_thesis/Skip/LB+locks.lit`](sevcik_thesis/Skip/LB+locks.lit) #64 | forbid `r1=1 ∧ r2=1` | `[Sevcik]` → sMRD |
| [`popl_promising/Page 7 Column 1b.lit`](popl_promising/Page 7 Column 1b.lit) #61 | forbid `r2=3 ∧ r3=0` | `[IMM]` |
| [`rmm-zoo/properties/atomicity-mca/MP+fence+addr.lit`](rmm-zoo/properties/atomicity-mca/MP+fence+addr.lit) #63 | forbid `r1=1 ∧ r2=0` | `[Power]` → IMM |

Most of this group is out-of-thin-air: the `avoidoota` listings, `JCTC12`, `P5`
and the load-buffering shapes are all asking that a value not be justified by a
cycle through its own dependencies. `no_oota` is the property MRD exists to
deliver, so these are the load-bearing ones.

**Seven have left this table.** `avoidoota/additional_nonlb.lit` #41 was never
an out-of-thin-air finding at all: `@x` was the *location* variable rather than
the final value at it, because the lexer bound `@x` with the `@` still attached
and it never matched the key the memory state is built under. The three
locations were free symbols the solver could set to 42, so the `forbid` failed
however the analysis behaved (#84, #5).

**Six have left this table.** `avoidoota/listing27_forbid.lit` #45 went for a
different reason from the other five: it is `listing27_allow.lit` under a model
that does *not* exploit undefined behaviour, and `Interpret` applied the
`e / !r -> e` fold unconditionally, so the two files could not disagree.
`options.ubopt` says which models exploit UB; it was set by no one and read by no
one. It is now both.

**Five have left this table.** `own/ORI.lit` #55, `own/ORI2.lit` #56,
`avoidoota/listing19.lit` #44, `esop_problem/lb+ctrldat+ctrl-single.lit` #47 and
`popl_bubbly/LB+deps.lit` #59 are back in `litmus-tests/`. They shared one cause:
`ValueAssignElab` concretised a write value using a model of the path predicate
and discharged the whole predicate in the same step, so a guard that pinned the
value pinned it and then vanished, and `d` — rebuilt from what was left — no
longer held the read the value came from. MoRDor allowed `LB+deps` under sMRD,
MRD's headline no-thin-air example, on exactly that. Conjuncts that constrain the
write's own value are now retained. What remains in this table did not move, so
whatever those need, it is not this.

`MP+fence+addr.lit` is different in kind and is the sharpest single case:
message passing with a fence on the writer and an address dependency on the
reader. Every model with fence ordering forbids it — the zoo carries it as a
*positive control*, the shape only a bare coherence checker allows — and MoRDor
allows it under IMM. The two release-acquire controls with the same character,
`MP+rel+acq` and `WRC+rel+acq` (#67, #68), have since been fixed and are back in
`litmus-tests/rmm-zoo/`: sMRD's `hb` gained `sw = [W_rel];rf;[R_acq]`. That fix
does *not* reach this file, because a relaxed write po-after a release fence
still synchronises with nothing. Fence ordering in the checker is what is left.

### MoRDor is too restrictive — an `allow` it finds no witness for

| Test | Assertion | Model |
|---|---|---|
| [`jctc/JCTC2.lit`](jctc/JCTC2.lit) #50 | allow `r1=1 ∧ r2=1 ∧ r3=1` | sMRD |
| [`jctc/JCTC3.lit`](jctc/JCTC3.lit) #52 | allow `r1=1 ∧ r2=1 ∧ r3=1` | sMRD |
| [`jctc/JCTC9b.lit`](jctc/JCTC9b.lit) #53 | allow `r1=1 ∧ r3=1` | sMRD |
| [`jctc/JCTC19.lit`](jctc/JCTC19.lit) #49 | allow `r1=42 ∧ r2=42 ∧ r3=42` | sMRD |
| [`jctc/JCTC20.lit`](jctc/JCTC20.lit) #51 | allow `r1=42 ∧ r2=42 ∧ r3=42` | sMRD |
| [`esop_problem/RRE.lit`](esop_problem/RRE.lit) #46 | allow `r1=42 ∧ r2=42 ∧ r3=42` | `[Problem]` → sMRD |
| [`popl_grounding/FADD.lit`](popl_grounding/FADD.lit) #60 | allow `r1=1 ∧ r3=1` | `[Grounding]` → IMM |
| [`popl_promising/Upd-Stuck.lit`](popl_promising/Upd-Stuck.lit) #62 | allow `r1=1 ∧ r2=0` | `[IMM]` |

`pldi_repairing/LB.lit` #57 has left this table. Its assertion was the thing
that was wrong: RC11's no-thin-air axiom is `acyclic(sb ∪ rf)`, which forbids
plain load buffering, so `allow` was never RC11's verdict. It now asserts
`forbid` and is back in `litmus-tests/pldi_repairing/`.

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
