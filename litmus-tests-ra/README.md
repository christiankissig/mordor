# Release-acquire litmus tests (reference only)

These litmus tests carry `[RA]` or `[SRA]` assertions and encode the outcome
**expected under release-acquire consistency** and its strong variant. The
hierarchy is WRA ⊂ RA ⊂ SRA. Sources: Lahav, Giannarakis & Vafeiadis (POPL 2016);
Lahav & Boker (TOPLAS 2022) Ex. 3.5–3.7. Vendored from the Relaxed Memory Model
Zoo — <https://rmm-zoo.kissig.org> — from its `strictly-weaker/SRA-vs-RA/`,
`strictly-weaker/RA-vs-WRA/` and `strictly-weaker/SC-vs-SRA/` witness sets.

## Why they live here and not in the test suite

**MoRDor does not implement RA or SRA as memory models.** `ModelRegistry` in
`src/coherence.ml` registers `imm`, `rc11`, `rc11c`, `smrd` and `undefined`, and
`model_options_table` in `src/context.ml` maps litmus-test model names onto
those. `RA` and `SRA` appear in neither.

An unrecognised name is not an error today: `apply_model_options` logs

```
Unknown memory model "RA"; no coherence model applied
```

and leaves the coherence model at the `smrd` default, so these files do produce a
verdict — sMRD's, not RA's. Note this is about the *model annotation*, not about
release and acquire access modes: those are part of the language MoRDor parses
and are used by every model it implements. What is missing is a coherence model
whose axioms are RA's.

These files are kept here **as reference only**. They are *not* scanned by the
integration suite, which scans `litmus-tests/`. To exercise them, either register
an RA/SRA coherence model, or use a tool that has one (herd7's RA model).

## Files

The sMRD column is what MoRDor reports today through the unknown-model fallback,
measured after the assertion-checker fixes described below. It answers a
different question from the one the file asks.

| Test | Asserts | Reference verdict | sMRD fallback |
|---|---|---|---|
| `models/ra-sra-wra/2+2W+rel+acq.lit` | allow `r0=1 ∧ r1=1` | RA/WRA allow; SRA/SC forbid | allows ✓ |
| `models/ra-sra-wra/MP+rel+acq.lit` | forbid `r0=1 ∧ r1=0` | all forbid (negative control) | **allows ✗** |
| `models/ra-sra-wra/Oscillating.lit` | forbid `r0=1 ∧ r1=2 ∧ r2=1` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `models/ra-sra-wra/SF.lit` | forbid `r0=2 ∧ r1=1` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `models/ra-sra-wra/WW.lit` | forbid `r0=2 ∧ r1=1` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `properties/atomicity-mca/IRIW+rel+acq.lit` | allow `r1=1 ∧ r2=0 ∧ r3=1 ∧ r4=0` | WRA/RA/SRA/C11 allow; SC forbids | allows ✓ |
| `properties/atomicity-mca/WRC+rel+acq.lit` | forbid `r1=1 ∧ r2=1 ∧ r3=0` | all forbid (negative control) | **allows ✗** |

## The two negative controls do not hold

`MP+rel+acq` and `WRC+rel+acq` are message passing over a release write and an
acquire read. **Every** model in the zoo's RA family forbids them, sMRD included
— they are in the set precisely as controls, to show a witness set is not
vacuous. MoRDor reports a witnessing execution for both.

This is not the missing-model problem. It is what the sMRD checker does with
release-acquire synchronisation, and it wants investigating on its own.

It was previously invisible, and `litmus-tests/rmm-zoo/README.md` still records
both as `forbids ✓` in its `properties/atomicity-mca/` table. That reading was
taken from a build in which `forbid` assertions short-circuited to valid without
being checked (`src/assertion.ml`, fixed in "Check the executions a forbid
assertion is given"), so every `forbid` in the repository reported `✓`. The three
rows in this file's table that still say `forbids ✓` have been re-measured since.

## See also

`litmus-tests/rmm-zoo/README.md` for the coverage analysis these tests were added
for, and `litmus-tests-cpp/` for the C11/C17/C20 family, which is out of the
suite for the same reason.
