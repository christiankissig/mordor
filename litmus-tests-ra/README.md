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
| `models/ra-sra-wra/Oscillating.lit` | forbid `r0=1 ∧ r1=2 ∧ r2=1` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `models/ra-sra-wra/SF.lit` | forbid `r0=2 ∧ r1=1` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `models/ra-sra-wra/WW.lit` | forbid `r0=2 ∧ r1=1` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `properties/atomicity-mca/IRIW+rel+acq.lit` | allow `r1=1 ∧ r2=0 ∧ r3=1 ∧ r4=0` | WRA/RA/SRA/C11 allow; SC forbids | allows ✓ |

The two negative controls that used to sit in this table — `MP+rel+acq.lit` and
`WRC+rel+acq.lit` — have left it; see below.

## The two negative controls now hold — #67, #68 (fixed)

`MP+rel+acq` and `WRC+rel+acq` are message passing over a release write and an
acquire read. **Every** model in the zoo's RA family forbids them, sMRD included
— they are in the set precisely as controls, to show a witness set is not
vacuous. MoRDor used to report a witnessing execution for both.

That was never the missing-model problem: RC11 and IMM forbid both, in one
execution fewer each, so there was no model disagreement to hide behind. The
cause was in `src/coherence.ml`'s `SMRD.build_cache`, which built
`hb = (ppo ∪ dp)⁺`. `rf` was not in it, so a release write read by an acquire
read created no synchronises-with edge and the coherence axiom could not see the
message-passing chain at all.

`hb` is now `(ppo ∪ dp ∪ sw)⁺` with `sw = [W_rel];rf;[R_acq]`. The two po legs of
the shape were already there — `Forwarding.compute_ppo_sync` orders every event
into a release write and out of an acquire read — so the closure now derives
`hb` from the release write's po-predecessors to the acquire read's
po-successors, and chains two such steps for WRC. Both files forbid their outcome
and land on the same execution counts as RC11 and IMM (5 and 11). Note the fix is
deliberately *not* `hb ∪ rf`, which would order relaxed accesses too.

Both files have moved back under `litmus-tests/rmm-zoo/` and are reannotated
`[SMRD]`, since they are checked under sMRD and are not asking an RA-specific
question. Fences are not covered: a relaxed write po-after a release fence still
does not synchronise, which is `MP+fence+addr.lit` and #63.

The `forbids ✓` rows in this file's table were re-measured after `forbid`
assertions stopped short-circuiting to valid (`src/assertion.ml`, fixed in "Check
the executions a forbid assertion is given").

## See also

`litmus-tests/rmm-zoo/README.md` for the coverage analysis these tests were added
for, and `litmus-tests-cpp/` for the C11/C17/C20 family, which is out of the
suite for the same reason.
