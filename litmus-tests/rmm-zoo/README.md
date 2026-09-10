# rmm-zoo litmus tests

Litmus tests added to close MoRDor's coverage gaps against the **Relaxed Memory
Model Zoo** — <https://rmm-zoo.kissig.org>, dataset in `rmm-zoo/rmm-zoo-dataset`.

The zoo tabulates every model against a fixed set of **property columns**
(`propertySchema` in `models.json`) and backs every ordering claim with a
**witness litmus test** (`litmus/`). This directory answers two questions:

1. Does MoRDor have a litmus test for each zoo property column?
2. Do the zoo's own witnesses, and the literature it cites, contain tests MoRDor
   does not have?

The headline gap was **multicopy atomicity** (`mca`): the zoo has no `mca` cell
for sMRD or MRD at all, and MoRDor had no test that isolates it — `test6/IRIW.lit`,
`test6/WRC.lit` and friends are the *plain* shapes, which load-load reordering
already explains. `properties/atomicity-mca/` fills that in.

## Layout

```
properties/     one directory per zoo property column (models.json propertySchema)
```

The `models/` subtree that once sat beside it held witness families for models
MoRDor does not implement — C11/C17/C20 and RA/SRA. Those files name a model the
registry has no entry for, so the suite was checking them under the `smrd`
fallback rather than under the model they were written for. They now live in
`litmus-tests-cpp/` and `litmus-tests-ra/`, out of the scanned tree, each with a
README recording the reference verdicts. Individual `properties/` files carrying
those annotations moved with them.

Every `.lit` file carries a header comment naming the zoo property or edge it
belongs to, the primary literature it comes from, and the reference verdicts
from that literature.

## Coverage against the zoo property table

`propertySchema` groups, with the MoRDor test that exercises each column.
"new" marks a test added by this directory.

### Compilation — optimal mapping to

| Key | Column | MoRDor coverage |
|---|---|---|
| `comp_x86`, `comp_power`, `comp_armv7`, `comp_armv8` | x86 / POWER / Armv7 / Armv8 | **out of scope.** These are claims about a *compilation scheme*, not about a program's outcomes. No single litmus test decides them; the zoo sources them from the mapping proofs. sMRD's four cells are all `true`, from Richards et al. (OOPSLA 2025). |

### Reordering — sound

| Key | Column | MoRDor coverage |
|---|---|---|
| `reorder_sl` | Store→Load | **new** `properties/reordering/store-load/` |
| `reorder_ss` | Store→Store | **new** `properties/reordering/store-store/`; also `sevcik_thesis/Reordering (f1.3)/{RA,RB}.lit` |
| `reorder_ll` | Load→Load | **new** `properties/reordering/load-load/` |
| `reorder_ls` | Load→Store | **new** `properties/reordering/load-store/` |

Only the Store→Store case was covered before, by the Ševčík pair. The new pairs
follow the same guarded shape so all four are comparable.

### Elimination — sound

| Key | Column | MoRDor coverage |
|---|---|---|
| `elim_sl` | Store/Load | `sevcik_thesis/Redundant Read Elimination (f1.4)/{RREWA,RREWB}.lit` |
| `elim_ss` | Store/Store | **new** `properties/elimination/store-store/` |
| `elim_ll` | Load/Load | `sevcik_thesis/Redundant Read Elimination (f1.4)/{RRERA,RRERB}.lit` |
| `elim_ls` | Load/Store | **new** `properties/elimination/load-store/`; the multi-threaded refutation is `sevcik_thesis/Skip/Redundant Write after Read Elimination.lit` |

### Other local transformations

| Key | Column | MoRDor coverage |
|---|---|---|
| `ile` | Irrelevant load elim. | `sevcik_thesis/Irrelevant Read Elimination/{IREA,IREB}.lit` |
| `sli` | Speculative load intro. | `sevcik_thesis/Irrelevant Read Introduction (f1.5)/{IRIA,IRIB,IRIC}.lit` |
| `rm` | Roach motel | `sevcik_thesis/Roach Motel Semantics.lit` |
| `irm` | Inverse roach motel | **new** `properties/local-transformations/inverse-roach-motel/` |
| `strengthen` | Strengthening | `own/FWD-STRENGTHEN-LIFT.lit` |
| `tp` | Trace preserving | `sevcik_thesis/Trace Preserving Transformation (f1.2)/{TPPA,TPPB}.lit` |
| `cse` | Common subexpr. elim. | `esop_problem/cse.lit`, `own/expressionPreservingSubstitution.lit` |

`irm` was the one blank. It is also the one column the zoo does *not* take from
the Moiseenko et al. survey — see `propertyProvenance["irm"]` in `models.json`,
which attributes it to Poetzl & Kroening (2015) §4.

### Global transformations

| Key | Column | MoRDor coverage |
|---|---|---|
| `rp` | Register promotion | **new** `properties/global-transformations/register-promotion/` |
| `ti` | Thread inlining | **new**, `[C11]`, moved to `litmus-tests-cpp/properties/global-transformations/thread-inlining/` |
| `vr` | Value range | **new** `properties/global-transformations/value-range/` |

All three were blank. `vr` matters most here: the zoo records `vr = true` for
exactly three models — SC, Promising and **sMRD** — so it is a column MoRDor's
own model is characterised by.

### Reasoning guarantees

| Key | Column | MoRDor coverage |
|---|---|---|
| `edrf` | External DRF | **new** `properties/reasoning-guarantees/external-drf/`; its racy witness `MP+rlx-race.lit` is `[C11]` and moved to `litmus-tests-cpp/` |
| `coh` | Coherence | `test6/{CoRR1,CoRW,CoWR,CoWW}.lit`; **new** `litmus-tests-ra/models/ra-sra-wra/{WW,Oscillating,SF}.lit` are single-location coherence violations |
| `no_ub` | No undefined behaviour | `symmrd/` (`LB+UB+data.lit` and the `refinement/` variants) |
| `in_order` | In-order execution | the LB family: `ISO/3-LB.lit`, `esop_problem/lb.lit`, `popl_bubbly/LB.lit`, … |
| `no_oota` | No out-of-thin-air | `avoidoota/` (31 tests), `on_thin_air_reads19/`, `own/OOTA7.lit` |

### Atomicity

| Key | Column | MoRDor coverage |
|---|---|---|
| `mca` | Multicopy atomic | **new** `properties/atomicity-mca/` (8 tests here; 2 more carry `[C11]`/`[SRA]` and moved to `litmus-tests-cpp/` and `litmus-tests-ra/`; `MP+fence+addr.lit` is parked in `litmus-tests-review/`) |

This was the gap. The zoo has an `mca` cell for 63 models (31 true, 32 false) and
**none for MRD or sMRD**.

## `properties/atomicity-mca/`

Property `mca`; sources Sarkar et al. (PLDI 2011), Pulte et al. (POPL 2018),
Alglave et al. (TOPLAS 2014), Su & Colvin (CCPE 38(2), 2026) §2.4 — the zoo's
source for the column itself.

Multicopy atomicity is the guarantee that a write becomes visible to all threads
at a single point. Plain IRIW and WRC do not test it, because load-load
reordering already explains their outcomes; the discriminating variants order
each reader's accesses by a dependency or fence, so that only a split view of a
single write is left as an explanation.

| Test | Reference verdict | MoRDor (sMRD) |
|---|---|---|
| `IRIW+rlx.lit` | POWER/C11 allow; SC/TSO/ARMv8 forbid | allows |
| `IRIW+addrs.lit` | POWER/ARMv7 allow; **ARMv8/RVWMO/SC forbid** | allows |
| `IRIW+ctrls.lit` | POWER/ARMv7/ARMv8 allow; SC forbids | allows |
| `WRC+rlx.lit` | POWER/C11 allow; SC/TSO/ARMv8 forbid | allows |
| `WRC+data+addr.lit` | POWER/ARMv7 allow; **ARMv8/RVWMO/SC forbid** | allows |
| `RWC+addr+fence.lit` | POWER/ARMv7 allow; SC/x86-TSO forbid | allows |
| `ISA2+data+addrs.lit` | POWER/ARMv7/ARMv8 allow (P0 unfenced); SC forbids | allows |
| `WRC+rel+acq.lit` | WRA/RA/SRA/C11/RC11/SC forbid (negative control) | forbids ✓ |
| `MP+fence+addr.lit` (now in `litmus-tests-review/`) | POWER/ARM/ARMv8/SC forbid; bare Coherence allows (positive control) | **allows ✗** |

Reading the table: **sMRD as MoRDor implements it is not multicopy atomic**, and
it allows every shape in the family — the controls included.

Part of that is sMRD working as intended. It allows `IRIW+addrs` and
`WRC+data+addr` because the address dependencies there are *syntactic and
semantically dead* — `rp + (r1 - r1)` is the same address whatever `r1` is, and a
semantic-dependency model drops it by design (the same reasoning that makes
`symmrd/LB+UB+data.lit` allowed). That is not a defect, but it does mean the
C-level analogues of the ARM/POWER `mca` witnesses do not transfer: on hardware
those dependencies are preserved *because* they are syntactic. Recording that is
the point of keeping `IRIW+rlx` and `IRIW+addrs` side by side.

The controls are a different matter. `MP+fence+addr` is a *positive* control —
every model with fence ordering forbids it, and only a bare coherence checker
allows it — and MoRDor allows it under `[Power]`, i.e. under IMM. That points at
fence ordering in the checker rather than at multicopy atomicity, and is still
open as #63.

The two release-acquire controls used to behave the same way, and no longer do.
sMRD's `hb` was `(ppo ∪ dp)⁺`, with no `rf` in it, so a release write read by an
acquire read produced no synchronises-with edge and the message-passing chain was
invisible to the coherence axiom (#67, #68). `hb` is now `(ppo ∪ dp ∪ sw)⁺` with
`sw = [W_rel];rf;[R_acq]`, which forbids both controls and rules out exactly the
one execution RC11 and IMM already ruled out. `WRC+rel+acq.lit` is back in the
table above and `MP+rel+acq.lit` in `models/ra-sra-wra/`, both reannotated
`[SMRD]`. Note this is *not* fence ordering: a relaxed write po-after a release
fence still does not synchronise, which is why `MP+fence+addr` has not moved.

An earlier revision of this table recorded `MP+fence+addr` and `WRC+rel+acq` as
`forbids ✓`. Those readings came from a build in which `forbid` assertions
short-circuited to valid without any execution being checked (`src/assertion.ml`;
see the commit "Check the executions a forbid assertion is given"), so every
`forbid` in the repository reported `✓`. Every row above has been re-measured
since — including `WRC+rel+acq`, whose `forbids ✓` is now earned rather than
vacuous.

`IRIW+scfences` is a second finding worth flagging: MoRDor allows it, matching
C11/C++17 and the known SC-fence defect that P0668 repaired, not RC11/C++20.

## `models/ra-sra-wra/`

The release-acquire family (WRA ⊂ RA ⊂ SRA) is annotated `[RA]` / `[SRA]`, which
`ModelRegistry` has no entry for, so the suite was checking it under the `smrd`
fallback. Four of the five live in `litmus-tests-ra/`, with the reference
verdicts and the per-test analysis in `litmus-tests-ra/README.md`.

`MP+rel+acq.lit` is the exception and is back here. It is the family's negative
control — every model in the zoo forbids it — so it is not asking an RA-specific
question, and sMRD forbids it once `sw` is in `hb` (#67). It is annotated
`[SMRD]`, since that is the model it is checked under.

## `models/cpp-release-sequences/` — moved

The release-sequence family is annotated `[C11]` / `[C17]` / `[C20]`, which
`ModelRegistry` has no entry for, so the suite was checking it under the `smrd`
fallback. It now lives in `litmus-tests-cpp/`, with the standards' verdicts, the
C++11/17/20 comparison table and the finding that MoRDor tracks C++17 on this
family in `litmus-tests-cpp/README.md`.

## Conventions

**Assertions state what MoRDor does, comments state what the literature says.**
The integration suite (`dune exec test/test_integration.exe`, and the
`Litmus Tests` CI workflow) runs the *strict* suite over every `.lit` file under
`litmus-tests/`, failing on any assertion MoRDor does not validate. Every test
here therefore asserts MoRDor's own verdict, with the reference verdicts recorded
in the header comment and in the tables above. Where the two differ, that
divergence is the finding — it is written down, not asserted away.

**Transformation pairs carry no assertion.** `src.lit` / `opt.lit` pairs follow
the existing `sevcik_thesis/` idiom: the transformation is sound for a model
exactly when the two programs admit the same behaviours. Compare with

```sh
dune exec mordor -- visual-es --single <file> --output-mode json
```

run over both files.

**Final-value conditions are projected.** Several upstream `rs/` tests condition
on a global's final value (`exists([x]=3 /\ ...)`) to pin the coherence order.
MoRDor admits those conjuncts individually but not always in conjunction with the
register outcome, so the ported assertion is the projection onto the reader's
registers and the coherence conjunct is recorded in the file header.

## Known expressibility gaps

Zoo witnesses that cannot be ported to MoRDor's input language as they stand:

- `incomparable/C11-vs-LKMM/RCU.litmus` — needs `rcu_read_lock` /
  `synchronize_rcu`; MoRDor has no RCU primitives.
- The scoped-memory-model families (`C11-vs-CUDA`, `C11-vs-OpenCL`, `C11-vs-HRF`,
  `HRF-vs-ScopedC11`, `PTX-vs-AMDGPU`, `OpenCL-vs-Vulkan`) — need memory scopes.
- `strictly-weaker/*` hardware witnesses in AArch64/ARM/PPC assembly
  (`WRC+addrs.aarch64`, `MP+dmb+addr`, `MP+sync+addr`, `SB+lwsync`, `SB+fence.tso`)
  — ported here at C level where the shape survives the translation
  (`properties/atomicity-mca/`), which as the table above shows is not for free.
- The Promising-specific witnesses (`Promising-vs-CSRA`, `Promising-vs-Weakestmo`)
  — MoRDor does not implement promising semantics; see
  `litmus-tests-promising/README.md` for how the existing suite handles that.

## Running

```sh
dune build
./_build/default/cli/main.exe run --single litmus-tests/rmm-zoo/properties/atomicity-mca/IRIW+addrs.lit

# the whole directory
for f in $(find litmus-tests/rmm-zoo -name '*.lit'); do
  echo "== $f"; ./_build/default/cli/main.exe run --single "$f" 2>/dev/null | grep -E '^(Valid|Executions):'
done
```
