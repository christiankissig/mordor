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
models/         witness families belonging to a model or model family
```

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
| `ti` | Thread inlining | **new** `properties/global-transformations/thread-inlining/` |
| `vr` | Value range | **new** `properties/global-transformations/value-range/` |

All three were blank. `vr` matters most here: the zoo records `vr = true` for
exactly three models — SC, Promising and **sMRD** — so it is a column MoRDor's
own model is characterised by.

### Reasoning guarantees

| Key | Column | MoRDor coverage |
|---|---|---|
| `edrf` | External DRF | **new** `properties/reasoning-guarantees/external-drf/` |
| `coh` | Coherence | `test6/{CoRR1,CoRW,CoWR,CoWW}.lit`; **new** `models/ra-sra-wra/{WW,Oscillating,SF}.lit` are single-location coherence violations |
| `no_ub` | No undefined behaviour | `symmrd/` (`LB+UB+data.lit` and the `refinement/` variants) |
| `in_order` | In-order execution | the LB family: `ISO/3-LB.lit`, `esop_problem/lb.lit`, `popl_bubbly/LB.lit`, … |
| `no_oota` | No out-of-thin-air | `avoidoota/` (31 tests), `on_thin_air_reads19/`, `own/OOTA7.lit` |

### Atomicity

| Key | Column | MoRDor coverage |
|---|---|---|
| `mca` | Multicopy atomic | **new** `properties/atomicity-mca/` (11 tests) |

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
| `IRIW+scfences.lit` | C11/C++17 allow; **RC11/C++20/SC forbid** | allows |
| `IRIW+rel+acq.lit` | WRA/RA/SRA/C11 allow; SC forbids | allows |
| `WRC+rlx.lit` | POWER/C11 allow; SC/TSO/ARMv8 forbid | allows |
| `WRC+data+addr.lit` | POWER/ARMv7 allow; **ARMv8/RVWMO/SC forbid** | allows |
| `WRC+rel+acq.lit` | all forbid (negative control) | forbids ✓ |
| `RWC+addr+fence.lit` | POWER/ARMv7 allow; SC/x86-TSO forbid | allows |
| `ISA2+data+addrs.lit` | POWER/ARMv7/ARMv8 allow (P0 unfenced); SC forbids | allows |
| `MP+fence+addr.lit` | POWER/ARM/ARMv8/SC forbid; bare Coherence allows (positive control) | forbids ✓ |

Reading the table: **sMRD as MoRDor implements it is not multicopy atomic**, and
the mechanism is specific. It forbids `MP+fence+addr` and `WRC+rel+acq`, so it
does honour fence and release-acquire ordering; but it allows `IRIW+addrs` and
`WRC+data+addr`, because the address dependencies there are *syntactic and
semantically dead* — `rp + (r1 - r1)` is the same address whatever `r1` is, and a
semantic-dependency model drops it by design. That is sMRD working as intended
(it is the same reasoning that makes `symmrd/LB+UB+data.lit` allowed), not a
defect, but it does mean the C-level analogues of the ARM/POWER `mca` witnesses
do not transfer: on hardware those dependencies are preserved *because* they are
syntactic. Recording that is the point of keeping `IRIW+rlx` and `IRIW+addrs`
side by side.

`IRIW+scfences` is a second finding worth flagging: MoRDor allows it, matching
C11/C++17 and the known SC-fence defect that P0668 repaired, not RC11/C++20.

## `models/ra-sra-wra/`

The release-acquire family: WRA ⊂ RA ⊂ SRA. Sources: Lahav, Giannarakis &
Vafeiadis (POPL 2016); Lahav & Boker (TOPLAS 2022) Ex. 3.5–3.7. Vendored from the
zoo's `strictly-weaker/SRA-vs-RA/`, `strictly-weaker/RA-vs-WRA/` and
`strictly-weaker/SC-vs-SRA/` witness sets. MoRDor had none of these.

| Test | Reference verdict | MoRDor (sMRD) |
|---|---|---|
| `2+2W+rel+acq.lit` | RA/WRA allow; SRA/SC forbid | allows |
| `MP+rel+acq.lit` | all forbid (negative control) | forbids ✓ |
| `Oscillating.lit` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `SF.lit` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |
| `WW.lit` | WRA allows; RA/SRA/C11/SC forbid | forbids ✓ |

sMRD sits with RA and above on all four: it has a coherence order, so the three
WRA-only outcomes are all ruled out, and it allows `2+2W` as RA does. The
`SC-vs-SRA/IRIW` witness lives in `properties/atomicity-mca/IRIW+rel+acq.lit`
rather than being duplicated here.

## `models/cpp-release-sequences/`

The release-sequence family, vendored from `gonzalobg/cpp_memory_model` via the
zoo's `litmus/cpp_memory_model/rs/`. Sources: ISO/IEC 14882:2011, :2017, :2020;
Boehm, Giroux & Vafeiadis P0668R5 (2018); Boehm P0982R1 (2018).

MoRDor had exactly one release-sequence test (`c20/rs-example.lit`) against the
zoo's sixteen. These fourteen files cover all sixteen upstream tests — two pairs
of upstream files are the same program under opposite conditions
(`mp-rs.cpp11`/`mp-rs.cpp17.undef`, `mp-rs-add-st.cpp11`/`.cpp17.undef`) and two
more differ only in which disjunct they ask about (`mp-rs-st-eadd-atomics`), plus
`RS+cpp20.lit` from the zoo's C++20-vs-C11 edge.

| Test | C++11 | C++17 | C++20 | MoRDor (sMRD) |
|---|---|---|---|---|
| `mp-rs.lit` | forbid | allow* | allow* | allows |
| `mp-rs-strel.lit` | forbid | forbid | forbid | forbids ✓ |
| `mp-rs-add.lit` | forbid | forbid | forbid | forbids ✓ |
| `mp-rs-eadd.lit` | forbid | forbid | forbid | forbids ✓ |
| `mp-rs-est.lit` | allow* | allow* | allow* | allows ✓ |
| `mp-rs-add-eadd.lit` | forbid | forbid | forbid | forbids ✓ |
| `mp-rs-add-est-atomic.lit` | allow | allow | forbid | allows |
| `mp-rs-add-est.lit` | allow* | allow* | allow* | allows ✓ |
| `mp-rs-add-st.lit` | forbid | allow* | allow* | allows |
| `mp-rs-st-eadd-atomics.lit` | forbid | allow | forbid | allows |
| `mp-rs-st-eadd.lit` | allow* | allow* | allow* | allows ✓ |
| `mp-rs-st-est-atomics.lit` | allow | allow | forbid | allows |
| `mp-rs-st-est.lit` | forbid* | allow* | allow* | allows |
| `RS+cpp20.lit` | — | — | allow | allows ✓ |

`*` = the allowing model reports the execution as a data race. Reference columns
are herd7 7.58 verdicts from the zoo's `rs/README.md`.

MoRDor tracks **C++17** on this family: it agrees with all three versions
wherever they agree, and on every test where the versions differ it takes the
C++17 reading — allowing what C++11 forbade (`mp-rs`, `mp-rs-add-st`,
`mp-rs-st-est`) and allowing what C++20 forbids (`mp-rs-add-est-atomic`,
`mp-rs-st-est-atomics`, `mp-rs-st-eadd-atomics`). So sMRD as implemented has not
taken up P0982's weakened release sequences.

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
