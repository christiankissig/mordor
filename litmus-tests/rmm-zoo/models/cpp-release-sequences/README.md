# C/C++ release sequences

The release-sequence family, vendored from the Relaxed Memory Model Zoo
(<https://rmm-zoo.kissig.org>), mostly from its `litmus/cpp_memory_model/rs/`
set, which comes from `gonzalobg/cpp_memory_model`, plus `RS+cpp20.lit` from the
zoo's C++20-vs-C11 edge. Sources: ISO/IEC 14882:2011, :2017, :2020; Boehm,
Giroux & Vafeiadis P0668R5 (2018); Boehm P0982R1 (2018). The fourteen files cover
the zoo's sixteen upstream tests: two pairs are the same program under opposite
conditions (`mp-rs.cpp11`/`mp-rs.cpp17.undef`, `mp-rs-add-st.cpp11`/`.cpp17.undef`)
and two more differ only in which disjunct they ask about
(`mp-rs-st-eadd-atomics`).

Each file asserts MoRDor's verdict under `C11`, `C17` and `C20`, and whether the
program has a data race under each, as `allow (ub)` or `forbid (ub)`.

## The models

`c11`, `c17` and `c20` are configurations of the `RC11` functor in
`src/coherence.ml`:

| Model | Release sequence | SC | Thin-air axiom | Races |
|---|---|---|---|---|
| `c11` | C++11's, `cpp11.cat` | C11's conditions on `S`, `c11_partialSC.cat` | none | `dr`, undefined |
| `c17` | P0982's, `cpp17.cat` | as C11 | none | as C11 |
| `c20` | as C++17 | RC11's `psc` (P0668) | none | as C11 |

The zoo's `cpp11.cat` and `cpp17.cat` take RC11's `psc` for SC. That makes them
forbid IRIW with SC fences, which C11 and C++17 allow
(`properties/atomicity-mca/IRIW+scfences.lit`), so MoRDor's C11 and C++17 use
herd's partial form of the C11 conditions instead. On twelve SC shapes (SB, RWC,
IRIW and WRC over SC accesses and over SC fences, Z6.U, and an S4 witness) they
agree with herd7 under `c11_orig.cat`, the standard's total order `S`.

Candidate generation rejects a cycle in `dp ∪ ppo ∪ rf` before any model is
asked, so none of the three can exhibit an out-of-thin-air execution.

## Verdicts against herd7

herd7 7.58 on the zoo's own C litmus files: `cpp11.cat` for C11 and `cpp17.cat`
for C++17 and C++20. There are no SC accesses or SC fences in this family, so
these cat files and MoRDor's models define the same thing here. `*` = racy,
which the standard calls undefined.

| Test | Asserts | herd7 C++11 | MoRDor C11 | herd7 C++17 | MoRDor C17 | MoRDor C20 |
|---|---|---|---|---|---|---|
| `mp-rs.lit` | `r1=2 ∧ r2=0` | Never | forbid | allow\* | allow\* | allow\* |
| `mp-rs-strel.lit` | `r1=2 ∧ r2=0` | Never | forbid | Never | forbid | forbid |
| `mp-rs-add.lit` | `r1=2 ∧ r2=0` | Never | forbid | Never | forbid | forbid |
| `mp-rs-eadd.lit` | `r1=2 ∧ r2=0` | Never | forbid | Never | forbid | forbid |
| `mp-rs-est.lit` | `r1=2 ∧ r2=0` | allow\* | allow\* | allow\* | allow\* | allow\* |
| `mp-rs-add-eadd.lit` | `r1=3 ∧ r2=0` | Never | forbid | Never | forbid | forbid |
| `mp-rs-add-est-atomic.lit` | `r1=3 ∧ r2=0` | allow | allow | allow | allow | allow |
| `mp-rs-add-est.lit` | `r1=3 ∧ r2=0` | allow\* | allow\* | allow\* | allow\* | allow\* |
| `mp-rs-add-st.lit` | `r1=3 ∧ r2=0` | Never | forbid | allow\* | allow\* | allow\* |
| `mp-rs-st-eadd-atomics.lit` | `(r1=2 ∨ r1=4) ∧ r2=0` | Never | forbid | allow | allow | allow |
| `mp-rs-st-eadd.lit` | `r1=3 ∧ r2=0` | allow\* | allow\* | allow\* | allow\* | allow\* |
| `mp-rs-st-est-atomics.lit` | `r1=3 ∧ r2=0` | allow | allow | allow | allow | allow |
| `mp-rs-st-est.lit` | `r1=3 ∧ r2=0` | allow\*† | allow\* | allow\* | allow\* | allow\* |
| `RS+cpp20.lit` | `r0=2 ∧ r1=0` | — | allow\* | — | allow\* | allow\* |

† Upstream's condition also asks `[x]=2`, under which herd7 answers Never\*;
the file asserts the condition without it, under which herd7 answers
Sometimes\*.

All three models agree with herd7 on every row, races included. MoRDor's `rc11`
agrees with herd7 under `rc11.cat` on every row too.

### Write elision and release sequences

In `mp-rs`, `mp-rs-st-eadd-atomics` and `mp-rs-st-est` a release store is
overwritten by a relaxed store of its own thread. sMRD's write elision
(`Elaborations.we`) may elide any write that is neither volatile nor part of an
RMW, and dropping the release store leaves the acquire nothing to synchronise
with. Under C++11, RC11 and IMM the relaxed store continues the release sequence
the release store heads, so the elision is unsound there, and those models
reject every execution that elides a release store for a store that is not a
release (`MEMORY_MODEL.elidable`). Under C++17 and C++20 the relaxed store does
not continue the sequence, the elision changes nothing, and they keep it. sMRD,
with no release sequences, keeps it too. Until this was checked per model, C11
and RC11 allowed `mp-rs` and `mp-rs-st-eadd-atomics`.

### The zoo's C++20 column is `cpp2w.cat`'s

The zoo records C++20 FORBIDS for `mp-rs-add-est-atomic`,
`mp-rs-st-eadd-atomics` and `mp-rs-st-est-atomics`, from herd7 under
`cpp2w.cat`. That file is `cpp17.cat` plus
`acyclic(tecotsb | rb)` for `tecotsb = ([A];eco;[A])+;sb`, "the change from Dxxxx
to close gap in hb for non-atomic operations", a later draft and not C++20. The
axiom also forbids message passing over relaxed accesses (herd7 answers MP+rlx
Never under `cpp2w.cat` and Sometimes under `cpp17.cat`). MoRDor's C++20 is
C++17's release sequence with P0668's SC, so it allows those three, as C++17
does. The C++20/C11 incomparability the zoo records still holds, through
`IRIW+scfences.lit` on one side and `mp-rs-add-st.lit` and `mp-rs.lit` on the
other.
