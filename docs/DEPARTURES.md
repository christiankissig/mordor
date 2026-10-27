# Departures from the sMRD paper

MoRDor implements Symbolic MRD as defined in Richards, Wright, Cooksey and
Batty, *Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic
Choice*, OOPSLA 2025, referred to below as "the paper". This document lists
every place where MoRDor's sMRD differs from the paper's definitions. It covers
the sMRD pipeline only: interpretation, justification and elaboration,
preserved program order, freezing, coherence and assertions. The other models
check the executions sMRD builds, so the departures before coherence apply to
them too, with one exception: only sMRD and MRD, which MoRDor implements as
sMRD, see executions built with forwarding or write elision (E4). Every other
model, RC11 among them, is asked about the program's own events (#207).

Each entry gives:

- **Paper**: what the paper says, by definition or section.
- **MoRDor**: what MoRDor does, by `file:function`.
- **Why**: the reason, or the issue that records it.
- **Witness**: the litmus tests that show the difference, or "none" if no test
  does yet.

Each entry also has a kind:

| Kind | Meaning |
|---|---|
| relaxation | MoRDor admits more than the paper, deliberately |
| repair | the paper's definition, taken literally, gives a wrong answer, and MoRDor does something else |
| restriction | MoRDor admits less than the paper: an elaboration the paper allows is not implemented, or is implemented only in part |
| extension | the paper does not cover the construct, and MoRDor gives it a meaning |
| open | a difference that is suspected to be a bug and is not settled |

Definition numbers are the paper's: 4.1 to 4.18 in §4, appendices A to I.
Issue and PR numbers refer to `christiankissig/mordor`.

## Summary

| # | Stage | Departure | Kind |
|---|---|---|---|
| [I1](#i1-fetch-and-add-returns-the-sum) | interpret | `fadd` puts the sum in its register, not the value read | repair |
| [I2](#i2-an-initial-event-and-reads-of-unwritten-locations) | interpret | an initial event 0 is added, and a read of a location nothing writes reads an unconstrained value from it | extension |
| [I3](#i3-loops-runs-out-of-unrollings-are-not-executions) | interpret | a run whose loop runs out of unrollings is not an execution | repair |
| [I4](#i4-undefined-behaviour-is-exploited-by-folding-at-interpretation) | interpret | UB-exploiting models fold `e / !r` during interpretation | extension |
| [I5](#i5-the-language-is-larger) | interpret | locks, `acq_rel`, `na`, `volatile`, `do`-loops | extension |
| [I6](#i6-addresses-are-unconstrained-integers) | interpret | addresses are unconstrained integers: `&x` and `malloc` may be 0 | open |
| [E1](#e1-allocations-and-frees-are-justified) | justify | allocations and frees get justifications and `dp` edges | extension |
| [E2](#e2-value-assignment) | elaborate | value assignment needs entailment, uses Ω, and leaves locations alone | restriction, relaxation |
| [E3](#e3-strengthening-only-inside-lifting) | elaborate | strengthening is applied only inside lifting, with the equation between two written values | restriction |
| [E4](#e4-forwarding-and-write-elision) | elaborate | forwarding and elision are po-forward and cut to the write's po-window; forwarding is thread-local for W×W, never elides volatile or RMW accesses, does not cross an acquire, and is also tried under Ω; write elision does not cross a release, nor elide a release store into a relaxed one; only sMRD and MRD elaborate | restriction, repair |
| [E5](#e5-lifting-is-syntactic) | elaborate | lifting matches predicates syntactically and keeps the common conjuncts | restriction, open |
| [E6](#e6-weakening) | elaborate | Ω is per write and stated over registers | extension |
| [E7](#e7-covered-justifications-are-dropped) | elaborate | a justification covered by one with fewer conjuncts is dropped | restriction |
| [E8](#e8-derived-program-wide-guarantees-are-not-implemented) | elaborate | the extended semantics of Def. 4.18 is not implemented | restriction |
| [P1](#p1-alias-ordering-is-satisfiability-under-p-ψ-and-the-programs-constraints) | ppo | `≤_alias` is satisfiability, under `P ∧ ψ` and the program's distinctness constraints | conforms since #38, #142 |
| [P2](#p2-no-xco-ppo_rmw-instead) | ppo | no `≤_xco`; `ppo_rmw` instead | restriction, extension |
| [P3](#p3-the-initial-event-and-terminal-events-are-in-ppo) | ppo | the initial event is ordered before, and terminal events after, every event | extension |
| [F1](#f1-ppo-is-cut-to-windows-anchored-at-any-event) | freeze | `ppo_j` is cut to its window; `ppo_sync` and `ppo_loc` are cut, after remapping, to windows anchored at any event; `ppo_init` is added; the union is closed | relaxation (deliberate) |
| [F2](#f2-dp-is-remapped-through-the-forwarding-context) | freeze | `dp` is remapped through `δ`, and elided writes contribute none | repair |
| [F3](#f3-justifications-need-not-share-a-forwarding-context) | freeze | justifications need not share `δ`; their contexts are united | relaxation |
| [F4](#f4-the-execution-predicate-has-more-conjuncts) | freeze | the execution predicate also has every event's `⋎`, and the distinctness constraints | repair |
| [F5](#f5-allocation-disjointness) | freeze | allocation disjointness is on base addresses, without sizes | restriction |
| [C1](#c1-hb-is-over-ppo-dp-not-sb) | coherence | `hb = (ppo ∪ dp ∪ sw ∪ lo)⁺`, not RC11's `(sb ∪ sw)⁺` | relaxation (deliberate) |
| [C2](#c2-sw-release-sequences-fences-and-psc) | coherence | `sw` is RC11's over `rfe`; `psc` takes `sb = po` | conforms since #126, #170 |
| [C3](#c3-elided-writes-are-not-in-coherence) | coherence | elided and forwarded events are not in coherence, so elision does not cross a release and forwarding not an acquire; other models reject elaborated executions | repair |
| [C4](#c4-co-relates-writes-whose-locations-must-be-equal) | coherence | `co` orders writes whose locations are equal under the execution's predicates | repair |
| [C5](#c5-no-data-races) | coherence | no data races; `na` is relaxed | extension |
| [A1](#a1-final-values-come-from-an-admitted-coherence-order) | assert | `@x` is the co-maximal write of an admitted `co` | extension |
| [A2](#a2-undefined-behaviour-is-defined-over-rhb) | assert | use-after-free and use-before-allocation over `rhb = (ppo ∪ fj ∪ dp ∪ rf)⁺` | extension |

## Interpretation (§4.2, Definitions 4.1–4.5)

### I1. Fetch-and-add returns the sum

- **Paper**: §4.2, `⟨r := fadd(x, ε)⟩ = rmw((R x α) • (W x (α + ε)) • κ(ρ[r ↦ α]))`. The register gets the value read.
- **MoRDor**: `src/interpret.ml:interpret_statements_open`, case `Fadd`: the register gets `α + ε`, the value written. Promising semantics (`src/promising.ml`) does the same.
- **Why**: bcea62d takes the paper's `ρ[r ↦ α]` as an error. Note that C's `atomic_fetch_add` returns the old value, as the paper does; MoRDor's `fadd` behaves like an add-and-fetch.
- **Witness**: `litmus-tests/popl_bridging/FADD Example.lit`, `litmus-tests/imm/FADD RMW Atomicity.lit`, `litmus-tests/popl_bridging/RMW Atomicity.lit`. Each asserts register values that are one operand above the value read.

### I2. An initial event, and reads of unwritten locations

- **Paper**: Def. 4.9 asks `E|R = π₂(rf)`: every read reads from a write of the execution. The paper has no initial event. Initial values are writes in the program.
- **MoRDor**: `src/interpret.ml:interpret_generic` puts an `Init` event, label 0, before everything. A read may read from it (`src/executions.ml:ReadFromValidation.init_rf`) only if its location is none of the execution's writes that are not po-after it. `ReadFromValidation.env_rf` skips edges from event 0, so the value read is unconstrained.
- **Why**: a location the program never writes has no write to read from. Without event 0, a program that reads such a location (a parameter `p`, an allocation's contents, an offset no write covers) would have no executions.
- **Witness**: `litmus-tests/symmrd/alignment.lit` (reads `p`, which nothing writes), `litmus-tests/own/UncoveredOffsetReadsInitial.lit`.

### I3. Loops: runs out of unrollings are not executions

- **Paper**: §4.2 and Appendix E (Fig. 40): `⟨while (b) {P}⟩ⁿ = ⟨if (b) {P; while (b) {P}} else {skip}⟩ⁿ⁻¹`, with `⟨P⟩⁰ = ∅`. The step counter `n` is one counter, threaded through sequencing, so nested and sequential loops share it. At depth 0 the continuation is empty, and a maximal conflict-free set still contains the events of the run that was cut off.
- **MoRDor**: `src/interpret.ml:StepCounterSemantics`. The default is a bound per loop (`--step-counter-per-loop`, default 2); `--step-counter` gives a global bound. Out of unrollings, the loop's exit check becomes a `Blocked` node (`unrol_while_loop`, `unrol_do_loop`). A run that would go round again ends without a terminal event, and `src/eventstructures.ml:generate_max_conflictfree_sets` only returns paths that end in terminal events. A truncated run is therefore not an execution.
- **Why**: a run cut off by the bound is not a run of the program. Keeping it reports outcomes that no complete run has, such as a spin loop that exits without having read the flag (#133).
- **Witness**: `litmus-tests/oopsla26_rgsep/MP-repeat.lit`.

### I4. Undefined behaviour is exploited by folding at interpretation

- **Paper**: §2 and Example 8.1 (LB+UB+data). The compiler may assume a division does not divide by zero. In the formal model this goes through strengthening, value assignment and weakening, with the guarantee as part of Ω.
- **MoRDor**: the expression `e / !r` is division where `r = 0` would be undefined. Under the UB-exploiting models (`UB11`, `RC11UB`, `IMMUB`; `options.ubopt`), `src/interpret.ml:ub_assume` folds it to `e` while the program is interpreted, and records `sym = 0` as a fact (`ub_facts`). The fact joins the per-write de facto constraints Ω, so the narrowed write stands next to the original one (E2). Under the other models nothing is folded.
- **Why**: this is a direct encoding of the extrinsic choice in Example 8.1 (#65).
- **Witness**: `litmus-tests/symmrd/LB+UB+data.lit`, `litmus-tests/symmrd/LB+UB+data+z.lit`, `litmus-tests/symmrd/refinement/`, `litmus-tests/avoidoota/listing27_allow.lit` against `listing27_forbid.lit`.

### I5. The language is larger

- **Paper**: Def. 4.1. Orders are `rlx`, `rel`, `acq` and `sc`; there are no locks and no `do`-loops.
- **MoRDor**:
  - `lock`/`unlock` events. They are acquire and release in `ppo_sync` (`src/forwarding.ml:compute_ppo_sync`), and a lock order `lo` is part of `hb` (C1).
  - `acq_rel` (`ReleaseAcquire`), for both reads and writes. `compute_ppo_sync` and `Coherence.SMRD` count it as both acquire and release.
  - `na`, treated as relaxed under sMRD (C5).
  - `do { P } while (b)` loops, unrolled as `while` loops are (I3).
  - The `volatile` flag (`x :v= e`). It keeps an access out of the elided position of forwarding and write elision, and out of lifting (`src/elaborations.ml:ForwardElab.fwd`, `ForwardElab.we`, `LiftElab.elab`). It gives no `ppo`, `dp` or `sw` edge. The docstrings of `compute_ppo_sync` and `ForwardingContext.ppo_sync` say volatile accesses contribute `ppo`; they do not.
- **Why**: MoRDor checks the same programs under many models, and these constructs come from their corpora.
- **Witness**: `litmus-tests/own/volatile-store-not-elided.lit` against `relaxed-store-elided.lit`, `volatile-read-not-lifted.lit`, `volatile-write-not-lifted.lit`, `litmus-tests/sevcik_thesis/LB+monitors (f1.1B).lit`.

### I6. Addresses are unconstrained integers

- **Paper**: §4, "the address of all global variables are assumed to be distinct", and an allocation's symbol is "disjoint from all `l ∈ L`". Nothing relates addresses to integer values such as 0.
- **MoRDor**: `src/interpret.ml:distinctness` makes globals pairwise distinct, and allocations distinct from globals and from each other (save reuse, F5). Nothing keeps an address away from 0. So `&x` and the result of `malloc` may equal 0, the null pointer, or any other integer a program compares them with.
- **Why**: not decided. C guarantees that the address of an object and a successful allocation are not null.
- **Witness**: none in the suite. The following program allows `r1 = rx` and `rm = 0` under sMRD:

  ```
  x := 0; p := 0;
  r1 := p;
  rx := &x;
  rm := malloc 1;
  %%
  allow (r1 = rx) [sMRD]
  allow (rm = 0) [sMRD]
  ```

  This can hide a thin-air cycle. In `r1 := p; rx := &x; if (r1 = rx) { *r1 := 1 } ||| r2 := x; rq := &x; if (r2 = 1) { p := rq }`, the outcome `r1 = rq ∧ r2 = 1` is allowed because `r1` reads the initial `p = 0`, with `&x = 0`.

## Justification and elaboration (§4.3, §4.7, Definitions 4.6, 4.10–4.18)

### E1. Allocations and frees are justified

- **Paper**: §4.3, `J₀ = {(⋎(w), syms(loc(w)) ∪ syms(val(w))) ⊢ w | w ∈ W, ⋎(w) ≢ ⊥}`. Only writes are justified, and `dp` (Def. 4.9) only ends in writes.
- **MoRDor**: `src/elaborations.ml:pre_justifications` justifies writes, allocations and frees. An allocation depends on its size, and a free on its location. Value assignment, forwarding and lifting skip them (`ValueAssignElab.elab`, `batch_elaborations`' `elaborable` filter), so each free keeps exactly one justification.
- **Why**: use-after-free needs ordering into frees and out of allocations (A2), and a free whose pointer was read must depend on that read.
- **Witness**: `litmus-tests/own/FreeRace.lit`, `litmus-tests/own/FreeRace2.lit`.

### E2. Value assignment

- **Paper**: Def. 4.10, `G_va`: if `α ≡_P v` for a value `v`, substitute `v` for `α` in the write's location and value, and set `D′ = syms(x′) ∪ syms(ε′)`. One symbol at a time, under `P`.
- **MoRDor**: `src/elaborations.ml:ValueAssignElab.elab`.
  - The context is `P ∧ ψ_δ ∧ Ω_w`, where Ω_w is the write's de facto constraints. These are the program-wide guarantee and any UB facts (I4). The paper uses `P` alone; Ω enters only through weakening.
  - The solver proposes a value for each symbol, and `Solver.exeq` checks that the context entails it. Every entailed symbol is substituted at once.
  - Only the written value is rewritten. The location keeps its symbols, so value assignment never removes an address dependency.
  - The predicate is kept whole, as in Def. 4.10 (#90 explains why discharging any conjunct is thin air).
- **Why**: using Ω here is what lets a UB assumption narrow a write while the original stays (#65). Entailment rather than a solver model fixes #43. Leaving locations alone is not argued anywhere.
- **Witness**: `litmus-tests/symmrd/LB+UB+data+z.lit` (Ω), `litmus-tests/own/VA-unrelated-guard-smrd.lit`, `litmus-tests/own/LB+deps-smrd.lit` (the predicate kept). The location restriction has no witness.

### E3. Strengthening only inside lifting

- **Paper**: Def. 4.11, `G_str`: strengthen `P` to any `P′` with `P′ ⇒ P ∧ ⋀_{e∈S} ⋎(e)`, where `S = O(P′) \ O(P)` are events in program order with `w`, not `≤`-after it, and not moved by `δ`.
- **MoRDor**: `src/elaborations.ml:StrengthenLiftElab`. Strengthening is never a pass of its own. For two conflicting writes to one location whose values differ, both predicates get the equation between the values (relabelled). Both are then value-assigned and lifted, and only the lifted result is kept. No other `P′` is tried, and the side conditions on `S` are not checked.
- **Why**: Def. 4.11 gives no hint which `P′` to add, and a strengthened justification on its own is covered by the one it came from (E7). Lifting supplies the hint (#90).
- **Witness**: `litmus-tests/own/FWD-STRENGTHEN-LIFT.lit` (the implemented case). `litmus-tests/own/LB+str-smrd.lit` is the paper's Appendix C example: the strengthening there adds a read's guard (`r2 = 1`), not a value equation, so MoRDor forbids an outcome sMRD allows.

### E4. Forwarding and write elision

- **Paper**: Def. 4.12 and 4.13. `e₁ →F′ e₂` if `e₁ ∈ pred_δ(e₂, P)` and `loc(e₁) ≡_{P∧ψ_δ} loc(e₂)`. Forwarding is `W × R_rlx ∪ W × W_rlx ∪ R × R`; write elision is `W × W`. `G_fwd` substitutes `[val(e₂) ↦ val(e₁)]` into `P`, the location and the value.
- **MoRDor**: `src/elaborations.ml:ForwardElab`.
  - The pair must be in `ppo_loc` minus the fork-join edges `fj`, and `e₁` an immediate `ppo`-predecessor of `e₂`. Location equality is checked under `P` alone (`fprime`), without `ψ_δ`.
  - The pair is po-forward: `e₁ ⊑ e₂` (`ForwardElab.po_forward`, #210), for forwarding and for write elision. `ppo_loc` is remapped through the context built so far, so its pairs alone do not ensure it.
  - Both events must be po-before the justified write (or be it), so forwarding stays within the write's window `{e | e ⊑ w ∨ e = w}`, and `e₁` must not be the initial event.
  - W×W forwarding (redundant-store elimination) is within one thread. Write elision is not.
  - A volatile access, or either access of an RMW, is never in the elided position.
  - Write elision (`ForwardElab.elision_blocked`) does not elide a release store into a store that is not a release, nor elide a write across an event po-between the two that publishes it: a write or fence of mode `rel` or stronger, an `unlock`, or an `sc` access. Acquires do not block it. This holds for an initialising write too, elided across the fork by a thread's write.
  - Forwarding (`ForwardElab.forwarding_blocked`, #210) does not cross an event po-between the two that acquires: a read or fence of mode `acq` or stronger, a `lock`, an `sc` read or fence. An acquire read is forwarded only from an acquire read, an `sc` read only from an `sc` read, and an `sc` read not across an `sc` write. A release, an `unlock` and a release fence do not block. `MORDOR_FWD_SYNC` selects the rule for experiments: `acq` (the default, this one), `none` (no restriction, as before #210), `rel` (the events that block write elision), `both`, or `sc` (only `sc` accesses and fences, and an `sc` read only from an `sc` read).
  - Forwarding is tried under `P`, and again under `P ∧ Ω` when the write has de facto constraints.
  - Only forwarding into a read substitutes (`ForwardElab.substitute`). A store-store forwarding rewrites nothing, since `val(e₂)` is an expression, not a symbol.
- **Why**: the po-window anticipates the freeze cut (F1). The thread-local W×W fixes POPL 2019's "Preserving detour" (#58). The RMW exclusion keeps RMW atomicity, which is stated over `rf`, effective. Substitution into `P` fixes #46. The release restrictions on elision and the acquire restrictions on forwarding are C3's.
- **Witness**: `litmus-tests/popl_bridging/Preserving detour.lit`, `litmus-tests/imm/FADD RMW Atomicity.lit`, `litmus-tests/esop_problem/RRE.lit`, `litmus-tests/own/volatile-store-not-elided.lit`, `litmus-tests/own/WE-across-release.lit`, `litmus-tests/opts/we-fence-remap.lit`, `litmus-tests/own/FWD-po-forward.lit`, the forwarding tests under C3. Checking without `ψ_δ` and forwarding under Ω have no witness.

### E5. Lifting is syntactic

- **Paper**: Def. 4.14–4.16, `G_lift`: if `w₁` under `P₁` and `w₂` under `P₂` are closed relabel-equivalent with a one-to-one relabelling Λ, and `⟦D₁⟧Λ = D₂`, add `(⟦P₁⟧Λ ∨ P₂, D₂) ⊢_δ w₂`. Both justifications have the same `δ`.
- **MoRDor**: `src/elaborations.ml:LiftElab.elab`.
  - Predicates are lists of conjuncts. `find_distinguishing_predicate` asks that each side's uncommon conjuncts, negated, appear in the other side. The lifted predicate is the common conjuncts, not the disjunction.
  - The test assumes both lists are sorted, which they need not be.
  - The two `δ` need not be equal: their union must be functional, and the result takes `w₂`'s.
  - It never lifts a volatile write, or a relabelling that pairs a volatile read.
  - It skips pairs where both predicates are empty.
- **Why**: the syntactic test is cheap and covers the common case of `C ∧ d` against `C ∧ ¬d`.
- **Witness**: #36 is the restriction. `litmus-tests-jmm/jctc/JCTC6.lit` needs a lift whose predicates are `β = 1` against `β = 0 ∧ β ≠ 1`, and it is refused. That file is annotated `[JMM]`, so the suite does not run it.
- **Open**: when the uncommon parts have more than one literal, the common conjuncts are weaker than the disjunction. `C ∧ a ∧ b` and `C ∧ ¬a ∧ ¬b` lift to `C`, though `P₁ ∨ P₂ = C ∧ ((a ∧ b) ∨ (¬a ∧ ¬b))`, which still depends on `a` and `b`. This admits thin air, and whether it does depends on the order of the conjuncts:

  ```
  x := 0; y := 0; z := 0;
  { r1 := x; r2 := y;
    if (r2 = 1) { if (r1 = 1) { z := 1 } } else { if (r1 != 1) { z := 1 } } }
  ||| { r3 := z; x := r3; y := r3 }
  %%
  forbid (r1 = 1 && r2 = 1 && r3 = 1) [sMRD]
  ```

  The `forbid` fails at 6dd8521. With the nesting swapped (`if (r1 = 1) { if (r2 = 1) ... }`) it holds. No issue is filed yet.

### E6. Weakening

- **Paper**: Def. 4.17, `G_weak`: from `(P′ ∧ P, D) ⊢ w` derive `(P′, D) ⊢ w` if `Ω ⇒ P`. Ω is one program-wide guarantee.
- **MoRDor**: `src/elaborations.ml:WeakElab.elab` drops each conjunct that Ω_w entails. Ω is written as a predicate over registers before the program (`[(r1 & 15) = 0] %% ...`). `src/interpret.ml` evaluates it in each event's register environment, giving a per-write `structure.defacto`, with the UB facts of I4 added.
- **Why**: Ω has to mention the reads it constrains, and in the source those are registers.
- **Witness**: `litmus-tests/symmrd/alignment.lit`, against `no-alignment.lit`.

### E7. Covered justifications are dropped

- **Paper**: §4.3, `J = ⋃ Jᵢ` keeps every justification derived.
- **MoRDor**: `src/elaborations.ml:batch_elaborations`' `filter_justs` drops a new justification if another one for the same write, with the same location, value, `fwd` and `we`, has a subset of its conjuncts (`src/justifications.ml:Justification.covers`). Episodicity's `collapse_forwarding` also keeps one justification per `(P, D, w)`; the executions pipeline never sets it.
- **Why**: without this the fixed point enumerates the power set of the forwarding edges, and on larger programs it does not terminate. A justification with fewer conjuncts gives fewer `dp` edges.
- **Witness**: none. A covered justification with more conjuncts can make `≤_alias` smaller (P1), so dropping it can, in principle, lose an execution. No case is known.

### E8. Derived program-wide guarantees are not implemented

- **Paper**: Def. 4.18, the extended semantics `⦇P⦈ⁿ_Ω₀`, which closes Ω under the invariants a program's executions satisfy.
- **MoRDor**: only the extrinsic Ω of E6. Refinement chains (`%% ~~> [Model=allow] %%`) compare two programs and are a different feature.
- **Witness**: none.

## Preserved program order (§4.4, Definitions 4.7–4.8)

### P1. Alias ordering is satisfiability under P, ψ and the program's constraints

- **Paper**: Def. 4.8, `≤^P_alias = {(e₁, e₂) ∈ ⊑ | ∃f. ⟦P ∧ loc(e₁) = loc(e₂)⟧_f ≡ ⊤}`, satisfiability. `≤^δ_P` is taken under `P ∧ ψ_δ`.
- **MoRDor**: `src/forwarding.ml:EventStructureContext.init` puts pairs whose locations the structure proves equal (`compute_ppo_loc_eq`) into `ppo_base`, unconditionally. `ForwardingContext.ppo` and `ForwardingContext.ppo_loc` keep the rest when `Solver.expoteq` finds them satisfiable under `P ∧ ψ_δ ∧ structure.constraints`. The constraints are the distinctness of I6 and F5. A pair is kept only if both events have a location.
- **Why**: this conforms. MoRDor used validity (`Solver.exeq`) until #38 (in `ppo`) and #142 (in `ppo_loc`). Adding the distinctness constraints matches the paper's assumption that globals and allocations are distinct.
- **Witness**: `litmus-tests/own/ptr-overwrite-coherence.lit`.

### P2. No ≤_xco; ppo_rmw instead

- **Paper**: Def. 4.8, `≤_xco = (A ∪ C)² ∩ ⊑` orders a thread's allocations and frees totally. Nothing in `≤` is about RMWs. They are constrained only through `⊑rmw` and RC11's atomicity axiom.
- **MoRDor**: no `≤_xco`. An allocation and a free are ordered only when their locations may alias (P1), so a free and a later allocation of another region are not ordered. `src/forwarding.ml:ForwardingContext.compute_ppo_rmw` adds `ppo_sync; (w, r) ∪ (w, r); ppo_sync` for each RMW whose condition holds. This orders what is sync-before an RMW's write before its read, and its write before what is sync-after its read.
- **Why**: `ppo_rmw` makes a release or acquire RMW a synchronisation point as a whole. Leaving out `≤_xco` is not argued anywhere.
- **Witness**: none for either half.

### P3. The initial event and terminal events are in ppo

- **Paper**: no initial or terminal events.
- **MoRDor**: `src/forwarding.ml:EventStructureContext.compute_ppo_init` orders event 0 before every event and every event before the terminal events of its thread (`ppo_init`). The terminal events are what put a thread's last events into `ppo` at all (F1).
- **Why**: see I2 and F1.
- **Witness**: `litmus-tests/own/CoRR-ReaderNoWrites.lit`.

The paper's `≤^δ_P` subtracts a set written `E?_{P∧ψ_δ}`. MoRDor's `ForwardingContext.remap_rel` removes the self-pairs that remapping creates, and `freeze_ppo` restricts to the path. Whether that is the paper's subtraction is not settled.

## Freezing (§4.5, Definition 4.9)

### F1. ppo is cut to windows anchored at any event

- **Paper**: Def. 4.9, `≤ ≜ ⋃_{j∈J} ≤^δ_{j_P} ∩ {e | e ⊑ w_j ∨ e = w_j}²`. Each justification contributes its `ppo` restricted to the events po-before its write, and the write. The cut is applied after remapping through `δ`. The union is not closed.
- **MoRDor**: `src/executions.ml:Freeze.freeze_ppo` cuts each `ppo_j` this way. It adds `ForwardingContext.ppo_sync` and `ppo_loc` (under the combined predicate `p_combined`, F4), both remapped through the united context and then cut by `Freeze.anchored_on_path` to the pairs `(a, b)` for which some event `e` of the path has `a ⊑ e ∨ a = e` and `b ⊑ e ∨ b = e`. It adds `ppo_init` (P3), which is a subset of `po`. It restricts the union to the path and closes it transitively (since 2525f99).
- **Relation to sMRD**: the cut is the paper's window `{e | e ⊑ w ∨ e = w}²`, applied as the paper applies it, after remapping, but anchored at every event of the path instead of only at the justified writes. A pair the paper keeps is kept. A pair on a thread's events after its last justified write, which the paper drops, is kept too. A remapped pair whose events lie in no common `⊑`-down-set is dropped, as it is in the paper. Without a join this is: both events in one thread, or one of them in the sequential prefix before the fork. A parallel block followed by a continuation is a join, and there a pair across the block's threads is anchored at a continuation event, as it is in the paper when that event is a justified write.
- **Why**: MoRDor's sMRD coherence uses `hb` over `ppo` (C1). The paper's cut leaves the events of a thread after its last justified write unordered. A thread that only reads would have an empty `ppo`, and coherence would admit CoRR violations. Leaving `ppo_sync` and `ppo_loc` uncut, as MoRDor did before, let write elision move their pairs across threads.
- **Consequences**:
  - Of the paper's cut, measured on the experiment branch `ppo-trunc-experiment` (30b1ff4, `MORDOR_PPO_TRUNC=paper` cuts all four parts to the justification windows): 21 `[sMRD]` verdicts flip, all through sMRD coherence.
  - Of the uncut parts, as before this cut: 28,993 cross-thread `ppo` pairs in 346 of 461 tests, counted on the goldens. They came from the remapped `ppo_sync` and `ppo_loc` pairs of a write that write elision folds into another thread's write: an initialising write (`x := 0` elided by a thread's `x := 1`), or a thread's own write. They made RC11-coherent executions fail coherence over `ppo`, and the closure made some fail `rhb` acyclicity: on `litmus-tests/own/SB+sc.lit`, some combinations' `ppo` contained both `(3,6)` and `(6,3)`. Cutting them changed no verdict. It admitted 283 more executions in 34 tests, each with an elided write; before, 16 of their combinations failed `rhb` acyclicity and the others coherence. It also merged executions that had differed only in such pairs, so 58 tests have fewer.
  - What remains across threads, counted on the goldens (excluding the initial, terminal and prefix events): 230 pairs in 8 tests. 12 are in `litmus-tests/symmrd/refinement/LB+UB+data.lit` and `LB+UBoff+data.lit`, whose continuation joins the threads. The other 218 are in 6 lock and monitor tests (`sevcik_thesis/`, `inverse-roach-motel/src.lit`). They are made by the closure through a backward pair: `ppo_sync` orders a `lock` before a later read, the read is forwarded from an initialising write, and the remapped pair runs from the `lock` back to that write, which is `⊑`-before it and so in its window. The write's own pairs to the other thread then compose with it. The paper's cut keeps the same backward pair in the window of a write after the `lock`. Since forwarding does not cross a `lock` or an acquire (#210, C3), these are gone, and the 12 in the two refinement tests are what remains.
- **Witness**: `litmus-tests/own/CoRR-ReaderNoWrites.lit`: under the paper's cut its `forbid (r1 = 1 && r2 = 0) [sMRD]` fails. `litmus-tests/own/CoWW-elided-init.lit`: with `x := 0` elided by `x := 1`, the uncut `ppo_loc` ordered `x := 1` before `x := 2`.

### F2. dp is remapped through the forwarding context

- **Paper**: Def. 4.9, `dp ≜ ⋃_{j∈J} (O(j_P) ∪ O(j_D)) × {w_j}`, and `φ` asks `† ∩ π₁(rf ∪ dp) = ∅`. No `dp` edge may start at an elided event.
- **MoRDor**: `src/executions.ml:Freeze.prepare` takes `dp` from the justifications of the writes that are not elided. It remaps the edges through the united forwarding context (`ForwardingContext.remap_rel`), so an edge from a forwarded read starts at the write it was forwarded from. `JustValidation.check_origins_elided` is still available as the paper's check.
- **Why**: the origin of a forwarded read's symbol is the read, which `δ` elides. Dropping the edge lets forwarding launder a dependency cycle, as in `litmus-tests/avoidoota/listing16.lit` (`r2 := y; z := r2; r3 := z; x := r3`).
- **Witness**: `litmus-tests/avoidoota/listing16.lit`.

### F3. Justifications need not share a forwarding context

- **Paper**: Def. 4.9: "all justifications `j ∈ J` share the forwarding context `δ`".
- **MoRDor**: `src/executions.ml:Freeze.prepare` unites the `fwd` and `we` of the chosen justifications into one context. `JustValidation.check_final` asks that the union be acyclic and functional, and `check_delta_not_on_path` that its events lie on the path.
- **Why**: each write's justifications are elaborated separately, so an exact match of contexts across writes is rare. The union is the context of the transformed program.
- **Witness**: none dedicated. Every test with forwarding in two threads freezes this way.

### F4. The execution predicate has more conjuncts

- **Paper**: Def. 4.9, `P ≜ ⋀_{j∈J} j_P ∧ ψ_δ`, and `φ` asks `∃g. ⟦P ∧ φ_rf⟧_g = ⊤`.
- **MoRDor**: `src/executions.ml:Freeze.prepare`'s `p_combined` also has the `⋎` of every event on the path (`path.p`, from `src/eventstructures.ml:generate_max_conflictfree_sets`) and the distinctness constraints `statex` (`calculate_dependencies`).
- **Why**: a branch with only reads in it has no justification, so in the paper nothing asks for its condition. MoRDor's execution follows the branch only if the condition can hold.
- **Witness**: none dedicated.

### F5. Allocation disjointness

- **Paper**: Def. 4.9 and Appendix I. Two allocations' regions, an address with its size, are disjoint (`⊗`) unless a free of one is `⊴`-between them, with `⊴ = (≤ ∪ rf ∪ dp)*`.
- **MoRDor**:
  - `src/interpret.ml:distinctness` and `src/executions.ml:calculate_dependencies` state disequality of the base addresses, without sizes. Pairs that `src/eventstructures.ml:may_reuse` may reuse are left out. That is decided on the structure: one may be freed before the other is allocated, judged by program order within a thread, and always possible across threads.
  - Per execution, `ReadFromValidation.adjacent_same_location_allocation_events` keeps two allocations apart unless a free of one is `rhb`-between them.
  - With `--disjoint-regions` (the default), addresses based on different bases differ whatever the offsets. `--overlapping-regions` keeps only the bases apart.
- **Why**: regions are not modelled yet. See the comment on `distinctness`.
- **Witness**: `litmus-tests/own/ReuseAcrossThreads.lit`, `NoReuseAcrossThreadsUnordered.lit`, `ReuseStalePointer.lit`, `NoReuseWhileLive.lit`, `ABA-CAS-Reuse.lit`.

## Coherence (§4.6)

The paper: the semantics is "the subset of the complete executions that are coherent according to the RC11 axiomatic constraints, excluding no-thin-air, and imposing that `dp ∪ ≤ ∪ rf` is acyclic". MoRDor checks `dp ∪ ppo ∪ rf` acyclicity during freezing (`src/executions.ml:Validation.rhb_acyclic`), with MoRDor's `ppo` (F1). Coherence is `src/coherence.ml:SMRD`.

### C1. hb is over ppo ∪ dp, not sb

- **Paper**: RC11's `hb = (sb ∪ sw)⁺`.
- **MoRDor**: `Coherence.SMRD.build_cache`, `hb = (ppo ∪ dp ∪ sw ∪ [Unlock]; lo; [Lock])⁺`, for some lock order `lo`.
- **Why**: deliberate. Coherence should not order what sMRD lets the compiler reorder. `ppo` keeps the outer `sb` legs of `sw` (`compute_ppo_sync`). It drops `sb` order between relaxed accesses to different locations. This is the reason for F1: `hb` needs `ppo` on a thread's last events.
- **Witness**: `litmus-tests/own/CoRR-ReaderNoWrites.lit`.

### C2. sw, release sequences, fences and psc

- **Paper**: RC11's `sw` with release sequences and fences, and `psc`.
- **MoRDor**: `Coherence.SMRD.build_cache`: RC11's `rs` and fence legs (#126, #170), but over `rfe` only, since within a thread `sw` would add the inner fence legs to `ppo`. `psc` is RC11's with `sb = po` (`CoherenceChecks.psc_acyclic`), because `hb` over `ppo` does not order an SC store before a later SC load.
- **Why**: this conforms, up to `rfe`, since #126 and #170. Before them sMRD had no fence synchronisation, no release sequences and no `psc`.
- **Witness**: `litmus-tests/own/SB+sc.lit`, `litmus-tests/own/RC11-RS-SameThreadRlx.lit`, `litmus-tests/c20/rs-example.lit`, `litmus-tests/own/MP+rel+fence-acq.lit`.

### C3. Elided writes are not in coherence

- **Paper**: Def. 4.12, `→WE` is any `W × W` pair with the forwarding relation, whatever the modes of the two writes and of the events between them. §4.6 checks RC11's axioms over the frozen execution.
- **MoRDor**: the forwarded and elided events are dropped from the execution (`src/executions.ml:Freeze.frame`, `e = path ∖ π₂(fwd ∪ we)`), so coherence does not see them. To keep that sound under RC11's `hb`, write elision is restricted where it is made (`src/elaborations.ml:ForwardElab.elision_blocked`, E4):
  - a release store is elided only by a release store (#168);
  - no write or fence of mode `rel` or stronger, `unlock` or `sc` access may lie po-between the elided and the eliding write (#207).

  Forwarding drops the forwarded event, and is restricted the other way round (`ForwardElab.forwarding_blocked`, #210):
  - no read or fence of mode `acq` or stronger, `lock`, or `sc` read or fence may lie po-between the source and the forwarded event, nor an `sc` write when the forwarded event is an `sc` read;
  - an acquire read is forwarded only from an acquire read, an `sc` read only from an `sc` read.

  Only sMRD and MRD elaborate (`MEMORY_MODEL.elaborates`). Every other model, RC11 included, rejects every execution with a forwarding or an elision (`src/coherence.ml:elisions_admitted`) and so is asked about the program's own events. Executions are still enumerated once for all the models of a run; each model's set is the subset it admits. IMM takes its own `ar` for no-thin-air (`allows_thin_air`), since `ar` has `rfe` but sMRD's `dp ∪ ppo ∪ rf` has every `rf`.
- **Why**: an elided write loses its happens-before obligations. With a release between the elided write `w₁` and the eliding write `w₂`, a thread that synchronises with the release happens after `w₁` but not after `w₂`, and could read a write coherence-before `w₁`. sMRD forbade that outcome only because remapping `ppo` through the elision turned the pair `(w₁, release)` into the backward pair `(w₂, release)`; RC11, whose `hb` is `(po ∪ sw)⁺`, admitted it (#207). A compiler does not sink a store past a release, so the restricted elisions are the dead-store eliminations it can make. An acquire between the two does not block: a store may sink past an acquire, an acquire adds `hb` predecessors to `w₂` that `w₁` does not have, and `ppo` orders nothing from `w₁` to the acquire for the remap to turn backward. An `sc` read blocks with the `sc` fence: sinking an `sc` store past an `sc` load is store buffering. Eliding a release store into a relaxed one loses the release sequence that the relaxed store continues (#168, #170). Forwarding of every kind drops the po-later event `e₂` and lets `e₁` stand for it: load forwarding (`R × R`) and store forwarding (`W × R_rlx`) satisfy the read at `e₁`, and store-store forwarding (`W × W_rlx`, redundant-store elimination) keeps `e₁` and drops the store of the same value. Each is `e₂` hoisted up to `e₁` and then eliminated next to it. A compiler may hoist an access above a release, into what it publishes, but not above an acquire, so forwarding is the mirror of elision. An acquire `a` between them is ordered before `e₂` by `ppo`, and the remap turns `(a, e₂)` into the backward pair `(a, e₁)`; sMRD used to forbid what such a forwarding admitted only through that pair, or not at all. Forwarding an acquire read from a weaker one drops its synchronisation. Hoisting an `sc` read above an `sc` write is store buffering. A release between does not block: `ppo` orders nothing from a release to a later event, so there is no pair to turn backward. Forwarding and elision are sMRD's account of compiler transformations, and the other models are models of the program as written.
- **Consequences**: on the goldens, no verdict changes. Executions with an elision across a release are gone from 9 sMRD tests (opts/we-fence-remap 16 → 5); all but that one lose only elisions of an initialising write across a thread's release fence, release store or `unlock`. Under the other models every elaborated execution is gone. Over all models and the corpus (the model matrix), RC11, the C11 family, SC, TSO, sMRD and MRD change no verdict; 14 weaker models (Coherence, RA, SRA, WRA, PC, PRAM, Local, Slow, POCausal, RYW, MR, MW, CRC, IMM) lose the outcomes only compiler transformations reach, such as `esop_problem/RRE.lit` and JCTC2, since they take `dp ∪ ppo ∪ rf` over the program's own dependencies for no-thin-air. IMM, deciding no-thin-air by its own `ar`, now allows `own/JCTC12.lit`, which IMM forbids through `addr;po`: MoRDor's IMM takes sMRD's `dp` for its `deps` (#63). No outcome that RC11 allows is one sMRD forbids.
- **Consequences of the forwarding rule** (#210), on the goldens: no verdict changes. 11 sMRD tests lose executions (10,861 → 10,641 sMRD executions over the corpus), all with forwarding across an acquire or a `lock`: the Ševčík roach-motel, monitor and lock tests, `inverse-roach-motel/src`, `own/ORI`, `ORI2`, `basic/rw`, `popl_grounding/RNGb` and `own/RSE-across-acquire`. Of the `ppo` pairs of sMRD executions that are not in `po`, the po-backward ones go from 77 in 9 tests to none, and the others from 384 to 24, all in `symmrd/refinement/LB+UB+data.lit` and `LB+UBoff+data.lit`, whose continuation joins the threads (F1). With `ppo` cut to `ppo ∩ po` in sMRD coherence, no verdict changes; before, `own/RSE-across-acquire.lit` flipped. On each of the 914 assertion conditions of the corpus (451 tests; RC11 refuses the 13 with locks), sMRD admits an execution satisfying it whenever RC11 does, under every mode of `MORDOR_FWD_SYNC`. Under `rel` only `RNGb` loses an execution, under `sc` none, and `both` is `acq`. Without the rule sMRD allowed message-passing outcomes that RC11 forbids (`own/LF-across-acquire.lit`, `LF-into-acquire.lit`, `LF-sc-across-sc-store.lit`, `LF-across-lock.lit`); the corpus had none.
- **Witness**: `litmus-tests/own/WE-across-release.lit`, `litmus-tests/own/RSE-across-acquire.lit`, `litmus-tests/own/LF-across-acquire.lit`, `litmus-tests/own/SF-across-acquire.lit`, `litmus-tests/own/LF-across-lock.lit`, `litmus-tests/own/LF-into-acquire.lit`, `litmus-tests/own/LF-sc-across-sc-store.lit`, `litmus-tests/own/LF-across-release.lit` (forwarding across a release is kept), `litmus-tests/own/RC11-RS-SameThreadRlx.lit`, `litmus-tests/own/relaxed-store-elided.lit`, `litmus-tests/popl_bridging/rfi is not always preserved.lit` (IMM).

### C4. co relates writes whose locations must be equal

- **Paper**: `mo` is "a per-location total order over writes", without saying when two symbolic locations are the same.
- **MoRDor**: `src/coherence.ml:location_equality` puts two writes in one `co` class when `Solver.exeq` proves their locations equal under the execution's predicates `ex_p`. Allocations and frees are not in `co` under sMRD (`orders_allocations = false`).
- **Why**: a write through a pointer has to be ordered with the writes to the location it points at.
- **Witness**: `litmus-tests/own/ptr-overwrite-coherence.lit`.

### C5. No data races

- **Paper**: the language has no non-atomic accesses (I5), so RC11's race clause does not arise.
- **MoRDor**: `Coherence.SMRD.data_races = None`. `na` accesses are relaxed under sMRD, and a race on them is not undefined behaviour.
- **Witness**: `litmus-tests/own/SB+na-smrd.lit`: undefined under RC11, defined under sMRD.

## Assertions and undefined behaviour (Appendix G)

### A1. Final values come from an admitted coherence order

- **Paper**: no final-state assertions.
- **MoRDor**: `src/assertion.ml:ConditionChecker.check_with_solver`. `@x`, or a bare global in a condition, is the value of the last write to `x`. A write through a pointer counts when its location is necessarily `x` under the execution's predicates. Where `po` leaves two such writes unordered, the condition holds if it holds for the co-maximal writes of some coherence order under which the model admits the execution (#124, #137).
- **Witness**: `litmus-tests/own/atloc-racing-writes.lit`, `atloc-racing-sc-stores.lit`, `atloc-alias.lit`, `atloc-noalias.lit`.

### A2. Undefined behaviour is defined over rhb

- **Paper**: Appendix G gives candidate definitions of executed undefined behaviour over `⊴ = rf ∪ dp ∪ ≤`. They compare reads, writes, allocations and frees that `⊴` does not order.
- **MoRDor**: `src/assertion.ml:UBValidation` and `src/executions.ml:Freeze.ub_constraint`, with `rhb = (ppo ∪ fj ∪ dp ∪ rf)⁺`, where `fj` is the fork-join order. An execution has undefined behaviour if any of the following holds:
  - a read reads from a free;
  - a write to an allocation is not `rhb`-before a free of it;
  - an access to an allocation is not `rhb`-after the allocation.

  Pointers are followed through `rf` to the allocation or global they are based on.
- **Why**: the candidates in Appendix G are not final, and MoRDor needs a definition the solver can state.
- **Witness**: `litmus-tests/own/FreeRace.lit`, `litmus-tests/own/FreeRace2.lit`.
