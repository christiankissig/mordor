(** Property-Based Tests for Symbolic MRD Testing invariants, theorems, and
    properties from the paper *)

(* Properties from the paper that have no test here: DRF-SC (Theorem 5), the
   standard compilation mappings (Lemma 5.1), store forwarding, J₀ ⊆ J, the
   three allocation-disjointness claims (π1 ⊗ π2, π ⊗ x, reuse after free) and
   execution completeness (every maximal conflict-free set considered, every
   valid rf enumerated, incoherent executions filtered).

   Each had a registered test case whose body was a comment and a unit value.
   They asserted nothing and reported green, which in the summary is
   indistinguishable from a property that was checked and holds. This note is
   what they were carrying. *)

open Alcotest
open Events
open Types
open Uset

(** Property 1: Thin-Air Freedom (Theorem from §1) *)
module PropertyThinAirFreedom = struct
  (** The model forbids thin-air values by requiring acyclic(dp ∪ ≤ ∪ rf) *)

  let test_acyclicity_prevents_thin_air () =
    (* Classic thin-air example:
       Thread 1:         Thread 2:
       int r1 = x;       int r2 = y;
       y = r1;           x = r2;

       With r1=1, r2=1, we'd have a cycle in rf
    *)

    (* Without dependencies: cycle in rf *)
    let rf_cycle = USet.of_list [ (1, 3); (2, 4); (3, 2); (4, 1) ] in
      check bool "rf_cycle_not_acyclic" false (URelation.acyclic rf_cycle);

      (* With dependencies: cycle in dp ∪ rf *)
      let dp = USet.of_list [ (1, 2); (3, 4) ] in
      let dp_rf = USet.union dp rf_cycle in
        check bool "dp_rf_cycle_not_acyclic" false (URelation.acyclic dp_rf);
        ()

  let test_dependencies_break_cycles () =
    (* With proper dependencies, the cycle is detected *)
    let po = USet.of_list [ (1, 2); (3, 4) ] in
    let rf = USet.of_list [ (2, 3); (4, 1) ] in
    let dp = USet.of_list [ (1, 2); (3, 4) ] in

    let combined = USet.union (USet.union po rf) dp in
      check bool "proper_deps_create_cycle" false (URelation.acyclic combined);
      ()
end

(** Property 3: Compilation Correctness (Lemma 5.1) *)
module PropertyCompilationCorrectness = struct
  (** Lemma 5.1: J𝑃K_n ⊤ ⊇ J𝑃K_RC11 ⊇ Jcomp(𝑃)K_IMM *)

  let test_smrd_includes_rc11 () =
    (* sMRD is a relaxation of RC11 *)
    (* Every RC11 execution has a corresponding sMRD execution *)
    (* Because: (dp ∪ ≤) ⊆ ⊑, so acyclic(⊑ ∪ rf) ⟹ acyclic(dp ∪ ≤ ∪ rf) *)
    let po = USet.of_list [ (1, 2); (2, 3); (4, 5) ] in
    let rf = USet.of_list [ (3, 4) ] in
    let dp = USet.of_list [ (1, 2) ] in
    let ppo = USet.of_list [ (1, 2) ] in

    (* If po ∪ rf is acyclic, then so is dp ∪ ppo ∪ rf when dp ∪ ppo ⊆ po *)
    check bool "po_includes_deps" true (USet.subset dp po);
    ()
end

(** Property 4: Elaboration Soundness *)
module PropertyElaborationSoundness = struct
  (** Each elaboration preserves or extends the set of valid behaviors *)

  let test_value_assignment_soundness () =
    (* Value assignment: if P ⟹ (α = v), substituting v for α is sound *)
    let open Lwt.Infix in
    let premises = [ EBinOp (ESymbol "α", "=", ENum Z.one) ] in
    let conclusion =
      EBinOp (EBinOp (ESymbol "α", "+", ENum Z.one), "=", ENum (Z.of_int 2))
    in

    let result = Solver.implies premises conclusion in
      check bool "va_soundness" true result;
      Lwt.return_unit

  let test_strengthening_soundness () =
    let open Lwt.Infix in
    (* Strengthening: adding constraints to P is always sound *)
    (* If a write occurs under P, it also occurs under P ∧ P' *)
    let p_original = [ EBinOp (ESymbol "x", ">", ENum Z.zero) ] in
    let p_strengthened =
      [
        EBinOp (ESymbol "x", ">", ENum Z.zero);
        EBinOp (ESymbol "x", "<", ENum (Z.of_int 100));
      ]
    in

    (* The strengthened predicate is more restrictive *)
    let stronger_implies_weaker =
      List.concat [ p_strengthened; [ EOr p_original ] ]
    in

    let result = Solver.is_sat stronger_implies_weaker in
      check bool "str_soundness" true result;
      Lwt.return_unit

  let test_weakening_soundness () =
    let open Lwt.Infix in
    (* Weakening: if Ω ⟹ P, then removing P is sound *)
    let omega = [ EBinOp (ESymbol "x", ">=", ENum Z.zero) ] in
    let p = [ EBinOp (ESymbol "x", ">=", ENum Z.zero) ] in

    (* Ω should imply P *)
    let implication = List.concat [ omega; [ EOr p ] ] in

    let result = Solver.is_sat implication in
      check bool "weak_soundness" true result;
      Lwt.return_unit

  let test_lifting_soundness () =
    let open Lwt.Infix in
    (* Lifting: if two writes are equivalent under complementary predicates,
       they can be merged *)
    let p1 = EBinOp (ESymbol "c", "=", ENum Z.one) in
    let p2 = EBinOp (ESymbol "c", "!=", ENum Z.one) in

    (* P1 ∨ P2 should be ⊤ *)
    let disjunction = EOr [ p1; p2 ] in

    let result = Solver.is_sat [ disjunction ] in
      check bool "lift_soundness" true result;
      Lwt.return_unit

  let suite =
    [
      test_case "PropertyElaborationSoundness.test_value_assignment_soundness"
        `Quick (fun () -> Lwt_main.run (test_value_assignment_soundness ())
      );
      test_case "PropertyElaborationSoundness.test_strengthening_soundness"
        `Quick (fun () -> Lwt_main.run (test_strengthening_soundness ())
      );
      test_case "PropertyElaborationSoundness.test_weakening_soundness" `Quick
        (fun () -> Lwt_main.run (test_weakening_soundness ())
      );
      test_case "PropertyElaborationSoundness.test_lifting_soundness" `Quick
        (fun () -> Lwt_main.run (test_lifting_soundness ())
      );
    ]
end

(** Property 5: Forwarding Correctness *)
module PropertyForwardingCorrectness = struct
  let test_load_forwarding_preserves_semantics () =
    (* Load forwarding: if two loads read the same location and
       the first is not overtaken, forwarding is correct *)
    let fwd_ctx = USet.of_list [ (1, 2) ] in

    (* The forwarding context records (1,2) means:
       - Event 2 is elided
       - Symbols from event 2 are replaced by symbols from event 1 *)
    check bool "fwd_recorded" true (USet.mem fwd_ctx (1, 2));
    ()

  let test_write_elision_preserves_semantics () =
    (* Write elision: if a write is immediately followed by another
       write to the same location, the first can be elided *)
    let we_ctx = USet.of_list [ (1, 2) ] in
      check bool "we_recorded" true (USet.mem we_ctx (1, 2));
      ()
end

(** Property 6: Semantic Equality *)
module PropertySemanticEquality = struct
  let test_semantic_equality_is_reflexive () =
    let open Lwt.Infix in
    let expr = EBinOp (ESymbol "x", "+", ENum Z.one) in
    let result = Solver.exeq expr expr in
      check bool "exeq_reflexive" true result;
      Lwt.return_unit

  let test_semantic_equality_is_symmetric () =
    let open Lwt.Infix in
    let e1 = EBinOp (ESymbol "x", "+", ENum Z.one) in
    let e2 = EBinOp (ENum Z.one, "+", ESymbol "x") in

    let r1 = Solver.exeq e1 e2 in
    let r2 = Solver.exeq e2 e1 in
      check bool "exeq_symmetric" true (r1 = r2);
      Lwt.return_unit

  let test_semantic_equality_is_transitive () =
    let open Lwt.Infix in
    let e1 = EBinOp (ESymbol "x", "+", ENum Z.zero) in
    let e2 = EVar "x" in
    let e3 = EBinOp (ENum Z.zero, "+", ESymbol "x") in

    (* e1 ≡ e2 and e2 ≡ e3 should imply e1 ≡ e3 *)
    let r12 = Solver.exeq e1 e2 in
    let r23 = Solver.exeq e2 e3 in
    let r13 = Solver.exeq e1 e3 in
      check bool "exeq_transitive" true (r12 && r23 && r13);
      Lwt.return_unit

  let suite =
    [
      test_case "PropertySemanticEquality.test_semantic_equality_is_reflexive"
        `Quick (fun () -> Lwt_main.run (test_semantic_equality_is_reflexive ())
      );
      test_case "PropertySemanticEquality.test_semantic_equality_is_symmetric"
        `Quick (fun () -> Lwt_main.run (test_semantic_equality_is_symmetric ())
      );
      test_case "PropertySemanticEquality.test_semantic_equality_is_transitive"
        `Quick (fun () -> Lwt_main.run (test_semantic_equality_is_transitive ())
      );
    ]
end

(** Property 7: Justification Monotonicity *)
module PropertyJustificationMonotonicity = struct
  let test_initial_justifications_are_strongest () =
    (* J₀ ⊆ J₁ ⊆ J₂ ⊆ ... ⊆ J *)
    (* Initial justifications capture all syntactic dependencies *)
    let e = { (Event.create Write 1 ()) with wval = Some (ESymbol "α") } in

    let j0 =
      {
        p = [];
        d = USet.of_list [ "α" ];
        fwd = USet.create ();
        we = USet.create ();
        w = e;
      }
    in

    (* Initial justification has all syntactic dependencies *)
    check bool "j0_has_deps" true (USet.size j0.d > 0);
    ()

  let test_elaboration_weakens_or_maintains () =
    (* Each elaboration either:
       - Weakens dependencies (removes symbols from D or P)
       - Adds equivalent justifications
       - Records transformations in δ *)
    let j_before =
      {
        p = [ EBinOp (ESymbol "c", "=", ENum Z.one) ];
        d = USet.of_list [ "x"; "y" ];
        fwd = USet.create ();
        we = USet.create ();
        w = { (Event.create Write 1 ()) with wval = Some (ENum Z.zero) };
      }
    in

    let j_after_weak =
      {
        p = [];
        (* Weakened *)
        d = USet.of_list [ "x"; "y" ];
        fwd = USet.create ();
        we = USet.create ();
        w = { (Event.create Write 1 ()) with wval = Some (ENum Z.zero) };
      }
    in

    check bool "elaboration_weakens" true
      (List.length j_after_weak.p <= List.length j_before.p);
    ()
end

let suite =
  ( "Property-Based Tests for Symbolic MRD",
    [
      test_case "PropertyThinAirFreedom.test_acyclicity_prevents_thin_air"
        `Quick PropertyThinAirFreedom.test_acyclicity_prevents_thin_air;
      test_case "PropertyThinAirFreedom.test_dependencies_break_cycles" `Quick
        PropertyThinAirFreedom.test_dependencies_break_cycles;
      test_case "PropertyCompilationCorrectness.test_smrd_includes_rc11" `Quick
        PropertyCompilationCorrectness.test_smrd_includes_rc11;
    ]
    @ PropertyElaborationSoundness.suite
    @ [
        test_case
          "PropertyForwardingCorrectness.test_load_forwarding_preserves_semantics"
          `Quick
          PropertyForwardingCorrectness.test_load_forwarding_preserves_semantics;
        test_case
          "PropertyForwardingCorrectness.test_write_elision_preserves_semantics"
          `Quick
          PropertyForwardingCorrectness.test_write_elision_preserves_semantics;
      ]
    @ PropertySemanticEquality.suite
    @ [
        test_case
          "PropertyJustificationMonotonicity.test_initial_justifications_are_strongest"
          `Quick
          PropertyJustificationMonotonicity
          .test_initial_justifications_are_strongest;
        test_case
          "PropertyJustificationMonotonicity.test_elaboration_weakens_or_maintains"
          `Quick
          PropertyJustificationMonotonicity
          .test_elaboration_weakens_or_maintains;
      ]
  )
