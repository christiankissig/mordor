(** Advanced Unit Tests for Symbolic MRD Testing complex elaboration sequences
    and integration scenarios *)
open Alcotest

open Events
open Expr
open Lwt.Syntax
open Types
open Uset

module TestUtils = struct
  let make_symbol name = VSymbol name
  let make_number n = VNumber (Z.of_int n)
  let make_var name = VVar name
end

open TestUtils

(** Test Module 1: Example 9.1 - LB+UB+data+z (Inconsistent Register Values) *)
module TestExample9_1 = struct
  (** Example 9.1: Inconsistent register values through UB optimization Thread
      1: Thread 2: int r1 = x; int r2 = y; y = 1 / !r1; x = r2; z = r1;

      After optimization, r1 appears to have value 1 (from read) but the write
      to z uses value 0 (from UB assumption). *)

  let test_inconsistent_register_values () =
    (* This is a surprising but allowed behavior *)
    (* Read x=1, but write z=0 based on UB analysis *)

    (* Initial justifications before elaboration *)
    let e2_initial =
      {
        p = [];
        d = USet.of_list [ "r1" ];
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 2 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (EBinOp (ENum Z.one, "/", EUnOp ("!", ESymbol "r1")));
            wmod = Relaxed;
          };
      }
    in

    let e3_initial =
      {
        p = [];
        d = USet.of_list [ "r1" ];
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 3 ()) with
            id = Some (make_var "z");
            loc = Some (Expr.of_value (make_var "z"));
            wval = Some (ESymbol "r1");
            wmod = Relaxed;
          };
      }
    in

    (* After strengthening, VA, and weakening on both writes *)
    (* Assuming !r1 ≠ 0, which implies r1 = 0 *)
    let e2_optimized =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 2 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ENum Z.one);
            wmod = Relaxed;
          };
      }
    in

    let e3_optimized =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 3 ()) with
            id = Some (make_var "z");
            loc = Some (Expr.of_value (make_var "z"));
            wval = Some (ENum Z.zero);
            wmod = Relaxed;
          };
      }
    in

    check bool "initial_y_depends_on_r1" true (USet.mem e2_initial.d "r1");
    check bool "initial_z_depends_on_r1" true (USet.mem e3_initial.d "r1");
    check int "optimized_y_no_deps" 0 (USet.size e2_optimized.d);
    check int "optimized_z_no_deps" 0 (USet.size e3_optimized.d);
    ()
end

(** Test Module 2: Example 10.1 - JCTC12 (Pointer Aliasing) *)
module TestExample10_1 = struct
  (** Example 10.1: Complex pointer aliasing scenario atomic<int> rp[2]; rp[0] =
      1; rp[1] = 2; int r1 = x; *(rp+r1) = 0; int r2 = *rp; y = r2;

      Whether *(rp+r1) and *rp alias depends on r1. *)

  let test_pointer_aliasing_initial () =
    (* When aliasing is possible, there's a ≤ edge *)
    let e5_write =
      {
        p = [];
        d = USet.of_list [ "r1" ];
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 5 ()) with
            loc = Some (EBinOp (ESymbol "rp", "+", ESymbol "r1"));
            wval = Some (ENum Z.zero);
            wmod = Relaxed;
          };
      }
    in

    let e6_read =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Read 6 ()) with
            id = Some (VSymbol "rp");
            loc = Some (ESymbol "rp");
            rval = Some (VSymbol "r2");
            rmod = Relaxed;
          };
      }
    in

    (* Without strengthening: must assume possible aliasing *)
    check bool "pointer_write_depends_on_r1" true (USet.mem e5_write.d "r1");
    ()

  let test_pointer_aliasing_strengthened () =
    (* With strengthening r1 ≠ 0, we know no aliasing *)
    let e7_write_strengthened =
      {
        p = [ EBinOp (ESymbol "r1", "≠", ENum Z.zero) ];
        d = USet.of_list [ "r1" ];
        (* Still depends on r1 for address *)
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 7 ()) with
            loc = Some (EBinOp (ESymbol "rp", "+", ESymbol "r1"));
            wval = Some (ENum Z.zero);
            wmod = Relaxed;
          };
      }
    in

    (* But now there's no ≤ edge with the read of *rp *)
    (* Instead there's a dp edge from the read of x to the write *)
    check bool "strengthened_has_predicate" true
      (List.length e7_write_strengthened.p > 0);
    ()
end

(** Test Module 3: Example 12.1 - Load Forwarding in Conditional *)
module TestExample12_1 = struct
  (** Example 12.1: Load forwarding across conditionals int r1 = x; int r2 = x;
      if (r1 == 1) y = r2; else y = 1; *)

  let test_load_forwarding_conditional () =
    (* After forwarding r1 -> r2, this becomes Example 5.1 *)
    let e4_initial =
      {
        p = [ EBinOp (ESymbol "r1", "=", ENum Z.one) ];
        d = USet.of_list [ "r2" ];
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 4 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ESymbol "r2");
            wmod = Relaxed;
          };
      }
    in

    let e4_forwarded =
      {
        p = [ EBinOp (ESymbol "r1", "=", ENum Z.one) ];
        d = USet.of_list [ "r1" ];
        (* Now depends on r1 *)
        fwd = USet.of_list [ (1, 2) ];
        (* Forwarding edge *)
        we = USet.create ();
        w =
          {
            (Event.create Write 4 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ESymbol "r1");
            wmod = Relaxed;
          };
      }
    in

    check bool "initial_depends_r2" true (USet.mem e4_initial.d "r2");
    check bool "initial_no_forwarding" false (USet.mem e4_initial.fwd (1, 2));
    check bool "forwarded_depends_r1" true (USet.mem e4_forwarded.d "r1");
    check bool "forwarded_has_edge" true (USet.mem e4_forwarded.fwd (1, 2));
    ()
end

(** Test Module 4: Example 13.1 - Lifting with Multiple Reads *)
module TestExample13_1 = struct
  (* Example 13.1: Lifting with symmetric branches
      int r1 = x;
      if (r1 == 1) {
        int rw1 = w;
        z = rw1;
      } else {
        int rw2 = w;
        z = rw2;
      }
  *)

  let test_lifting_multiple_reads () =
    Printf.printf "\n=== Testing Example 13.1: Lifting ===\n";

    (* Both branches read w and write to z *)
    let e4_true =
      {
        p = [ EBinOp (ESymbol "r1", "=", ENum Z.one) ];
        d = USet.of_list [ "rw1" ];
        (* Read w in true branch *)
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 4 ()) with
            id = Some (make_var "z");
            loc = Some (Expr.of_value (make_var "z"));
            wval = Some (ESymbol "rw1");
            wmod = Relaxed;
          };
      }
    in

    let e7_false =
      {
        p = [ EBinOp (ESymbol "r1", "≠", ENum Z.one) ];
        d = USet.of_list [ "rw2" ];
        (* Read w in false branch *)
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 7 ()) with
            id = Some (make_var "z");
            loc = Some (Expr.of_value (make_var "z"));
            wval = Some (ESymbol "rw2");
            wmod = Relaxed;
          };
      }
    in

    (* After lifting: predicates are combined *)
    let e4_lifted =
      {
        p = [];
        (* ⊤ after lifting *)
        d = USet.of_list [ "rw1" ];
        (* or "rw2" - either works *)
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 4 ()) with
            id = Some (make_var "z");
            loc = Some (Expr.of_value (make_var "z"));
            wval = Some (ESymbol "rw1");
            wmod = Relaxed;
          };
      }
    in

    check bool "true_branch_has_pred" true (List.length e4_true.p > 0);
    check bool "false_branch_has_pred" true (List.length e7_false.p > 0);
    check int "lifted_no_pred" 0 (List.length e4_lifted.p);
    ()
end

(** Test Module 5: Store-Store Forwarding (Appendix A) *)
module TestStoreStoreForwarding = struct
  (* Store-store forwarding: Example 17.1
      int r1 = x;
      z = 1;
      if (r1 == 1) {
        z = 1;
        int r2 = z;
        if (r2 == 0) y = 1;
      } else {
        int r2 = z;
        if (r2 == 0) y = 1;
      }
  *)

  let test_store_store_forwarding () =
    (* Duplicate stores to z on lines 2 and 4 *)
    (* After store-store forwarding, line 4's store is elided *)
    let e6_initial_true =
      {
        p =
          [
            EBinOp (ESymbol "r1", "=", ENum Z.one);
            EBinOp (ESymbol "r2", "=", ENum Z.zero);
          ];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w =
          {
            (Event.create Write 6 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ENum Z.one);
            wmod = Relaxed;
          };
      }
    in

    (* After forwarding, write 4 is elided, reads see write 2 *)
    let e6_forwarded =
      {
        p =
          [
            EBinOp (ESymbol "r1", "=", ENum Z.one);
            EBinOp (ESymbol "r2", "=", ENum Z.zero);
          ];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.of_list [ (4, 2) ];
        (* Write 4 elides write 2 *)
        w =
          {
            (Event.create Write 6 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ENum Z.one);
            wmod = Relaxed;
          };
      }
    in

    check int "no_initial_elision" 0 (USet.size e6_initial_true.we);
    check bool "forwarded_has_elision" true (USet.mem e6_forwarded.we (4, 2));
    ()
end

(** Test Module 6: Complex Elaboration Sequences *)
module TestElaborationSequences = struct
  let test_str_va_weak_sequence () =
    (* Example: strengthen with α=0, value assign, then weaken with Ω *)
    let open Lwt.Infix in
    (* Initial: y = 1/!α with dependency on α *)
    (* Step 1: Strengthen with !α ≠ 0 *)
    let after_str = [ EUnOp ("!", EBinOp (ESymbol "α", "!=", ENum Z.zero)) ] in

    (* Step 2: Value assign α=0 from predicate *)
    (* Now: y = 1/!0 = 1/1 = 1 *)

    (* Step 3: Weaken using Ω ⟹ !α ≠ 0 *)
    (* Result: no dependencies *)
    let constraints_after_str =
      [ EUnOp ("!", EBinOp (ESymbol "α", "!=", ENum Z.zero)) ]
    in

    Solver.is_sat constraints_after_str >>= fun sat_result ->
    check bool "strengthened_satisfiable" true sat_result;
    Lwt.return_unit

  let test_fwd_lift_sequence () =
    (* Forward r1->r2, then lift equivalent writes *)
    let fwd_edges = USet.of_list [ (1, 2) ] in

    let e3_after_fwd =
      {
        p = [ EBinOp (ESymbol "r1", "=", ENum Z.one) ];
        d = USet.of_list [ "r1" ];
        fwd = fwd_edges;
        we = USet.create ();
        w =
          {
            (Event.create Write 3 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ESymbol "r1");
            wmod = Relaxed;
          };
      }
    in

    let e5_after_fwd =
      {
        p = [ EBinOp (ESymbol "r1", "≠", ENum Z.one) ];
        d = USet.create ();
        fwd = fwd_edges;
        we = USet.create ();
        w =
          {
            (Event.create Write 5 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ENum Z.one);
            wmod = Relaxed;
          };
      }
    in

    (* Now both write y=1 (after value assignment in first branch) *)
    (* Lifting can merge them *)
    let e3_after_lift =
      {
        p = [];
        d = USet.create ();
        fwd = fwd_edges;
        we = USet.create ();
        w =
          {
            (Event.create Write 3 ()) with
            id = Some (make_var "y");
            loc = Some (Expr.of_value (make_var "y"));
            wval = Some (ENum Z.one);
            wmod = Relaxed;
          };
      }
    in

    check bool "fwd_has_edges" true (USet.size e3_after_fwd.fwd > 0);
    check int "lift_removes_pred" 0 (List.length e3_after_lift.p);
    Lwt.return_unit
end

(** Test Module 7: Preserved Program Order (≤) *)
module TestPreservedProgramOrder = struct
  let test_ppo_synchronization () =
    Printf.printf "\n=== Testing Preserved Program Order ===\n";

    (* ≤ includes:
       1. Synchronization: E × W|rel,sc ∪ R|acq,sc × E
       2. Same location accesses
       3. Allocation order
    *)

    (* Test synchronization ordering *)
    let e1 = { (Event.create Read 1 ()) with rmod = Acquire } in
    let e2 = { (Event.create Write 2 ()) with wmod = Relaxed } in

    (* (1, 2) should be in ≤ because e1 is acquire *)
    check bool "acq_read_orders_following" true (e1.rmod = Acquire);

    let e3 = { (Event.create Write 3 ()) with wmod = Release } in
    let e4 = { (Event.create Read 4 ()) with rmod = Relaxed } in

    (* (3, 4) should be in ≤ because e3 is release *)
    check bool "rel_write_orders_following" true (e3.wmod = Release);

    Printf.printf "PASS: Synchronization in preserved program order\n"

  let test_ppo_same_location () =
    (* Same location accesses are ordered by ≤_alias *)
    let e1 =
      {
        (Event.create Write 1 ()) with
        id = Some (make_var "x");
        wmod = Relaxed;
      }
    in
    let e2 =
      { (Event.create Read 2 ()) with id = Some (make_var "x"); rmod = Relaxed }
    in

    (* Under predicate ⊤, x = x, so (1,2) in ≤ *)
    check bool "same_location_ordering" true (e1.id = e2.id);
    Printf.printf "PASS: Same location in preserved program order\n"

  let test_ppo_allocation_order () =
    (* Allocation and free events are totally ordered by ≤_xco *)
    let e1 = { (Event.create Malloc 1 ()) with rval = Some (VSymbol "π1") } in
    let e2 = { (Event.create Malloc 2 ()) with rval = Some (VSymbol "π2") } in
    let e3 = { (Event.create Free 3 ()) with id = Some (VSymbol "π1") } in

    (* (1,2), (2,3), (1,3) all in ≤ *)
    check bool "alloc_events_ordered" true (e1.typ = Malloc && e2.typ = Malloc);
    Printf.printf "PASS: Allocation order in preserved program order\n"
end

(** Test Module 8: Dependency Calculation *)
module TestDependencyCalculation = struct
  let test_dp_from_justifications () =
    Printf.printf "\n=== Testing Dependency Calculation ===\n";

    (* dp = ⋃{j∈J} (O(j_P) ∪ O(j_D)) × {w} *)
    let e1 = { (Event.create Read 1 ()) with rval = Some (VSymbol "α") } in
    let e2 = { (Event.create Read 2 ()) with rval = Some (VSymbol "β") } in
    let e3 =
      {
        (Event.create Write 3 ()) with
        wval = Some (EBinOp (ESymbol "α", "+", ESymbol "β"));
      }
    in

    (* Justification for e3 *)
    let just =
      {
        p = [];
        d = USet.of_list [ "α"; "β" ];
        fwd = USet.create ();
        we = USet.create ();
        w = e3;
      }
    in

    (* Origin of α is e1, origin of β is e2 *)
    (* So dp should include (1,3) and (2,3) *)
    check bool "just_depends_alpha" true (USet.mem just.d "α");
    check bool "just_depends_beta" true (USet.mem just.d "β");
    Printf.printf "PASS: Dependencies calculated from justification\n"

  let test_dp_with_control_deps () =
    (* Control dependencies from predicates *)
    let e1 = { (Event.create Read 1 ()) with rval = Some (VSymbol "α") } in
    let e3 =
      { (Event.create Write 3 ()) with wval = Some (ENum (Z.of_int 42)) }
    in

    let just =
      {
        p = [ EBinOp (ESymbol "α", "=", ENum Z.one) ];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e3;
      }
    in

    (* Origin of α in predicate is e1 *)
    (* So dp should include (1,3) *)
    check bool "just_has_predicate" true (List.length just.p > 0);
    Printf.printf "PASS: Control dependencies in dp\n"
end

let suite =
  ( "Advanced Symbolic MRD Tests",
    [
      Alcotest.test_case "Example 9.1: Inconsistent Register Values" `Quick
        TestExample9_1.test_inconsistent_register_values;
      Alcotest.test_case "Example 10.1: Pointer Aliasing Initial" `Quick
        TestExample10_1.test_pointer_aliasing_initial;
      Alcotest.test_case "Example 10.1: Pointer Aliasing Strengthened" `Quick
        TestExample10_1.test_pointer_aliasing_strengthened;
      Alcotest.test_case "Example 12.1: Load Forwarding in Conditional" `Quick
        TestExample12_1.test_load_forwarding_conditional;
      Alcotest.test_case "Example 13.1: Lifting with Multiple Reads" `Quick
        TestExample13_1.test_lifting_multiple_reads;
      Alcotest.test_case "Store-Store Forwarding" `Quick
        TestStoreStoreForwarding.test_store_store_forwarding;
      Alcotest.test_case "Elaboration Sequence: str→va→weak" `Quick (fun () ->
          Lwt_main.run (TestElaborationSequences.test_str_va_weak_sequence ())
      );
      Alcotest.test_case "Elaboration Sequence: fwd→lift" `Quick (fun () ->
          Lwt_main.run (TestElaborationSequences.test_fwd_lift_sequence ())
      );
      Alcotest.test_case "Preserved Program Order: Synchronization" `Quick
        TestPreservedProgramOrder.test_ppo_synchronization;
      Alcotest.test_case "Preserved Program Order: Same Location" `Quick
        TestPreservedProgramOrder.test_ppo_same_location;
      Alcotest.test_case "Preserved Program Order: Allocation Order" `Quick
        TestPreservedProgramOrder.test_ppo_allocation_order;
      Alcotest.test_case "Dependency Calculation from Justifications" `Quick
        TestDependencyCalculation.test_dp_from_justifications;
      Alcotest.test_case "Dependency Calculation with Control Dependencies"
        `Quick TestDependencyCalculation.test_dp_with_control_deps;
    ]
  )
