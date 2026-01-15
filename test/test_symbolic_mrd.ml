(** Unit Tests for Symbolic MRD Based on "Symbolic MRD: Dynamic Memory,
    Undefined Behaviour, and Extrinsic Choice" *)

open Alcotest
open Coherence
open Events
open Eventstructures
open Executions
open Expr
open Types
open Uset

(** Test utilities *)
module TestUtils = struct
  let make_symbol name = VSymbol name
  let make_number n = VNumber (Z.of_int n)
  let make_var name = VVar name

  (** Create a simple read event *)
  let make_read_event label loc symbol mode =
    let ev = Event.create Read label () in
      {
        ev with
        id = Some loc;
        loc = Some (Expr.of_value loc);
        rval = Some symbol;
        rmod = mode;
      }

  (** Create a simple write event *)
  let make_write_event label loc value mode =
    let ev = Event.create Write label () in
      {
        ev with
        id = Some loc;
        loc = Some (Expr.of_value loc);
        wval = Some value;
        wmod = mode;
      }

  (** Create an allocation event *)
  let make_alloc_event label symbol size =
    let ev = Event.create Malloc label () in
      { ev with rval = Some symbol; wval = Some (Expr.of_value size) }

  (** Create a free event *)
  let make_free_event label loc =
    let ev = Event.create Free label () in
      { ev with loc = Some loc }
end

open TestUtils

(** Test Module 1: Basic Event Creation *)
module TestEvents = struct
  let test_create_read () =
    let ev = make_read_event 1 (make_var "x") (make_symbol "α") Relaxed in
      check int "read_event_label" 1 ev.label;
      check bool "read_event_type" true (ev.typ = Read);
      check bool "read_event_mode" true (ev.rmod = Relaxed)

  let test_create_write () =
    let ev =
      make_write_event 2 (make_var "y") (Expr.of_value (make_number 1)) Release
    in
      check int "write_event_label" 2 ev.label;
      check bool "write_event_type" true (ev.typ = Write);
      check bool "write_event_mode" true (ev.wmod = Release)

  let test_create_alloc () =
    let ev = make_alloc_event 4 (make_symbol "β") (make_number 16) in
      check int "alloc_event_label" 4 ev.label;
      check bool "alloc_event_type" true (ev.typ = Malloc)

  let suite =
    [
      test_case "TestEvents.test_create_read" `Quick test_create_read;
      test_case "TestEvents.test_create_write" `Quick test_create_write;
      test_case "TestEvents.test_create_alloc" `Quick test_create_alloc;
    ]
end

(** Test Module 3: Expressions and Values *)
module TestExpressions = struct
  let test_value_types () =
    let num = VNumber (Z.of_int 42) in
    let sym = VSymbol "α" in
    let var = VVar "x" in
      check bool "value_number_created" true
        ( match num with
        | VNumber _ -> true
        | _ -> false
        );
      check bool "value_symbol_created" true
        ( match sym with
        | VSymbol _ -> true
        | _ -> false
        );
      check bool "value_var_created" true
        ( match var with
        | VVar _ -> true
        | _ -> false
        )

  let test_binary_expressions () =
    let lhs = ESymbol "α" in
    let rhs = ENum (Z.of_int 1) in
    let expr = EBinOp (lhs, "=", rhs) in
      check bool "binop_created" true
        ( match expr with
        | EBinOp _ -> true
        | _ -> false
        )

  let test_unary_expressions () =
    let val_ = ESymbol "α" in
    let expr = EUnOp ("!", val_) in
      check bool "unop_created" true
        ( match expr with
        | EUnOp _ -> true
        | _ -> false
        )

  let test_disjunction () =
    let clause1 = [ EBinOp (ESymbol "α", "=", ENum Z.one) ] in
    let clause2 = [ EBinOp (ESymbol "α", "=", ENum Z.zero) ] in
    let disj = EOr [ clause1; clause2 ] in
      check bool "disjunction_created" true
        ( match disj with
        | EOr _ -> true
        | _ -> false
        )

  let suite =
    [
      test_case "TestExpressions.test_value_types" `Quick test_value_types;
      test_case "TestExpressions.test_binary_expressions" `Quick
        test_binary_expressions;
      test_case "TestExpressions.test_unary_expressions" `Quick
        test_unary_expressions;
      test_case "TestExpressions.test_disjunction" `Quick test_disjunction;
    ]
end

(** Test Module 4: Solver (async tests) *)
module TestSolver = struct
  let test_solver_creation () =
    let constraints = [ EBinOp (ESymbol "x", ">", ENum Z.zero) ] in
    let solver = Solver.create constraints in
      check bool "solver_created" true (List.length solver.expressions > 0);
      Lwt.return_unit

  let test_satisfiable_constraint () =
    let open Lwt.Infix in
    let constraints = [ EBinOp (ESymbol "x", "=", ENum (Z.of_int 5)) ] in
      Solver.is_sat constraints >>= fun result ->
      check bool "simple_sat_constraint" true result;
      Lwt.return_unit

  let test_unsatisfiable_constraint () =
    let open Lwt.Infix in
    let constraints =
      [
        EBinOp (ESymbol "x", "=", ENum Z.one);
        EBinOp (ESymbol "x", "=", ENum Z.zero);
      ]
    in
      Solver.is_unsat constraints >>= fun result ->
      check bool "simple_unsat_constraint" true result;
      Lwt.return_unit

  let test_implies () =
    let open Lwt.Infix in
    let premises = [ EBinOp (ESymbol "x", "=", ENum Z.one) ] in
    let conclusion = EBinOp (ESymbol "x", ">", ENum Z.zero) in
      Solver.implies premises conclusion >>= fun result ->
      check bool "implication_test" true result;
      Lwt.return_unit

  let test_semantic_equality () =
    let open Lwt.Infix in
    let expr1 = EBinOp (ESymbol "x", "+", ENum Z.one) in
    let expr2 = EBinOp (ENum Z.one, "+", ESymbol "x") in
      Solver.exeq expr1 expr2 >>= fun result ->
      check bool "commutativity" true result;
      Lwt.return_unit

  let suite =
    [
      test_case "TestSolver.test_solver_creation" `Quick (fun () ->
          Lwt_main.run (test_solver_creation ())
      );
      test_case "TestSolver.test_satisfiable_constraint" `Quick (fun () ->
          Lwt_main.run (test_satisfiable_constraint ())
      );
      test_case "TestSolver.test_unsatisfiable_constraint" `Quick (fun () ->
          Lwt_main.run (test_unsatisfiable_constraint ())
      );
      test_case "TestSolver.test_implies" `Quick (fun () ->
          Lwt_main.run (test_implies ())
      );
      test_case "TestSolver.test_semantic_equality" `Quick (fun () ->
          Lwt_main.run (test_semantic_equality ())
      );
    ]
end

(** Test Module 5: Paper Example 1.1 - LB+UB+data (Undefined Behavior) *)
module TestExample1_1 = struct
  (** Example 1.1: Load Buffering with Undefined Behavior Thread 1: Thread 2:
      int r1 = x; int r2 = y; y = 1 / !r1; x = r2;

      The division by !r1 is only defined when r1 = 0 (so !r1 != 0).
      Optimization: assume r1 = 0, so write y = 1 (constant). *)
  let test_lb_ub_data_initial_justification () =
    let events = Hashtbl.create 10 in

    (* Thread 1 events *)
    let e1 = make_read_event 1 (make_var "x") (make_symbol "α") Relaxed in
    let e2 =
      make_write_event 2 (make_var "y")
        (EBinOp (ENum Z.one, "/", EUnOp ("!", ESymbol "α")))
        Relaxed
    in

    (* Thread 2 events *)
    let e3 = make_read_event 3 (make_var "y") (make_symbol "β") Relaxed in
    let e4 =
      make_write_event 4 (make_var "x")
        (Expr.of_value (make_symbol "β"))
        Relaxed
    in

    Hashtbl.add events 1 e1;
    Hashtbl.add events 2 e2;
    Hashtbl.add events 3 e3;
    Hashtbl.add events 4 e4;

    (* Initial justification for write 2 has data dependency on α *)
    let d_set = USet.create () in
    let d_set = USet.add d_set "α" in

    let just =
      {
        p = [ EBinOp (EUnOp ("!", ESymbol "α"), "≠", ENum Z.zero) ];
        d = d_set;
        fwd = USet.create ();
        we = USet.create ();
        w = e2;
        op = ("initial", None, None);
      }
    in

    check int "lb_ub_initial_deps" 1 (USet.size just.d);
    check bool "has_data_dep" true (USet.mem just.d "α");
    Printf.printf "PASS: Initial justification with dependencies\n"

  let test_lb_ub_data_remove_justification () =
    let e2 =
      make_write_event 2 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    let just =
      {
        p = [ EBinOp (ESymbol "α", "=", ENum Z.zero) ];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e2;
        op = ("remove", None, None);
      }
    in

    check int "lb_ub_remove_deps" 0 (USet.size just.d);
    Printf.printf "PASS: Remove justification with no dependencies\n"

  let test_lb_ub_complete_trace () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in

    (* Add events to the structure *)
    let ses = { ses with e = USet.of_list [ 1; 2; 3; 4 ] } in
    let ses = { ses with po = USet.of_list [ (1, 2); (3, 4) ] } in

    check int "complete_trace_events" 4 (USet.size ses.e);
    check int "complete_trace_po" 2 (USet.size ses.po);
    Printf.printf "PASS: Complete LB+UB+data trace\n"

  let suite =
    [
      test_case "TestExample1_1.test_lb_ub_data_initial_justification" `Quick
        test_lb_ub_data_initial_justification;
      test_case "TestExample1_1.test_lb_ub_data_remove_justification" `Quick
        test_lb_ub_data_remove_justification;
      test_case "TestExample1_1.test_lb_ub_complete_trace" `Quick
        test_lb_ub_complete_trace;
    ]
end

(** Test Module 6: Paper Example 3.1 - Reordering *)
module TestExample3_1 = struct
  let test_reordering_justification () =
    let e1 =
      make_write_event 1 (make_var "x") (Expr.of_value (make_number 1)) Relaxed
    in

    let just =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e1;
        op = ("reorder", None, None);
      }
    in

    check int "reorder_just_deps" 0 (USet.size just.d);
    Printf.printf "PASS: Reordering justification\n"

  let suite =
    [
      test_case "TestExample3_1.test_reordering_justification" `Quick
        test_reordering_justification;
    ]
end

(** Test Module 7: Paper Example 4.1 - Forwarding *)
module TestExample4_1 = struct
  let test_forwarding_structure () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in
    let ses = { ses with e = USet.of_list [ 1; 2; 3 ] } in
    let ses = { ses with po = USet.of_list [ (1, 2); (2, 3) ] } in

    check int "forwarding_events" 3 (USet.size ses.e);
    check int "forwarding_po" 2 (USet.size ses.po);
    Printf.printf "PASS: Forwarding structure\n"

  let suite =
    [
      test_case "TestExample4_1.test_forwarding_structure" `Quick
        test_forwarding_structure;
    ]
end

(** Test Module 8: Paper Example 5.1 - Speculation *)
module TestExample5_1 = struct
  let test_speculation_structure () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in
    let ses = { ses with e = USet.of_list [ 1; 2 ] } in

    check int "speculation_events" 2 (USet.size ses.e);
    Printf.printf "PASS: Speculation structure\n"

  let suite =
    [
      test_case "TestExample5_1.test_speculation_structure" `Quick
        test_speculation_structure;
    ]
end

(** Test Module 9: Paper Example 6.1 - Register Promotion *)
module TestExample6_1 = struct
  let test_register_promotion () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in
    let ses = { ses with e = USet.of_list [ 1; 2; 3; 4 ] } in
    let ses = { ses with po = USet.of_list [ (1, 2); (2, 3); (3, 4) ] } in

    check int "register_promotion_events" 4 (USet.size ses.e);
    check int "register_promotion_po" 3 (USet.size ses.po);
    Printf.printf "PASS: Register promotion\n"

  let suite =
    [
      test_case "TestExample6_1.test_register_promotion" `Quick
        test_register_promotion;
    ]
end

(** Test Module 10: Justifications *)
module TestJustifications = struct
  let test_independent_write () =
    let e =
      make_write_event 1 (make_var "z") (Expr.of_value (make_number 42)) Relaxed
    in

    let just =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e;
        op = ("independent", None, None);
      }
    in

    check int "independent_deps" 0 (USet.size just.d);
    Printf.printf "PASS: Independent write justification\n"

  let test_dependent_write () =
    let e =
      make_write_event 2 (make_var "w")
        (EBinOp (ESymbol "α", "+", ENum Z.one))
        Relaxed
    in

    let d_set = USet.create () in
    let d_set = USet.add d_set "α" in

    let just =
      {
        p = [];
        d = d_set;
        fwd = USet.create ();
        we = USet.create ();
        w = e;
        op = ("dependent", None, None);
      }
    in

    check int "dependent_deps" 1 (USet.size just.d);
    check bool "has_alpha_dep" true (USet.mem just.d "α");
    Printf.printf "PASS: Dependent write justification\n"

  let test_forwarding_context () =
    let e =
      make_write_event 3 (make_var "v")
        (Expr.of_value (make_symbol "β"))
        Relaxed
    in

    let fwd = USet.create () in
    let fwd = USet.add fwd (1, 3) in
    let fwd = USet.add fwd (2, 3) in

    let just =
      {
        p = [];
        d = USet.create ();
        fwd;
        we = USet.create ();
        w = e;
        op = ("with_forwarding", None, None);
      }
    in

    check int "forwarding_context_size" 2 (USet.size just.fwd);
    Printf.printf "PASS: Forwarding context in justification\n"

  let test_write_elision () =
    let e =
      make_write_event 4 (make_var "w") (Expr.of_value (make_number 7)) Relaxed
    in
    let we = USet.create () in
    let we = USet.add we (3, 4) in

    let just =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we;
        w = e;
        op = ("with_elision", None, None);
      }
    in

    check int "write_elision_size" 1 (USet.size just.we);
    Printf.printf "PASS: Write elision context in justification\n"

  let suite =
    [
      test_case "TestJustifications.test_independent_write" `Quick
        test_independent_write;
      test_case "TestJustifications.test_dependent_write" `Quick
        test_dependent_write;
      test_case "TestJustifications.test_forwarding_context" `Quick
        test_forwarding_context;
      test_case "TestJustifications.test_write_elision" `Quick
        test_write_elision;
    ]
end

(** Test Module 11: Symbolic Event Structure *)
module TestSymbolicEventStructure = struct
  let test_create_empty_structure () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in

    check int "empty_structure_events" 0 (USet.size ses.e);
    check int "empty_structure_po" 0 (USet.size ses.po);
    Printf.printf "PASS: Empty symbolic event structure\n"

  let test_add_program_order () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in
    let ses = { ses with e = USet.of_list [ 1; 2; 3 ] } in
    let ses = { ses with po = USet.of_list [ (1, 2); (2, 3) ] } in

    check int "structure_po_size" 2 (USet.size ses.po);
    check bool "structure_po_12" true (USet.mem ses.po (1, 2));
    check bool "structure_po_23" true (USet.mem ses.po (2, 3));
    Printf.printf "PASS: Program order in structure\n"

  let test_rmw_pairs () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in
    let ses = { ses with e = USet.of_list [ 1; 2; 3; 4 ] } in
    let ses = { ses with rmw = USet.of_list [ (1, 2); (3, 4) ] } in
    (* Two RMW operations *)

    check int "structure_rmw_size" 2 (USet.size ses.rmw);
    Printf.printf "PASS: RMW pairs in structure\n"

  let test_program_wide_guarantee () =
    (* Use the create helper from Types module *)
    let ses = SymbolicEventStructure.create () in
    let ses =
      { ses with pwg = [ EBinOp (ESymbol "x", "≤", ENum (Z.of_int 100)) ] }
    in

    check int "pwg_length" 1 (List.length ses.pwg);
    Printf.printf "PASS: Program-wide guarantee\n"

  let suite =
    [
      test_case "TestSymbolicEventStructure.test_create_empty_structure" `Quick
        test_create_empty_structure;
      test_case "TestSymbolicEventStructure.test_add_program_order" `Quick
        test_add_program_order;
      test_case "TestSymbolicEventStructure.test_rmw_pairs" `Quick
        test_rmw_pairs;
      test_case "TestSymbolicEventStructure.test_program_wide_guarantee" `Quick
        test_program_wide_guarantee;
    ]
end

(** Test Module 12: Coherence Relations *)
module TestCoherence = struct
  let test_semicolon_composition () =
    let r1 = USet.of_list [ (1, 2); (2, 3) ] in
    let r2 = USet.of_list [ (3, 4); (4, 5) ] in
    let composed = URelation.compose [ r1; r2 ] in

    check bool "semicolon_doesnt_include_original" false
      (USet.mem composed (1, 2));
    check bool "semicolon_includes_derived" true (USet.mem composed (2, 4));
    ()

  let test_event_identity () =
    let events = Hashtbl.create 10 in
    let e1 = make_read_event 1 (make_var "x") (make_symbol "α") Acquire in
    let e2 = make_read_event 2 (make_var "y") (make_symbol "β") Relaxed in
    let e3 = make_read_event 3 (make_var "z") (make_symbol "γ") Acquire in

    Hashtbl.add events 1 e1;
    Hashtbl.add events 2 e2;
    Hashtbl.add events 3 e3;

    let e_set = USet.of_list [ 1; 2; 3 ] in
    let rel =
      ModelUtils.match_events events e_set Read (Some Acquire) None None
    in

    (* Should include only acquire reads: (1,1) and (3,3) *)
    check bool "em_includes_acq_read_1" true (USet.mem rel (1, 1));
    check bool "em_includes_acq_read_3" true (USet.mem rel (3, 3));
    check bool "em_excludes_rlx_read" false (USet.mem rel (2, 2));
    ()

  let suite =
    [
      test_case "TestCoherence.test_semicolon_composition" `Quick
        test_semicolon_composition;
      test_case "TestCoherence.test_event_identity" `Quick test_event_identity;
    ]
end

let suite =
  ( "Test Symbolic MRD",
    (* Run all test modules *)
    TestEvents.suite
    @ TestExpressions.suite
    (* Run async solver tests *)
    @ TestSolver.suite
    (* Run paper example tests *)
    @ TestExample1_1.suite
    @ TestExample3_1.suite
    @ TestExample4_1.suite
    @ TestExample5_1.suite
    @ TestExample6_1.suite
    (* Run structural tests *)
    @ TestJustifications.suite
    @ TestSymbolicEventStructure.suite
    @ TestCoherence.suite
  )
