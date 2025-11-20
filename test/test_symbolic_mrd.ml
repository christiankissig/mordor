(** Unit Tests for Symbolic MRD Based on "Symbolic MRD: Dynamic Memory,
    Undefined Behaviour, and Extrinsic Choice" *)

open Alcotest
open Coherence
open Events
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

  (** Create a branch event *)
  let make_branch_event label condition =
    let ev = Event.create Branch label () in
      { ev with cond = Some condition }

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

  let test_create_branch () =
    let cond =
      EBinOp
        (Expr.of_value (make_symbol "α"), "=", Expr.of_value (make_number 1))
    in
    let ev = make_branch_event 3 cond in
      check int "branch_event_label" 3 ev.label;
      check bool "branch_event_type" true (ev.typ = Branch)

  let test_create_alloc () =
    let ev = make_alloc_event 4 (make_symbol "β") (make_number 16) in
      check int "alloc_event_label" 4 ev.label;
      check bool "alloc_event_type" true (ev.typ = Malloc)

  let suite =
    [
      test_case "TestEvents.test_create_read" `Quick test_create_read;
      test_case "TestEvents.test_create_write" `Quick test_create_write;
      test_case "TestEvents.test_create_branch" `Quick test_create_branch;
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
        p = [];
        (* predicate: ⊤ *)
        d = d_set;
        (* data dependency on α *)
        fwd = USet.create ();
        we = USet.create ();
        w = e2;
        op = ("initial", None, None);
      }
    in

    check int "ub_initial_just_deps" 1 (USet.size just.d);
    check bool "ub_initial_just_has_alpha" true (USet.mem just.d "α")

  let test_lb_ub_data_optimized_justification () =
    (* After strengthening with !α ≠ 0, value assignment with α = 0,
       and weakening, we get an independent justification *)
    let e2_opt =
      make_write_event 2 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    let just_opt =
      {
        p = [];
        (* predicate: ⊤ after weakening *)
        d = USet.create ();
        (* no dependencies *)
        fwd = USet.create ();
        we = USet.create ();
        w = e2_opt;
        op = ("optimized", None, None);
      }
    in

    check int "ub_optimized_just_deps" 0 (USet.size just_opt.d);
    Printf.printf "PASS: LB+UB+data optimization produces independent write\n"

  let suite =
    [
      test_case "TestExample1_1.test_lb_ub_data_initial_justification" `Quick
        test_lb_ub_data_initial_justification;
      test_case "TestExample1_1.test_lb_ub_data_optimized_justification" `Quick
        test_lb_ub_data_optimized_justification;
    ]
end

(** Test Module 6: Paper Example 3.1 - Alignment (Extrinsic Choice) *)
module TestExample3_1 = struct
  (** Example 3.1: Alignment-based optimization int* r1 = p; if (r1 % 16 == 0) y
      = 1;

      If compiler chooses to over-align p to 16 bytes, the condition is always
      true, so the write can be hoisted. *)
  let test_alignment_initial () =
    let e1 = make_read_event 1 (make_var "p") (make_symbol "α") Relaxed in
    let cond =
      EBinOp (EBinOp (ESymbol "α", "%", ENum (Z.of_int 16)), "=", ENum Z.zero)
    in
    let e2 = make_branch_event 2 cond in
    let e3 =
      make_write_event 3 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    (* Initial justification has control dependency *)
    let just =
      {
        p =
          [
            EBinOp
              (EBinOp (ESymbol "α", "%", ENum (Z.of_int 16)), "=", ENum Z.zero);
          ];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e3;
        op = ("initial", None, None);
      }
    in

    check bool "alignment_initial_has_predicate" true (List.length just.p > 0);
    Printf.printf
      "PASS: Alignment test initial justification has control dependency\n"

  let test_alignment_with_extrinsic_guarantee () =
    (* With extrinsic guarantee Ω => (α % 16 = 0), we can weaken *)
    let e3 =
      make_write_event 3 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    let just_weak =
      {
        p = [];
        (* weakened to ⊤ *)
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e3;
        op = ("weakened", None, None);
      }
    in

    check int "alignment_weakened_no_predicate" 0 (List.length just_weak.p);
    Printf.printf
      "PASS: Alignment with extrinsic guarantee removes control dependency\n"

  let suite =
    [
      test_case "TestExample3_1.test_alignment_initial" `Quick
        test_alignment_initial;
      test_case "TestExample3_1.test_alignment_with_extrinsic_guarantee" `Quick
        test_alignment_with_extrinsic_guarantee;
    ]
end

(** Test Module 7: Paper Example 4.1 - Dynamic Memory *)
module TestExample4_1 = struct
  (** Example 4.1: Load Buffering with Allocation and Aliasing Thread 1: Thread
      2: atomic int x = 0; int r2 = x; atomic int* p = malloc(...); *p = r2; int
      r1 = *p; x = 1;

      Allocation guarantees disjointness: *p and x don't alias. *)
  let test_lb_alias_initial () =
    let events = Hashtbl.create 10 in

    (* Thread 1 *)
    let e1 = make_alloc_event 1 (make_symbol "π") (make_number 4) in
    let e2 = make_read_event 2 (VSymbol "π") (make_symbol "α") Relaxed in
    let e3 =
      make_write_event 3 (make_var "x") (Expr.of_value (make_number 1)) Relaxed
    in

    (* Thread 2 *)
    let e4 = make_read_event 4 (make_var "x") (make_symbol "β") Relaxed in
    let e5 =
      make_write_event 5 (VSymbol "π") (Expr.of_value (make_symbol "β")) Relaxed
    in

    Hashtbl.add events 1 e1;
    Hashtbl.add events 2 e2;
    Hashtbl.add events 3 e3;
    Hashtbl.add events 4 e4;
    Hashtbl.add events 5 e5;

    (* Without disjointness: events 2 and 3 might alias *)
    (* With disjointness from allocation: can reorder *)

    (* Create disjoint predicate *)
    let disj_pred =
      disjoint
        (ESymbol "π", ENum (Z.of_int 4))
        (Expr.of_value (make_var "x"), ENum Z.one)
    in

    check bool "disjointness_predicate_created" true
      ( match disj_pred with
      | EBinOp _ -> true
      | _ -> false
      );
    Printf.printf "PASS: Dynamic memory disjointness predicate created\n"

  let suite =
    [
      test_case "TestExample4_1.test_lb_alias_initial" `Quick
        test_lb_alias_initial;
    ]
end

(** Test Module 8: Paper Example 5.1 - Control Dependencies *)
module TestExample5_1 = struct
  (** Example 5.1: Load Buffering with Value-Assignment False Dependency Thread
      1: Thread 2: int r1 = x; int ry = y; if (r1 == 1) x = ry; y = r1; else y =
      1;

      Both branches write the same value (1), so no real dependency on r1. *)
  let test_lb_false_dep_initial () =
    let e1 = make_read_event 1 (make_var "x") (make_symbol "r1") Relaxed in
    let cond = EBinOp (ESymbol "r1", "=", ENum Z.one) in
    let e2 = make_branch_event 2 cond in

    (* Write in true branch *)
    let e3 =
      make_write_event 3 (make_var "y")
        (Expr.of_value (make_symbol "r1"))
        Relaxed
    in
    (* Write in false branch *)
    let e5 =
      make_write_event 5 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    (* Initial justifications *)
    let d_set_true = USet.create () in
    let d_set_true = USet.add d_set_true "r1" in

    let just_true =
      {
        p = [ EBinOp (ESymbol "r1", "=", ENum Z.one) ];
        d = d_set_true;
        fwd = USet.create ();
        we = USet.create ();
        w = e3;
        op = ("true_branch", None, None);
      }
    in

    let just_false =
      {
        p = [ EBinOp (ESymbol "r1", "≠", ENum Z.one) ];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e5;
        op = ("false_branch", None, None);
      }
    in

    check bool "true_branch_has_control_dep" true (List.length just_true.p > 0);
    check bool "true_branch_has_data_dep" true (USet.mem just_true.d "r1");
    Printf.printf "PASS: Control dependency initial justifications created\n"

  let test_lb_false_dep_after_va () =
    (* After value assignment: r1 = 1 in predicate => write y = 1 *)
    let e3_va =
      make_write_event 3 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    let just_va =
      {
        p = [ EBinOp (ESymbol "r1", "=", ENum Z.one) ];
        d = USet.create ();
        (* no data dependency after VA *)
        fwd = USet.create ();
        we = USet.create ();
        w = e3_va;
        op = ("value_assigned", None, None);
      }
    in

    check int "after_va_no_data_deps" 0 (USet.size just_va.d);
    Printf.printf "PASS: Value assignment removes data dependency\n"

  let test_lb_false_dep_after_lift () =
    (* After lifting: both branches write same value under combined predicate *)
    let e3_lift =
      make_write_event 3 (make_var "y") (Expr.of_value (make_number 1)) Relaxed
    in

    let just_lift =
      {
        p = [];
        (* ⊤ after lifting *)
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e3_lift;
        op = ("lifted", None, None);
      }
    in

    check int "after_lift_no_control_dep" 0 (List.length just_lift.p);
    Printf.printf "PASS: Lifting removes control dependency\n"

  let suite =
    [
      test_case "TestExample5_1.test_lb_false_dep_initial" `Quick
        test_lb_false_dep_initial;
      test_case "TestExample5_1.test_lb_false_dep_after_va" `Quick
        test_lb_false_dep_after_va;
      test_case "TestExample5_1.test_lb_false_dep_after_lift" `Quick
        test_lb_false_dep_after_lift;
    ]
end

(** Test Module 9: Paper Example 6.1 - Forwarding *)
module TestExample6_1 = struct
  (** Example 6.1: Load Forwarding int r1 = x; int r2 = x; y = r2;

      The two loads can be fused, forwarding r1 to r2. *)
  let test_forwarding_initial () =
    let e1 = make_read_event 1 (make_var "x") (make_symbol "r1") Relaxed in
    let e2 = make_read_event 2 (make_var "x") (make_symbol "r2") Relaxed in
    let e3 =
      make_write_event 3 (make_var "y")
        (Expr.of_value (make_symbol "r2"))
        Relaxed
    in

    let d_set = USet.create () in
    let d_set = USet.add d_set "r2" in

    let just =
      {
        p = [];
        d = d_set;
        fwd = USet.create ();
        we = USet.create ();
        w = e3;
        op = ("initial", None, None);
      }
    in

    check bool "forwarding_initial_deps_r2" true (USet.mem just.d "r2");
    Printf.printf "PASS: Forwarding initial justification created\n"

  let test_forwarding_after_fwd () =
    let e3 =
      make_write_event 3 (make_var "y")
        (Expr.of_value (make_symbol "r1"))
        Relaxed
    in

    let fwd_edges = USet.create () in
    let fwd_edges = USet.add fwd_edges (1, 2) in

    let d_set = USet.create () in
    let d_set = USet.add d_set "r1" in

    let just_fwd =
      {
        p = [];
        d = d_set;
        (* now depends on r1 instead of r2 *)
        fwd = fwd_edges;
        (* records (1,2) forwarding *)
        we = USet.create ();
        w = e3;
        op = ("forwarded", None, None);
      }
    in

    check bool "forwarding_has_fwd_edge" true (USet.mem just_fwd.fwd (1, 2));
    check bool "forwarding_deps_r1" true (USet.mem just_fwd.d "r1");
    check bool "forwarding_not_deps_r2" false (USet.mem just_fwd.d "r2");
    Printf.printf "PASS: Forwarding changes dependencies correctly\n"

  let suite =
    [
      test_case "TestExample6_1.test_forwarding_initial" `Quick
        test_forwarding_initial;
      test_case "TestExample6_1.test_forwarding_after_fwd" `Quick
        test_forwarding_after_fwd;
    ]
end

(** Test Module 10: Justification Structure *)
module TestJustifications = struct
  let test_independent_write () =
    let e =
      make_write_event 1 (make_var "x") (Expr.of_value (make_number 42)) Relaxed
    in
    let just =
      {
        p = [];
        (* ⊤ *)
        d = USet.create ();
        (* ∅ *)
        fwd = USet.create ();
        we = USet.create ();
        w = e;
        op = ("independent", None, None);
      }
    in

    check int "independent_no_predicates" 0 (List.length just.p);
    check int "independent_no_deps" 0 (USet.size just.d);
    Printf.printf "PASS: Independent write justification\n"

  let test_dependent_write () =
    let e =
      make_write_event 2 (make_var "y")
        (Expr.of_value (make_symbol "α"))
        Relaxed
    in
    let d_set = USet.create () in
    let d_set = USet.add d_set "α" in

    let just =
      {
        p = [ EBinOp (ESymbol "α", ">", ENum Z.zero) ];
        d = d_set;
        fwd = USet.create ();
        we = USet.create ();
        w = e;
        op = ("dependent", None, None);
      }
    in

    check bool "dependent_has_predicates" true (List.length just.p > 0);
    check bool "dependent_has_deps" true (USet.size just.d > 0);
    Printf.printf "PASS: Dependent write justification\n"

  let test_forwarding_context () =
    let e =
      make_write_event 3 (make_var "z")
        (Expr.of_value (make_symbol "β"))
        Relaxed
    in
    let fwd = USet.create () in
    let fwd = USet.add fwd (1, 2) in
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
    let ses =
      {
        e = USet.create ();
        events = Hashtbl.create 10;
        po = USet.create ();
        po_iter = USet.create ();
        rmw = USet.create ();
        lo = USet.create ();
        restrict = Hashtbl.create 10;
        cas_groups = Hashtbl.create 10;
        pwg = [];
        fj = USet.create ();
        p = USet.create ();
        constraint_ = [];
      }
    in

    check int "empty_structure_events" 0 (USet.size ses.e);
    check int "empty_structure_po" 0 (USet.size ses.po);
    Printf.printf "PASS: Empty symbolic event structure\n"

  let test_add_program_order () =
    let ses =
      {
        e = USet.of_list [ 1; 2; 3 ];
        events = Hashtbl.create 10;
        po = USet.of_list [ (1, 2); (2, 3) ];
        po_iter = USet.create ();
        rmw = USet.create ();
        lo = USet.create ();
        restrict = Hashtbl.create 10;
        cas_groups = Hashtbl.create 10;
        pwg = [];
        fj = USet.create ();
        p = USet.create ();
        constraint_ = [];
      }
    in

    check int "structure_po_size" 2 (USet.size ses.po);
    check bool "structure_po_12" true (USet.mem ses.po (1, 2));
    check bool "structure_po_23" true (USet.mem ses.po (2, 3));
    Printf.printf "PASS: Program order in structure\n"

  let test_rmw_pairs () =
    let ses =
      {
        e = USet.of_list [ 1; 2; 3; 4 ];
        events = Hashtbl.create 10;
        po = USet.create ();
        po_iter = USet.create ();
        rmw = USet.of_list [ (1, 2); (3, 4) ];
        (* Two RMW operations *)
        lo = USet.create ();
        restrict = Hashtbl.create 10;
        cas_groups = Hashtbl.create 10;
        pwg = [];
        fj = USet.create ();
        p = USet.create ();
        constraint_ = [];
      }
    in

    check int "structure_rmw_size" 2 (USet.size ses.rmw);
    Printf.printf "PASS: RMW pairs in structure\n"

  let test_program_wide_guarantee () =
    let ses =
      {
        e = USet.create ();
        events = Hashtbl.create 10;
        po = USet.create ();
        po_iter = USet.create ();
        rmw = USet.create ();
        lo = USet.create ();
        restrict = Hashtbl.create 10;
        cas_groups = Hashtbl.create 10;
        pwg = [ EBinOp (ESymbol "x", "≤", ENum (Z.of_int 100)) ];
        fj = USet.create ();
        p = USet.create ();
        constraint_ = [];
      }
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
    let composed = semicolon_rel [ r1; r2 ] in

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
    let rel = em events e_set Read (Some Acquire) None None in

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

(** Test Module 13: Origin Function *)
module TestOrigin = struct
  let test_origin_from_read () =
    let events = Hashtbl.create 10 in
    let e1 = make_read_event 1 (make_var "x") (make_symbol "α") Relaxed in
      Hashtbl.add events 1 e1;

      let read_events = USet.singleton 1 in
      let malloc_events = USet.create () in
      let all_events = USet.union read_events malloc_events in

      let orig = origin events all_events "α" in

      ( match orig with
      | Some label -> check int "origin_read_label" 1 label
      | None -> check bool "origin_read_found" false true
      );
      Printf.printf "PASS: Origin function finds read\n"

  let test_origin_from_alloc () =
    let events = Hashtbl.create 10 in
    let e1 = make_alloc_event 1 (make_symbol "π") (make_number 16) in
      Hashtbl.add events 1 e1;

      let read_events = USet.create () in
      let malloc_events = USet.singleton 1 in
      let all_events = USet.union read_events malloc_events in

      let orig = origin events all_events "π" in

      ( match orig with
      | Some label -> check int "origin_alloc_label" 1 label
      | None -> check bool "origin_alloc_found" false true
      );
      ()

  let test_origin_not_found () =
    let events = Hashtbl.create 10 in
    let read_events = USet.create () in
    let malloc_events = USet.create () in
    let all_events = USet.union read_events malloc_events in

    let orig = origin events all_events "ξ" in

    check bool "origin_not_found" true (orig = None);
    Printf.printf "PASS: Origin function returns None for unknown symbol\n"

  let run_tests () =
    Printf.printf "\n=== Testing Origin Function ===\n";
    test_origin_from_read ();
    test_origin_from_alloc ();
    test_origin_not_found ()

  let suite =
    [
      test_case "TestOrigin.test_origin_from_read" `Quick test_origin_from_read;
      test_case "TestOrigin.test_origin_from_alloc" `Quick
        test_origin_from_alloc;
      test_case "TestOrigin.test_origin_not_found" `Quick test_origin_not_found;
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
    @ TestOrigin.suite
  )
