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

(** Data Providers for Test Cases *)
module DataProviders = struct
  (** Data for TestEvents *)
  let read_event_data = [ (1, make_var "x", make_symbol "α", Relaxed) ]

  let write_event_data =
    [ (2, make_var "y", Expr.of_value (make_number 1), Release) ]

  let alloc_event_data = [ (4, make_symbol "β", make_number 16) ]

  (** Data for TestExpressions *)
  let value_types_data =
    [
      (VNumber (Z.of_int 42), "number");
      (VSymbol "α", "symbol");
      (VVar "x", "var");
    ]

  let binary_expr_data = [ (ESymbol "α", "=", ENum (Z.of_int 1)) ]
  let unary_expr_data = [ ("!", ESymbol "α") ]

  (** Data for TestSolver *)
  let solver_creation_data = [ ([ EBinOp (ESymbol "x", ">", ENum Z.zero) ], 1) ]

  let sat_constraint_data =
    [ ([ EBinOp (ESymbol "x", "=", ENum (Z.of_int 5)) ], true) ]

  let unsat_constraint_data =
    [
      ( [
          EBinOp (ESymbol "x", "=", ENum Z.one);
          EBinOp (ESymbol "x", "=", ENum Z.zero);
        ],
        true
      );
    ]

  let implies_data =
    [
      ( [ EBinOp (ESymbol "x", "=", ENum Z.one) ],
        EBinOp (ESymbol "x", ">", ENum Z.zero),
        true
      );
    ]

  let semantic_equality_data =
    [
      ( EBinOp (ESymbol "x", "+", ENum Z.one),
        EBinOp (ENum Z.one, "+", ESymbol "x"),
        true
      );
    ]

  (** Data for TestExample1_1 *)
  let lb_ub_data_initial_justification_data =
    [
      ( 1,
        make_var "x",
        make_symbol "α",
        Relaxed,
        2,
        make_var "y",
        EBinOp (ENum Z.one, "/", EUnOp ("!", ESymbol "α")),
        Relaxed,
        3,
        make_var "y",
        make_symbol "β",
        Relaxed,
        4,
        make_var "x",
        Expr.of_value (make_symbol "β"),
        Relaxed
      );
    ]

  (** Data for TestJustifications *)
  let independent_write_data =
    [ (1, make_var "z", Expr.of_value (make_number 42), Relaxed) ]

  let dependent_write_data =
    [ (2, make_var "w", EBinOp (ESymbol "α", "+", ENum Z.one), Relaxed, "α") ]

  let forwarding_context_data =
    [
      ( 3,
        make_var "v",
        Expr.of_value (make_symbol "β"),
        Relaxed,
        [ (1, 3); (2, 3) ]
      );
    ]

  let write_elision_data =
    [ (4, make_var "w", Expr.of_value (make_number 7), Relaxed, [ (3, 4) ]) ]

  (** Data for TestSymbolicEventStructure *)
  let empty_structure_data = [ (USet.create (), USet.create ()) ]

  let program_order_data = [ ([ 1; 2; 3 ], [ (1, 2); (2, 3) ]) ]

  let rmw_pairs_data =
    [ ([ 1; 2; 3; 4 ], [ (1, EBoolean true, 2); (3, EBoolean true, 4) ]) ]

  (** Data for TestCoherence *)
  let semicolon_composition_data =
    [
      ( USet.of_list [ (1, 2); (2, 3) ],
        USet.of_list [ (3, 4); (4, 5) ],
        [ (2, 4) ]
      );
    ]

  let event_identity_data =
    [
      ( [
          (1, make_read_event 1 (make_var "x") (make_symbol "α") Acquire);
          (2, make_read_event 2 (make_var "y") (make_symbol "β") Relaxed);
          (3, make_read_event 3 (make_var "z") (make_symbol "γ") Acquire);
        ],
        [ 1; 2; 3 ],
        [ (1, 1); (3, 3) ]
      );
    ]
end

(** Test Module 1: Basic Event Creation *)
module TestEvents = struct
  let test_create_read (label, loc, symbol, mode) () =
    let ev = make_read_event label loc symbol mode in
      check int "read_event_label" label ev.label;
      check bool "read_event_type" true (ev.typ = Read);
      check bool "read_event_mode" true (ev.rmod = mode)

  let test_create_write (label, loc, value, mode) () =
    let ev = make_write_event label loc value mode in
      check int "write_event_label" label ev.label;
      check bool "write_event_type" true (ev.typ = Write);
      check bool "write_event_mode" true (ev.wmod = mode)

  let test_create_alloc (label, symbol, size) () =
    let ev = make_alloc_event label symbol size in
      check int "alloc_event_label" label ev.label;
      check bool "alloc_event_type" true (ev.typ = Malloc)

  let suite =
    List.map
      (fun (label, loc, symbol, mode) ->
        test_case
          (Printf.sprintf "TestEvents.test_create_read_%d" label)
          `Quick
          (test_create_read (label, loc, symbol, mode))
      )
      DataProviders.read_event_data
    @ List.map
        (fun (label, loc, value, mode) ->
          test_case
            (Printf.sprintf "TestEvents.test_create_write_%d" label)
            `Quick
            (test_create_write (label, loc, value, mode))
        )
        DataProviders.write_event_data
    @ List.map
        (fun (label, symbol, size) ->
          test_case
            (Printf.sprintf "TestEvents.test_create_alloc_%d" label)
            `Quick
            (test_create_alloc (label, symbol, size))
        )
        DataProviders.alloc_event_data
end

(** Test Module 3: Expressions and Values *)
module TestExpressions = struct
  let test_value_types (value, expected_type) () =
    match (value, expected_type) with
    | VNumber _, "number" -> check bool "value_number_created" true true
    | VSymbol _, "symbol" -> check bool "value_symbol_created" true true
    | VVar _, "var" -> check bool "value_var_created" true true
    | _ -> check bool "value_type_mismatch" false true

  let test_binary_expressions (lhs, op, rhs) () =
    let expr = EBinOp (lhs, op, rhs) in
      check bool "binop_created" true
        ( match expr with
        | EBinOp _ -> true
        | _ -> false
        )

  let test_unary_expressions (op, val_) () =
    let expr = EUnOp (op, val_) in
      check bool "unop_created" true
        ( match expr with
        | EUnOp _ -> true
        | _ -> false
        )

  let suite =
    List.map
      (fun (value, expected_type) ->
        test_case
          (Printf.sprintf "TestExpressions.test_value_types_%s" expected_type)
          `Quick
          (test_value_types (value, expected_type))
      )
      DataProviders.value_types_data
    @ List.map
        (fun (lhs, op, rhs) ->
          test_case "TestExpressions.test_binary_expressions" `Quick
            (test_binary_expressions (lhs, op, rhs))
        )
        DataProviders.binary_expr_data
    @ List.map
        (fun (op, val_) ->
          test_case "TestExpressions.test_unary_expressions" `Quick
            (test_unary_expressions (op, val_))
        )
        DataProviders.unary_expr_data
end

(** Test Module 4: Solver (async tests) *)
module TestSolver = struct
  let test_solver_creation (constraints, expected_size) () =
    let solver = Solver.create constraints in
      check bool "solver_created" true
        (List.length solver.expressions = expected_size);
      Lwt.return_unit

  let test_satisfiable_constraint (constraints, expected) () =
    let open Lwt.Infix in
    Solver.is_sat constraints >>= fun result ->
    check bool "simple_sat_constraint" expected result;
    Lwt.return_unit

  let test_unsatisfiable_constraint (constraints, expected) () =
    let open Lwt.Infix in
    Solver.is_unsat constraints >>= fun result ->
    check bool "simple_unsat_constraint" expected result;
    Lwt.return_unit

  let test_implies (premises, conclusion, expected) () =
    let open Lwt.Infix in
    Solver.implies premises conclusion >>= fun result ->
    check bool "implication_test" expected result;
    Lwt.return_unit

  let test_semantic_equality (expr1, expr2, expected) () =
    let open Lwt.Infix in
    Solver.exeq expr1 expr2 >>= fun result ->
    check bool "commutativity" expected result;
    Lwt.return_unit

  let suite =
    List.map
      (fun (constraints, expected_size) ->
        test_case "TestSolver.test_solver_creation" `Quick (fun () ->
            Lwt_main.run (test_solver_creation (constraints, expected_size) ())
        )
      )
      DataProviders.solver_creation_data
    @ List.map
        (fun (constraints, expected) ->
          test_case "TestSolver.test_satisfiable_constraint" `Quick (fun () ->
              Lwt_main.run
                (test_satisfiable_constraint (constraints, expected) ())
          )
        )
        DataProviders.sat_constraint_data
    @ List.map
        (fun (constraints, expected) ->
          test_case "TestSolver.test_unsatisfiable_constraint" `Quick (fun () ->
              Lwt_main.run
                (test_unsatisfiable_constraint (constraints, expected) ())
          )
        )
        DataProviders.unsat_constraint_data
    @ List.map
        (fun (premises, conclusion, expected) ->
          test_case "TestSolver.test_implies" `Quick (fun () ->
              Lwt_main.run (test_implies (premises, conclusion, expected) ())
          )
        )
        DataProviders.implies_data
    @ List.map
        (fun (expr1, expr2, expected) ->
          test_case "TestSolver.test_semantic_equality" `Quick (fun () ->
              Lwt_main.run (test_semantic_equality (expr1, expr2, expected) ())
          )
        )
        DataProviders.semantic_equality_data
end

(** Test Module 5: Paper Example 1.1 - LB+UB+data (Undefined Behavior) *)
module TestExample1_1 = struct
  let test_lb_ub_data_initial_justification
      ( e1_label,
        e1_loc,
        e1_symbol,
        e1_mode,
        e2_label,
        e2_loc,
        e2_value,
        e2_mode,
        e3_label,
        e3_loc,
        e3_symbol,
        e3_mode,
        e4_label,
        e4_loc,
        e4_value,
        e4_mode
      ) () =
    let events = Hashtbl.create 10 in

    (* Thread 1 events *)
    let e1 = make_read_event e1_label e1_loc e1_symbol e1_mode in
    let e2 = make_write_event e2_label e2_loc e2_value e2_mode in

    (* Thread 2 events *)
    let e3 = make_read_event e3_label e3_loc e3_symbol e3_mode in
    let e4 = make_write_event e4_label e4_loc e4_value e4_mode in

    Hashtbl.add events e1_label e1;
    Hashtbl.add events e2_label e2;
    Hashtbl.add events e3_label e3;
    Hashtbl.add events e4_label e4;

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
      }
    in

    check int "lb_ub_initial_deps" 1 (USet.size just.d);
    check bool "has_data_dep" true (USet.mem just.d "α");
    Printf.printf "PASS: Initial justification with dependencies\n"

  let suite =
    List.map
      (fun data ->
        test_case "TestExample1_1.test_lb_ub_data_initial_justification" `Quick
          (test_lb_ub_data_initial_justification data)
      )
      DataProviders.lb_ub_data_initial_justification_data
end

(** Test Module 10: Justifications *)
module TestJustifications = struct
  let test_independent_write (label, loc, value, mode) () =
    let e = make_write_event label loc value mode in
    let just =
      {
        p = [];
        d = USet.create ();
        fwd = USet.create ();
        we = USet.create ();
        w = e;
      }
    in
      check int "independent_deps" 0 (USet.size just.d);
      Printf.printf "PASS: Independent write justification\n"

  let test_dependent_write (label, loc, value, mode, dep) () =
    let e = make_write_event label loc value mode in
    let d_set = USet.create () in
    let d_set = USet.add d_set dep in
    let just =
      { p = []; d = d_set; fwd = USet.create (); we = USet.create (); w = e }
    in
      check int "dependent_deps" 1 (USet.size just.d);
      check bool "has_alpha_dep" true (USet.mem just.d dep);
      Printf.printf "PASS: Dependent write justification\n"

  let test_forwarding_context (label, loc, value, mode, fwd_pairs) () =
    let e = make_write_event label loc value mode in
    let fwd = USet.create () in
    let fwd =
      List.fold_left (fun acc (a, b) -> USet.add acc (a, b)) fwd fwd_pairs
    in
    let just =
      { p = []; d = USet.create (); fwd; we = USet.create (); w = e }
    in
      check int "forwarding_context_size" (List.length fwd_pairs)
        (USet.size just.fwd);
      Printf.printf "PASS: Forwarding context in justification\n"

  let test_write_elision (label, loc, value, mode, we_pairs) () =
    let e = make_write_event label loc value mode in
    let we = USet.create () in
    let we =
      List.fold_left (fun acc (a, b) -> USet.add acc (a, b)) we we_pairs
    in
    let just =
      { p = []; d = USet.create (); fwd = USet.create (); we; w = e }
    in
      check int "write_elision_size" (List.length we_pairs) (USet.size just.we);
      Printf.printf "PASS: Write elision context in justification\n"

  let suite =
    List.map
      (fun (label, loc, value, mode) ->
        test_case
          (Printf.sprintf "TestJustifications.test_independent_write_%d" label)
          `Quick
          (test_independent_write (label, loc, value, mode))
      )
      DataProviders.independent_write_data
    @ List.map
        (fun (label, loc, value, mode, dep) ->
          test_case
            (Printf.sprintf "TestJustifications.test_dependent_write_%d" label)
            `Quick
            (test_dependent_write (label, loc, value, mode, dep))
        )
        DataProviders.dependent_write_data
    @ List.map
        (fun (label, loc, value, mode, fwd_pairs) ->
          test_case
            (Printf.sprintf "TestJustifications.test_forwarding_context_%d"
               label
            )
            `Quick
            (test_forwarding_context (label, loc, value, mode, fwd_pairs))
        )
        DataProviders.forwarding_context_data
    @ List.map
        (fun (label, loc, value, mode, we_pairs) ->
          test_case
            (Printf.sprintf "TestJustifications.test_write_elision_%d" label)
            `Quick
            (test_write_elision (label, loc, value, mode, we_pairs))
        )
        DataProviders.write_elision_data
end

(** Test Module 11: Symbolic Event Structure *)
module TestSymbolicEventStructure = struct
  let test_create_empty_structure (events, po) () =
    let ses = { (SymbolicEventStructure.create ()) with e = events; po } in
      check int "empty_structure_events" 0 (USet.size ses.e);
      check int "empty_structure_po" 0 (USet.size ses.po);
      Printf.printf "PASS: Empty symbolic event structure\n"

  let test_add_program_order (events, po) () =
    let ses =
      {
        (SymbolicEventStructure.create ()) with
        e = USet.of_list events;
        po = USet.of_list po;
      }
    in
      check int "structure_po_size" (List.length po) (USet.size ses.po);
      List.iter
        (fun (a, b) ->
          check bool
            (Printf.sprintf "structure_po_%d_%d" a b)
            true
            (USet.mem ses.po (a, b))
        )
        po;
      Printf.printf "PASS: Program order in structure\n"

  let test_rmw_pairs (events, rmw) () =
    let ses =
      {
        (SymbolicEventStructure.create ()) with
        e = USet.of_list events;
        rmw = USet.of_list rmw;
      }
    in
      check int "structure_rmw_size" (List.length rmw) (USet.size ses.rmw);
      Printf.printf "PASS: RMW pairs in structure\n"

  let suite =
    List.map
      (fun (events, po) ->
        test_case "TestSymbolicEventStructure.test_create_empty_structure"
          `Quick
          (test_create_empty_structure (events, po))
      )
      DataProviders.empty_structure_data
    @ List.map
        (fun (events, po) ->
          test_case "TestSymbolicEventStructure.test_add_program_order" `Quick
            (test_add_program_order (events, po))
        )
        DataProviders.program_order_data
    @ List.map
        (fun (events, rmw) ->
          test_case "TestSymbolicEventStructure.test_rmw_pairs" `Quick
            (test_rmw_pairs (events, rmw))
        )
        DataProviders.rmw_pairs_data
end

(** Test Module 12: Coherence Relations *)
module TestCoherence = struct
  let test_semicolon_composition (r1, r2, expected) () =
    let composed = URelation.compose [ r1; r2 ] in
      List.iter
        (fun (a, b) ->
          check bool
            (Printf.sprintf "semicolon_includes_%d_%d" a b)
            true
            (USet.mem composed (a, b))
        )
        expected;
      ()

  let test_event_identity (events, e_set, expected) () =
    let events_tbl = Hashtbl.create 10 in
      List.iter (fun (id, ev) -> Hashtbl.add events_tbl id ev) events;
      let rel =
        ModelUtils.match_events events_tbl (USet.of_list e_set) Read
          (Some Acquire) None None
      in
        List.iter
          (fun (a, b) ->
            check bool
              (Printf.sprintf "em_includes_%d_%d" a b)
              true
              (USet.mem rel (a, b))
          )
          expected;
        ()

  let suite =
    List.map
      (fun (r1, r2, expected) ->
        test_case "TestCoherence.test_semicolon_composition" `Quick
          (test_semicolon_composition (r1, r2, expected))
      )
      DataProviders.semicolon_composition_data
    @ List.map
        (fun (events, e_set, expected) ->
          test_case "TestCoherence.test_event_identity" `Quick
            (test_event_identity (events, e_set, expected))
        )
        DataProviders.event_identity_data
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
    (* Run structural tests *)
    @ TestJustifications.suite
    @ TestSymbolicEventStructure.suite
    @ TestCoherence.suite
  )
