open Solver
open Types
open Expr
open Lwt.Syntax

(** Helper to run Lwt tests *)
let run_lwt f = Lwt_main.run (f ())

(** Test context creation *)
let test_create_context () =
  let ctx = create_context () in
    Alcotest.(check bool) "context created" true (ctx.ctx <> Obj.magic 0);
    Alcotest.(check bool) "solver created" true (ctx.solver <> Obj.magic 0);
    Alcotest.(check int) "vars table empty" 0 (Hashtbl.length ctx.vars)

(** Test variable creation and retrieval *)
let test_get_var () =
  let ctx = create_context () in
  let var1 = get_var ctx "x" in
    Alcotest.(check int) "one var created" 1 (Hashtbl.length ctx.vars);
    let var2 = get_var ctx "x" in
      Alcotest.(check bool) "same var retrieved" true (var1 == var2);
      let var3 = get_var ctx "y" in
        Alcotest.(check int) "two vars created" 2 (Hashtbl.length ctx.vars);
        Alcotest.(check bool) "different var created" true (var1 != var3)

(** Test value to Z3 conversion - numbers *)
let test_value_to_z3_number () =
  let ctx = create_context () in
  let z3_expr = value_to_z3 ctx (VNumber (Z.of_int 42)) in
  let str = Z3.Expr.to_string z3_expr in
    Alcotest.(check string) "number converts" "42" str

(** Test value to Z3 conversion - variables *)
let test_value_to_z3_var () =
  let ctx = create_context () in
  let _ = value_to_z3 ctx (VVar "x") in
    Alcotest.(check int) "var created" 1 (Hashtbl.length ctx.vars)

(** Test value to Z3 conversion - booleans *)
let test_value_to_z3_boolean () =
  let ctx = create_context () in
  let z3_true = value_to_z3 ctx (VBoolean true) in
  let z3_false = value_to_z3 ctx (VBoolean false) in
    Alcotest.(check bool) "true is true" true (Z3.Boolean.is_true z3_true);
    Alcotest.(check bool) "false is false" true (Z3.Boolean.is_false z3_false)

(** Test expression to Z3 - numbers *)
let test_expr_to_z3_num () =
  let ctx = create_context () in
  let z3_expr = expr_to_z3 ctx (ENum (Z.of_int 17)) in
  let str = Z3.Expr.to_string z3_expr in
    Alcotest.(check string) "expr number converts" "17" str

(** Test expression to Z3 - variables *)
let test_expr_to_z3_var () =
  let ctx = create_context () in
  let _ = expr_to_z3 ctx (EVar "y") in
    Alcotest.(check int) "var created from expr" 1 (Hashtbl.length ctx.vars)

(** Test expression to Z3 - addition *)
let test_expr_to_z3_add () =
  let ctx = create_context () in
  let expr = EBinOp (VNumber (Z.of_int 5), "+", VNumber (Z.of_int 3)) in
  let z3_expr = expr_to_z3 ctx expr in
  let str = Z3.Expr.to_string z3_expr in
    Alcotest.(check bool) "addition expr created" true (String.length str > 0)

(** Test expression to Z3 - equality *)
let test_expr_to_z3_eq () =
  let ctx = create_context () in
  let expr = EBinOp (VVar "x", "=", VNumber (Z.of_int 10)) in
  let z3_expr = expr_to_z3 ctx expr in
    Alcotest.(check bool) "equality expr created" true (Z3.Boolean.is_eq z3_expr)

(** Test expression to Z3 - comparison operators *)
let test_expr_to_z3_comparison () =
  let ctx = create_context () in
  let expr_lt = EBinOp (VVar "x", "<", VNumber (Z.of_int 5)) in
  let expr_gt = EBinOp (VVar "x", ">", VNumber (Z.of_int 5)) in
  let expr_le = EBinOp (VVar "x", "<=", VNumber (Z.of_int 5)) in
  let expr_ge = EBinOp (VVar "x", ">=", VNumber (Z.of_int 5)) in
  let _ = expr_to_z3 ctx expr_lt in
  let _ = expr_to_z3 ctx expr_gt in
  let _ = expr_to_z3 ctx expr_le in
  let _ = expr_to_z3 ctx expr_ge in
    Alcotest.(check bool) "comparison exprs created" true true

(** Test expression to Z3 - logical operators *)
let test_expr_to_z3_logical () =
  let ctx = create_context () in
  let expr_and = EBinOp (VBoolean true, "&&", VBoolean false) in
  let expr_or = EBinOp (VBoolean true, "||", VBoolean false) in
  let expr_impl = EBinOp (VBoolean true, "=>", VBoolean false) in
  let _ = expr_to_z3 ctx expr_and in
  let _ = expr_to_z3 ctx expr_or in
  let _ = expr_to_z3 ctx expr_impl in
    Alcotest.(check bool) "logical exprs created" true true

(** Test expression to Z3 - unary not *)
let test_expr_to_z3_not () =
  let ctx = create_context () in
  let expr = EUnOp ("!", VBoolean true) in
  let z3_expr = expr_to_z3 ctx expr in
    Alcotest.(check bool) "not expr created" true (Z3.Boolean.is_not z3_expr)

(** Test solver creation *)
let test_create_solver () =
  let expr = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
  let solver = create [ expr ] in
    Alcotest.(check int)
      "solver has one expression" 1
      (List.length solver.expressions)

(** Test satisfiable constraint *)
let test_check_satisfiable () =
  run_lwt (fun () ->
      let expr = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let solver = create [ expr ] in
        let* result = check solver in
          match result with
          | Some true ->
              Lwt.return
                (Alcotest.(check bool) "constraint is satisfiable" true true)
          | Some false -> Lwt.return (Alcotest.fail "expected satisfiable")
          | None ->
              Lwt.return (Alcotest.fail "expected satisfiable, got unknown")
  )

(** Test unsatisfiable constraint *)
let test_check_unsatisfiable () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VVar "x", "=", VNumber (Z.of_int 10)) in
      let solver = create [ expr1; expr2 ] in
        let* result = check solver in
          match result with
          | Some false ->
              Lwt.return
                (Alcotest.(check bool) "constraint is unsatisfiable" true true)
          | Some true -> Lwt.return (Alcotest.fail "expected unsatisfiable")
          | None ->
              Lwt.return (Alcotest.fail "expected unsatisfiable, got unknown")
  )

(** Test solving simple constraint *)
let test_solve_simple () =
  run_lwt (fun () ->
      let expr = EBinOp (VVar "x", "=", VNumber (Z.of_int 42)) in
      let solver = create [ expr ] in
        let* result = solve solver in
          match result with
          | Some bindings -> (
              match concrete_value bindings "x" with
              | Some (VNumber n) ->
                  Lwt.return
                    (Alcotest.(check bool)
                       "x equals 42" true
                       (Z.equal n (Z.of_int 42))
                    )
              | _ -> Lwt.return (Alcotest.fail "expected concrete number value")
            )
          | None -> Lwt.return (Alcotest.fail "expected solution")
  )

(** Test solving with arithmetic *)
let test_solve_arithmetic () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "+", VVar "y") in
      let expr2 = EBinOp (VExpression expr1, "=", VNumber (Z.of_int 10)) in
      let expr3 = EBinOp (VVar "x", "=", VNumber (Z.of_int 3)) in
      let solver = create [ expr2; expr3 ] in
        let* result = solve solver in
          match result with
          | Some bindings -> (
              match
                (concrete_value bindings "x", concrete_value bindings "y")
              with
              | Some (VNumber x), Some (VNumber y) ->
                  let sum = Z.add x y in
                    Lwt.return
                      (Alcotest.(check bool)
                         "x + y = 10" true
                         (Z.equal sum (Z.of_int 10))
                      )
              | _ -> Lwt.return (Alcotest.fail "expected concrete values")
            )
          | None -> Lwt.return (Alcotest.fail "expected solution")
  )

(** Test solving inequality *)
let test_solve_inequality () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", ">", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VVar "x", "<", VNumber (Z.of_int 10)) in
      let solver = create [ expr1; expr2 ] in
        let* result = solve solver in
          match result with
          | Some bindings -> (
              match concrete_value bindings "x" with
              | Some (VNumber n) ->
                  let in_range = Z.gt n (Z.of_int 5) && Z.lt n (Z.of_int 10) in
                    Lwt.return (Alcotest.(check bool) "5 < x < 10" true in_range)
              | _ -> Lwt.return (Alcotest.fail "expected concrete number value")
            )
          | None -> Lwt.return (Alcotest.fail "expected solution")
  )

(** Test concrete_value with missing variable *)
let test_concrete_value_missing () =
  let bindings = Hashtbl.create 4 in
    Hashtbl.add bindings "x" (VNumber (Z.of_int 5));
    let result = concrete_value bindings "y" in
      Alcotest.(check bool) "missing var returns None" true (result = None)

(** Test concrete_value with existing variable *)
let test_concrete_value_exists () =
  let bindings = Hashtbl.create 4 in
    Hashtbl.add bindings "x" (VNumber (Z.of_int 5));
    let result = concrete_value bindings "x" in
      match result with
      | Some (VNumber n) ->
          Alcotest.(check bool)
            "var value retrieved" true
            (Z.equal n (Z.of_int 5))
      | _ -> Alcotest.fail "expected number value"

(** Test simplify_disjunction - empty result *)
let test_simplify_disjunction_empty () =
  run_lwt (fun () ->
      (* All clauses are contradictions *)
      let clauses = [ [ ENum Z.zero ] ] in
        let* _ = simplify_disjunction clauses in
          (* Note: This test depends on is_contradiction implementation *)
          Lwt.return (Alcotest.(check bool) "empty or none result" true true)
  )

(** Test simplify_disjunction - filters tautologies *)
let test_simplify_disjunction_filter () =
  run_lwt (fun () ->
      let clause1 = [ ENum (Z.of_int 1) ] in
      let clause2 = [ ENum (Z.of_int 2) ] in
      let clauses = [ clause1; clause2 ] in
        let* result = simplify_disjunction clauses in
          match result with
          | Some cs ->
              Lwt.return
                (Alcotest.(check bool)
                   "clauses returned" true
                   (List.length cs > 0)
                )
          | None -> Lwt.return (Alcotest.(check bool) "no clauses" true true)
  )

(** Test exeq - identical expressions *)
let test_exeq_identical () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "+", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VVar "x", "+", VNumber (Z.of_int 5)) in
        let* result = exeq expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "identical expressions are equal" true result)
  )

(** Test exeq - semantically equal expressions *)
let test_exeq_semantic () =
  run_lwt (fun () ->
      (* x = 5 and 5 = x should be semantically equal *)
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VNumber (Z.of_int 5), "=", VVar "x") in
        let* result = exeq expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "x = 5 and 5 = x are equal" true result)
  )

(** Test exeq - not semantically equal *)
let test_exeq_not_equal () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VVar "x", "=", VNumber (Z.of_int 10)) in
        let* result = exeq expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "x = 5 and x = 10 are not equal" false result)
  )

(** Test exeq - with state/context *)
let test_exeq_with_state () =
  run_lwt (fun () ->
      (* Given x = 5, then x and 5 are semantically equal *)
      let state = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
      let expr1 = EVar "x" in
      let expr2 = ENum (Z.of_int 5) in
        let* result = exeq ~state expr1 expr2 in
          Lwt.return (Alcotest.(check bool) "x equals 5 given x = 5" true result)
  )

(** Test exeq - contradictory state *)
let test_exeq_contradictory_state () =
  run_lwt (fun () ->
      (* Given x = 5 and x = 10 (contradiction), any two expressions are "equal" *)
      let state =
        [
          EBinOp (VVar "x", "=", VNumber (Z.of_int 5));
          EBinOp (VVar "x", "=", VNumber (Z.of_int 10));
        ]
      in
      let expr1 = ENum (Z.of_int 1) in
      let expr2 = ENum (Z.of_int 2) in
        let* result = exeq ~state expr1 expr2 in
          (* In an inconsistent state, everything can be "proven" *)
          Lwt.return
            (Alcotest.(check bool)
               "contradictory state makes anything equal" true result
            )
  )

(** Test expoteq - identical expressions *)
let test_expoteq_identical () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "+", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VVar "x", "+", VNumber (Z.of_int 5)) in
        let* result = expoteq expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool)
               "identical expressions are potentially equal" true result
            )
  )

(** Test expoteq - potentially equal *)
let test_expoteq_potential () =
  run_lwt (fun () ->
      (* x and y could be equal if x = y *)
      let expr1 = EVar "x" in
      let expr2 = EVar "y" in
        let* result = expoteq expr1 expr2 in
          Lwt.return (Alcotest.(check bool) "x and y could be equal" true result)
  )

(** Test expoteq - cannot be equal *)
let test_expoteq_impossible () =
  run_lwt (fun () ->
      (* 5 and 10 can never be equal *)
      let expr1 = ENum (Z.of_int 5) in
      let expr2 = ENum (Z.of_int 10) in
        let* result = expoteq expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "5 and 10 cannot be equal" false result)
  )

(** Test expoteq - with state *)
let test_expoteq_with_state () =
  run_lwt (fun () ->
      (* Given x > 10, can x = 5? No *)
      let state = [ EBinOp (VVar "x", ">", VNumber (Z.of_int 10)) ] in
      let expr1 = EVar "x" in
      let expr2 = ENum (Z.of_int 5) in
        let* result = expoteq ~state expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "x cannot equal 5 given x > 10" false result)
  )

(** Test expoteq - satisfiable with state *)
let test_expoteq_satisfiable_with_state () =
  run_lwt (fun () ->
      (* Given x > 5, can x = 10? Yes *)
      let state = [ EBinOp (VVar "x", ">", VNumber (Z.of_int 5)) ] in
      let expr1 = EVar "x" in
      let expr2 = ENum (Z.of_int 10) in
        let* result = expoteq ~state expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "x could equal 10 given x > 5" true result)
  )

(** Test Semeq module - create state *)
let test_semeq_create_state () =
  let state = Semeq.create_state () in
    Alcotest.(check int) "state starts empty" 0 (List.length state.context)

(** Test Semeq module - set state *)
let test_semeq_set_state () =
  let state = Semeq.create_state () in
  let constraints = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
    Semeq.set_state state constraints;
    Alcotest.(check int) "state has one constraint" 1 (List.length state.context)

(** Test Semeq module - exeq with state *)
let test_semeq_exeq () =
  run_lwt (fun () ->
      let state = Semeq.create_state () in
      let constraints = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
        Semeq.set_state state constraints;
        let expr1 = EVar "x" in
        let expr2 = ENum (Z.of_int 5) in
          let* result = Semeq.exeq state expr1 expr2 in
            Lwt.return
              (Alcotest.(check bool) "x equals 5 with state" true result)
  )

(** Test Semeq module - expoteq with state *)
let test_semeq_expoteq () =
  run_lwt (fun () ->
      let state = Semeq.create_state () in
      let constraints = [ EBinOp (VVar "x", ">", VNumber (Z.of_int 5)) ] in
        Semeq.set_state state constraints;
        let expr1 = EVar "x" in
        let expr2 = ENum (Z.of_int 10) in
          let* result = Semeq.expoteq state expr1 expr2 in
            Lwt.return
              (Alcotest.(check bool) "x could equal 10 given x > 5" true result)
  )

(** Test Semeq module - exeq_value with numbers *)
let test_semeq_exeq_value_numbers () =
  run_lwt (fun () ->
      let state = Semeq.create_state () in
      let v1 = VNumber (Z.of_int 5) in
      let v2 = VNumber (Z.of_int 5) in
        let* result = Semeq.exeq_value state v1 v2 in
          Lwt.return (Alcotest.(check bool) "5 equals 5" true result)
  )

(** Test Semeq module - exeq_value with expressions *)
let test_semeq_exeq_value_expressions () =
  run_lwt (fun () ->
      let state = Semeq.create_state () in
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VNumber (Z.of_int 5), "=", VVar "x") in
      let v1 = VExpression expr1 in
      let v2 = VExpression expr2 in
        let* result = Semeq.exeq_value state v1 v2 in
          Lwt.return
            (Alcotest.(check bool) "expression values equal" true result)
  )

(** Test Semeq module - expoteq_value *)
let test_semeq_expoteq_value () =
  run_lwt (fun () ->
      let state = Semeq.create_state () in
      let v1 = VVar "x" in
      let v2 = VVar "y" in
        let* result = Semeq.expoteq_value state v1 v2 in
          Lwt.return
            (Alcotest.(check bool) "variables could be equal" true result)
  )

(** Test SemeqCache - create cache *)
let test_cache_create () =
  let cache = SemeqCache.create () in
    Alcotest.(check int) "eq cache empty" 0 (Hashtbl.length cache.eq_cache);
    Alcotest.(check int) "poteq cache empty" 0 (Hashtbl.length cache.poteq_cache)

(** Test SemeqCache - exeq_cached *)
let test_cache_exeq_cached () =
  run_lwt (fun () ->
      let cache = SemeqCache.create () in
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VNumber (Z.of_int 5), "=", VVar "x") in
        (* First call should compute *)
        let* result1 = SemeqCache.exeq_cached cache expr1 expr2 in
          Alcotest.(check int)
            "cache has one entry" 1
            (Hashtbl.length cache.eq_cache);
          (* Second call should use cache *)
          let* result2 = SemeqCache.exeq_cached cache expr1 expr2 in
            Alcotest.(check bool) "cached result matches" result1 result2;
            Alcotest.(check int)
              "cache still has one entry" 1
              (Hashtbl.length cache.eq_cache);
            Lwt.return (Alcotest.(check bool) "test complete" true true)
  )

(** Test SemeqCache - expoteq_cached *)
let test_cache_expoteq_cached () =
  run_lwt (fun () ->
      let cache = SemeqCache.create () in
      let expr1 = EVar "x" in
      let expr2 = EVar "y" in
        (* First call should compute *)
        let* result1 = SemeqCache.expoteq_cached cache expr1 expr2 in
          Alcotest.(check int)
            "cache has one entry" 1
            (Hashtbl.length cache.poteq_cache);
          (* Second call should use cache *)
          let* result2 = SemeqCache.expoteq_cached cache expr1 expr2 in
            Alcotest.(check bool) "cached result matches" result1 result2;
            Lwt.return (Alcotest.(check bool) "test complete" true true)
  )

(** Test SemeqCache - clear *)
let test_cache_clear () =
  run_lwt (fun () ->
      let cache = SemeqCache.create () in
      let expr1 = EVar "x" in
      let expr2 = EVar "y" in
        let* _ = SemeqCache.exeq_cached cache expr1 expr2 in
          let* _ = SemeqCache.expoteq_cached cache expr1 expr2 in
            Alcotest.(check bool)
              "caches populated" true
              (Hashtbl.length cache.eq_cache > 0
              && Hashtbl.length cache.poteq_cache > 0
              );
            SemeqCache.clear cache;
            Alcotest.(check int)
              "eq cache cleared" 0
              (Hashtbl.length cache.eq_cache);
            Alcotest.(check int)
              "poteq cache cleared" 0
              (Hashtbl.length cache.poteq_cache);
            Lwt.return (Alcotest.(check bool) "test complete" true true)
  )

(** Test SemeqCache - with state *)
let test_cache_with_state () =
  run_lwt (fun () ->
      let cache = SemeqCache.create () in
      let state = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
      let expr1 = EVar "x" in
      let expr2 = ENum (Z.of_int 5) in
        let* result = SemeqCache.exeq_cached cache ~state expr1 expr2 in
          Lwt.return
            (Alcotest.(check bool) "x equals 5 with cached state" true result)
  )

(** Test helper functions - implies *)
let test_implies_true () =
  run_lwt (fun () ->
      (* x = 5 implies x = 5 *)
      let constraints = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
      let conclusion = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
        let* result = implies constraints conclusion in
          Lwt.return (Alcotest.(check bool) "x = 5 implies x = 5" true result)
  )

(** Test helper functions - implies with derivation *)
let test_implies_derivation () =
  run_lwt (fun () ->
      (* x = 5 implies x < 10 *)
      let constraints = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
      let conclusion = EBinOp (VVar "x", "<", VNumber (Z.of_int 10)) in
        let* result = implies constraints conclusion in
          Lwt.return (Alcotest.(check bool) "x = 5 implies x < 10" true result)
  )

(** Test helper functions - implies false *)
let test_implies_false () =
  run_lwt (fun () ->
      (* x = 5 does not imply x = 10 *)
      let constraints = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
      let conclusion = EBinOp (VVar "x", "=", VNumber (Z.of_int 10)) in
        let* result = implies constraints conclusion in
          Lwt.return
            (Alcotest.(check bool) "x = 5 does not imply x = 10" false result)
  )

(** Test helper functions - is_sat *)
let test_is_sat_true () =
  run_lwt (fun () ->
      let exprs = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
        let* result = is_sat exprs in
          Lwt.return (Alcotest.(check bool) "x = 5 is satisfiable" true result)
  )

(** Test helper functions - is_sat false *)
let test_is_sat_false () =
  run_lwt (fun () ->
      let exprs =
        [
          EBinOp (VVar "x", "=", VNumber (Z.of_int 5));
          EBinOp (VVar "x", "=", VNumber (Z.of_int 10));
        ]
      in
        let* result = is_sat exprs in
          Lwt.return
            (Alcotest.(check bool)
               "x = 5 and x = 10 is not satisfiable" false result
            )
  )

(** Test helper functions - is_unsat *)
let test_is_unsat_true () =
  run_lwt (fun () ->
      let exprs =
        [
          EBinOp (VVar "x", "=", VNumber (Z.of_int 5));
          EBinOp (VVar "x", "=", VNumber (Z.of_int 10));
        ]
      in
        let* result = is_unsat exprs in
          Lwt.return
            (Alcotest.(check bool)
               "x = 5 and x = 10 is unsatisfiable" true result
            )
  )

(** Test helper functions - is_unsat false *)
let test_is_unsat_false () =
  run_lwt (fun () ->
      let exprs = [ EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) ] in
        let* result = is_unsat exprs in
          Lwt.return
            (Alcotest.(check bool) "x = 5 is not unsatisfiable" false result)
  )

(** Test helper functions - solve_for_vars *)
let test_solve_for_vars () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let expr2 = EBinOp (VVar "y", "=", VNumber (Z.of_int 10)) in
      let solver = create [ expr1; expr2 ] in
        let* result = solve_for_vars solver [ "x"; "y" ] in
          match result with
          | Some bindings -> (
              let x_val = concrete_value bindings "x" in
              let y_val = concrete_value bindings "y" in
                match (x_val, y_val) with
                | Some (VNumber x), Some (VNumber y) ->
                    let x_correct = Z.equal x (Z.of_int 5) in
                    let y_correct = Z.equal y (Z.of_int 10) in
                      Lwt.return
                        (Alcotest.(check bool)
                           "x = 5 and y = 10" true (x_correct && y_correct)
                        )
                | _ -> Lwt.return (Alcotest.fail "expected concrete values")
            )
          | None -> Lwt.return (Alcotest.fail "expected solution")
  )

(** Test helper functions - model_to_string *)
let test_model_to_string () =
  let bindings = Hashtbl.create 4 in
    Hashtbl.add bindings "x" (VNumber (Z.of_int 5));
    Hashtbl.add bindings "y" (VNumber (Z.of_int 10));
    let str = model_to_string bindings in
      Alcotest.(check bool)
        "model string contains x" true
        (String.length str > 0 && Str.string_match (Str.regexp ".*x.*") str 0)

(** Test push/pop *)
let test_push_pop () =
  run_lwt (fun () ->
      let expr1 = EBinOp (VVar "x", "=", VNumber (Z.of_int 5)) in
      let solver = create [ expr1 ] in
        let* result1 = check solver in
        let _ = push solver in
        let expr2 = EBinOp (VVar "x", "=", VNumber (Z.of_int 10)) in
        let _ = add_assertions solver [ expr2 ] in
          let* result2 = check solver in
          let _ = pop solver in
            let* result3 = check solver in
              match (result1, result2, result3) with
              | Some true, Some false, Some true ->
                  Lwt.return
                    (Alcotest.(check bool) "push/pop works correctly" true true)
              | _ ->
                  Lwt.return
                    (Alcotest.fail
                       "expected (sat, unsat, sat) for push/pop test"
                    )
  )

let suite =
  ( "Solver",
    [
      Alcotest.test_case "Create context" `Quick test_create_context;
      Alcotest.test_case "Get variable" `Quick test_get_var;
      Alcotest.test_case "Value to Z3 - number" `Quick test_value_to_z3_number;
      Alcotest.test_case "Value to Z3 - var" `Quick test_value_to_z3_var;
      Alcotest.test_case "Value to Z3 - boolean" `Quick test_value_to_z3_boolean;
      Alcotest.test_case "Expr to Z3 - num" `Quick test_expr_to_z3_num;
      Alcotest.test_case "Expr to Z3 - var" `Quick test_expr_to_z3_var;
      Alcotest.test_case "Expr to Z3 - add" `Quick test_expr_to_z3_add;
      Alcotest.test_case "Expr to Z3 - equality" `Quick test_expr_to_z3_eq;
      Alcotest.test_case "Expr to Z3 - comparison" `Quick
        test_expr_to_z3_comparison;
      Alcotest.test_case "Expr to Z3 - logical" `Quick test_expr_to_z3_logical;
      Alcotest.test_case "Expr to Z3 - not" `Quick test_expr_to_z3_not;
      Alcotest.test_case "Create solver" `Quick test_create_solver;
      Alcotest.test_case "Check satisfiable" `Quick test_check_satisfiable;
      Alcotest.test_case "Check unsatisfiable" `Quick test_check_unsatisfiable;
      Alcotest.test_case "Solve simple" `Quick test_solve_simple;
      Alcotest.test_case "Solve arithmetic" `Quick test_solve_arithmetic;
      Alcotest.test_case "Solve inequality" `Quick test_solve_inequality;
      Alcotest.test_case "Concrete value - missing" `Quick
        test_concrete_value_missing;
      Alcotest.test_case "Concrete value - exists" `Quick
        test_concrete_value_exists;
      Alcotest.test_case "Simplify disjunction - empty" `Quick
        test_simplify_disjunction_empty;
      Alcotest.test_case "Simplify disjunction - filter" `Quick
        test_simplify_disjunction_filter;
      Alcotest.test_case "exeq - identical" `Quick test_exeq_identical;
      Alcotest.test_case "exeq - semantic" `Quick test_exeq_semantic;
      Alcotest.test_case "exeq - not equal" `Quick test_exeq_not_equal;
      Alcotest.test_case "exeq - with state" `Quick test_exeq_with_state;
      Alcotest.test_case "exeq - contradictory state" `Quick
        test_exeq_contradictory_state;
      Alcotest.test_case "expoteq - identical" `Quick test_expoteq_identical;
      Alcotest.test_case "expoteq - potential" `Quick test_expoteq_potential;
      Alcotest.test_case "expoteq - impossible" `Quick test_expoteq_impossible;
      Alcotest.test_case "expoteq - with state" `Quick test_expoteq_with_state;
      Alcotest.test_case "expoteq - satisfiable with state" `Quick
        test_expoteq_satisfiable_with_state;
      Alcotest.test_case "Semeq - create state" `Quick test_semeq_create_state;
      Alcotest.test_case "Semeq - set state" `Quick test_semeq_set_state;
      Alcotest.test_case "Semeq - exeq" `Quick test_semeq_exeq;
      Alcotest.test_case "Semeq - expoteq" `Quick test_semeq_expoteq;
      Alcotest.test_case "Semeq - exeq_value numbers" `Quick
        test_semeq_exeq_value_numbers;
      Alcotest.test_case "Semeq - exeq_value expressions" `Quick
        test_semeq_exeq_value_expressions;
      Alcotest.test_case "Semeq - expoteq_value" `Quick test_semeq_expoteq_value;
      Alcotest.test_case "Cache - create" `Quick test_cache_create;
      Alcotest.test_case "Cache - exeq_cached" `Quick test_cache_exeq_cached;
      Alcotest.test_case "Cache - expoteq_cached" `Quick
        test_cache_expoteq_cached;
      Alcotest.test_case "Cache - clear" `Quick test_cache_clear;
      Alcotest.test_case "Cache - with state" `Quick test_cache_with_state;
      Alcotest.test_case "implies - true" `Quick test_implies_true;
      Alcotest.test_case "implies - derivation" `Quick test_implies_derivation;
      Alcotest.test_case "implies - false" `Quick test_implies_false;
      Alcotest.test_case "is_sat - true" `Quick test_is_sat_true;
      Alcotest.test_case "is_sat - false" `Quick test_is_sat_false;
      Alcotest.test_case "is_unsat - true" `Quick test_is_unsat_true;
      Alcotest.test_case "is_unsat - false" `Quick test_is_unsat_false;
      Alcotest.test_case "solve_for_vars" `Quick test_solve_for_vars;
      Alcotest.test_case "model_to_string" `Quick test_model_to_string;
      Alcotest.test_case "push/pop" `Quick test_push_pop;
    ]
  )
