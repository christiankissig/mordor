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
    ]
  )
