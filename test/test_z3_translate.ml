(** The native {!Smt_backend}'s translation of MoRDor's expressions into Z3
    terms ({!Z3_translate}). Moved from [test_solver.ml] with the translation
    itself (W2, #178). *)

open Types
open Z3_translate

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
  let expr = EBinOp (ENum (Z.of_int 5), "+", ENum (Z.of_int 3)) in
  let z3_expr = expr_to_z3 ctx expr in
  let str = Z3.Expr.to_string z3_expr in
    Alcotest.(check bool) "addition expr created" true (String.length str > 0)

(** Test expression to Z3 - equality *)
let test_expr_to_z3_eq () =
  let ctx = create_context () in
  let expr = EBinOp (EVar "x", "=", ENum (Z.of_int 10)) in
  let z3_expr = expr_to_z3 ctx expr in
    Alcotest.(check bool) "equality expr created" true (Z3.Boolean.is_eq z3_expr)

(** Test expression to Z3 - comparison operators *)
let test_expr_to_z3_comparison () =
  let ctx = create_context () in
  let expr_lt = EBinOp (EVar "x", "<", ENum (Z.of_int 5)) in
  let expr_gt = EBinOp (EVar "x", ">", ENum (Z.of_int 5)) in
  let expr_le = EBinOp (EVar "x", "<=", ENum (Z.of_int 5)) in
  let expr_ge = EBinOp (EVar "x", ">=", ENum (Z.of_int 5)) in
  let _ = expr_to_z3 ctx expr_lt in
  let _ = expr_to_z3 ctx expr_gt in
  let _ = expr_to_z3 ctx expr_le in
  let _ = expr_to_z3 ctx expr_ge in
    Alcotest.(check bool) "comparison exprs created" true true

(** Test expression to Z3 - logical operators *)
let test_expr_to_z3_logical () =
  let ctx = create_context () in
  let expr_and = EBinOp (EBoolean true, "&&", EBoolean false) in
  let expr_or = EBinOp (EBoolean true, "||", EBoolean false) in
  let expr_impl = EBinOp (EBoolean true, "=>", EBoolean false) in
  let _ = expr_to_z3 ctx expr_and in
  let _ = expr_to_z3 ctx expr_or in
  let _ = expr_to_z3 ctx expr_impl in
    Alcotest.(check bool) "logical exprs created" true true

(** Test expression to Z3 - unary not *)
let test_expr_to_z3_not () =
  let ctx = create_context () in
  let expr = EUnOp ("!", EBoolean true) in
  let z3_expr = expr_to_z3 ctx expr in
    Alcotest.(check bool) "not expr created" true (Z3.Boolean.is_not z3_expr)

let suite =
  ( "Z3 translation",
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
    ]
  )
