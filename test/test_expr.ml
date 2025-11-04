open Uset
open Expr
open Types

(* Helper to create test values *)
let v_num n = Value.number (Z.of_int n)
let v_sym s = Value.symbol s
let v_var v = Value.var v
let v_bool b = Value.boolean b
let e_num n = Expr.num (Z.of_int n)
let e_var v = Expr.var v
let e_sym s = ESymbol s
let e_binop l op r = Expr.binop l op r

(* Value module tests *)

let test_value_equality () =
  let n1 = v_num 42 in
  let n2 = v_num 42 in
  let n3 = v_num 99 in
  let s1 = v_sym "α" in
  let s2 = v_sym "α" in
  let s3 = v_sym "β" in
    Alcotest.(check bool) "equal numbers" true (Value.equal n1 n2);
    Alcotest.(check bool) "unequal numbers" false (Value.equal n1 n3);
    Alcotest.(check bool) "equal symbols" true (Value.equal s1 s2);
    Alcotest.(check bool) "unequal symbols" false (Value.equal s1 s3);
    Alcotest.(check bool) "number != symbol" false (Value.equal n1 s1)

let test_value_to_string () =
  let n = v_num 42 in
  let s = v_sym "α" in
  let v = v_var "x" in
  let b = v_bool true in
    Alcotest.(check string) "number to string" "42" (Value.to_string n);
    Alcotest.(check string) "symbol to string" "α" (Value.to_string s);
    Alcotest.(check string) "var to string" "x" (Value.to_string v);
    Alcotest.(check string) "boolean to string" "true" (Value.to_string b)

let test_value_get_symbols () =
  let s = v_sym "α" in
  let n = v_num 42 in
  let symbols = Value.get_symbols s in
  let no_symbols = Value.get_symbols n in
    Alcotest.(check bool) "symbol extracted" true (List.mem "α" symbols);
    Alcotest.(check int) "no symbols from number" 0 (List.length no_symbols)

let test_value_subst () =
  let s1 = v_sym "α" in
  let s2 = v_sym "β" in
  let result = Value.subst s1 s1 s2 in
    Alcotest.(check bool) "substitution works" true (Value.equal result s2);
    let no_change = Value.subst (v_num 42) s1 s2 in
      Alcotest.(check bool)
        "no substitution on number" true
        (Value.equal no_change (v_num 42))

(* Expr module tests *)

let test_expr_constructors () =
  let num_expr = e_num 42 in
  let var_expr = e_var "x" in
  let binop_expr = e_binop (e_num 1) "+" (e_num 2) in
  let unop_expr = Expr.unop "-" (e_num 5) in
    Alcotest.(check bool)
      "num expr created" true
      ( match num_expr with
      | ENum _ -> true
      | _ -> false
      );
    Alcotest.(check bool)
      "var expr created" true
      ( match var_expr with
      | EVar _ -> true
      | _ -> false
      );
    Alcotest.(check bool)
      "binop expr created" true
      ( match binop_expr with
      | EBinOp _ -> true
      | _ -> false
      );
    Alcotest.(check bool)
      "unop expr created" true
      ( match unop_expr with
      | EUnOp _ -> true
      | _ -> false
      )

let test_expr_equality () =
  let e1 = e_binop (e_num 1) "+" (e_num 2) in
  let e2 = e_binop (e_num 1) "+" (e_num 2) in
  let e3 = e_binop (e_num 1) "*" (e_num 2) in
  let e4 = e_binop (e_num 2) "+" (e_num 1) in
    Alcotest.(check bool) "equal expressions" true (Expr.equal e1 e2);
    Alcotest.(check bool) "different operators" false (Expr.equal e1 e3);
    Alcotest.(check bool) "different operands" false (Expr.equal e1 e4)

let test_expr_to_string () =
  let e1 = e_binop (e_num 1) "+" (e_num 2) in
  let e2 = Expr.unop "-" (e_num 5) in
  let s1 = Expr.to_string e1 in
  let s2 = Expr.to_string e2 in
    Alcotest.(check bool)
      "binop string contains operator" true (String.contains s1 '+');
    Alcotest.(check bool)
      "unop string contains operator" true (String.contains s2 '-')

let test_expr_get_symbols () =
  let e = e_binop (e_sym "α") "+" (e_sym "β") in
  let symbols = Expr.get_symbols e in
    Alcotest.(check bool) "extracts first symbol" true (List.mem "α" symbols);
    Alcotest.(check bool) "extracts second symbol" true (List.mem "β" symbols)

let test_expr_is_flat () =
  let flat1 = e_binop (e_num 1) "=" (e_num 2) in
  let flat2 = e_binop (e_var "x") "<" (e_num 10) in
  let no_flat = e_binop (e_binop (e_num 1) "+" (e_num 2)) "=" (e_num 3) in
    Alcotest.(check bool) "flat comparison" true (Expr.is_flat flat1);
    Alcotest.(check bool) "flat with var" true (Expr.is_flat flat2);
    Alcotest.(check bool) "non-flat expression" false (Expr.is_flat no_flat)

let test_expr_inverse () =
  let cases =
    [
      ("inverse of =", "!=", e_binop (e_var "x") "=" (e_num 5));
      ("inverse of !=", "=", e_binop (e_var "x") "!=" (e_num 5));
      ("inverse of <", ">=", e_binop (e_var "x") "<" (e_num 5));
      ("inverse of >=", "<", e_binop (e_var "x") ">=" (e_num 5));
      ("inverse of >", "<=", e_binop (e_var "x") ">" (e_num 5));
      ("inverse of <=", ">", e_binop (e_var "x") "<=" (e_num 5));
    ]
  in
    List.iter
      (fun (name, expected_op, expr) ->
        let inv = Expr.inverse expr in
          Alcotest.(check bool)
            name true
            ( match inv with
            | EBinOp (_, op, _) when op = expected_op -> true
            | _ -> false
            )
      )
      cases

let test_expr_flipped () =
  let e1 = e_binop (e_num 1) "<" (e_num 2) in
  let flipped = Expr.flipped e1 in
    Alcotest.(check bool)
      "< flips to >" true
      ( match flipped with
      | EBinOp (ENum n, ">", ENum m) ->
          Z.equal n (Z.of_int 2) && Z.equal m (Z.of_int 1)
      | _ -> false
      );

    let e2 = e_binop (e_num 1) "+" (e_num 2) in
    let flipped2 = Expr.flipped e2 in
      Alcotest.(check bool)
        "+ is commutative" true
        ( match flipped2 with
        | EBinOp (ENum n, "+", ENum m) ->
            Z.equal n (Z.of_int 2) && Z.equal m (Z.of_int 1)
        | _ -> false
        );

      (* Non-commutative operations should not flip *)
      let e3 = e_binop (e_num 1) "-" (e_num 2) in
      let flipped3 = Expr.flipped e3 in
        Alcotest.(check bool)
          "- doesn't flip" true
          ( match flipped3 with
          | EBinOp (ENum n, "-", ENum m) ->
              Z.equal n (Z.of_int 1) && Z.equal m (Z.of_int 2)
          | _ -> false
          )

let test_expr_subst () =
  let x = e_var "x" in
  let five = e_num 5 in
  let e = e_binop x "+" (e_num 2) in
  let result = Expr.subst e "x" five in
    Alcotest.(check bool)
      "substitution applied" true
      ( match result with
      | EBinOp (ENum n, "+", ENum m) ->
          Z.equal n (Z.of_int 5) && Z.equal m (Z.of_int 2)
      | _ -> false
      )

let test_expr_flatten () =
  let e1 = e_num 1 in
  let e2 = e_num 2 in
  let e3 = e_num 3 in
  let and_expr = e_binop e1 "&&" e2 in
  let nested = e_binop and_expr "&&" e3 in
  let flat = Expr.flatten nested in
    Alcotest.(check bool) "flattens && operations" true (List.length flat > 1)

let test_expr_is_tautology () =
  let x = e_var "x" in
  let taut1 = e_binop x "=" x in
  let taut2 = e_binop x "<=" x in
  let taut3 = e_binop x ">=" x in
  let not_taut = e_binop x "<" x in
    Alcotest.(check bool) "x = x is tautology" true (Expr.is_tautology taut1);
    Alcotest.(check bool) "x <= x is tautology" true (Expr.is_tautology taut2);
    Alcotest.(check bool) "x >= x is tautology" true (Expr.is_tautology taut3);
    Alcotest.(check bool)
      "x < x is not tautology" false
      (Expr.is_tautology not_taut)

let test_expr_is_contradiction () =
  let x = e_var "x" in
  let contr1 = e_binop x "<" x in
  let contr2 = e_binop x ">" x in
  let contr3 = e_binop x "!=" x in
  let not_contr = e_binop x "=" x in
    Alcotest.(check bool)
      "x < x is contradiction" true
      (Expr.is_contradiction contr1);
    Alcotest.(check bool)
      "x > x is contradiction" true
      (Expr.is_contradiction contr2);
    Alcotest.(check bool)
      "x != x is contradiction" true
      (Expr.is_contradiction contr3);
    Alcotest.(check bool)
      "x = x is not contradiction" false
      (Expr.is_contradiction not_contr);

    (* Test with concrete numbers *)
    let false_eq = e_binop (e_num 1) "=" (e_num 2) in
    let true_eq = e_binop (e_num 1) "=" (e_num 1) in
      Alcotest.(check bool)
        "1 = 2 is contradiction" true
        (Expr.is_contradiction false_eq);
      Alcotest.(check bool)
        "1 = 1 is not contradiction" false
        (Expr.is_contradiction true_eq)

let test_is_number () =
  let n = e_num 42 in
  let s = e_sym "α" in
    Alcotest.(check bool) "number is_number" true (Expr.is_number n);
    Alcotest.(check bool) "symbol not is_number" false (Expr.is_number s)

(* Evaluate function tests *)

let test_evaluate_literals () =
  let cases = [ ENum (Z.of_int 42); EBoolean true; ESymbol "α" ] in
  let empty_env _ = None in
    List.iter
      (fun expr ->
        Expr.evaluate expr empty_env
        |> Expr.equal expr
        |> Alcotest.(check bool) "literal evaluates to itself" true
      )
      cases

let test_evaluate_var_lookup () =
  (* Variable with value in environment *)
  let env_with_x v = if v = "x" then Some (e_num 10) else None in
  let x = e_var "x" in
  let result = Expr.evaluate x env_with_x in
    Alcotest.(check bool)
      "variable looks up value" true
      (Expr.equal result (e_num 10));

    (* Variable without value in environment *)
    let empty_env _ = None in
    let y = e_var "y" in
    let result_y = Expr.evaluate y empty_env in
      Alcotest.(check bool)
        "undefined variable returns itself" true (Expr.equal result_y y)

let test_evaluate_arithmetic () =
  let cases =
    [
      ("addition", e_binop (e_num 5) "+" (e_num 3), e_num 8);
      ("subtraction", e_binop (e_num 10) "-" (e_num 4), e_num 6);
      ("multiplication", e_binop (e_num 6) "*" (e_num 7), e_num 42);
      ("division", e_binop (e_num 20) "/" (e_num 4), e_num 5);
    ]
  in
  let empty_env _ = None in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr empty_env in
          Alcotest.(check bool)
            (name ^ " evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_division_by_zero () =
  let empty_env _ = None in
  let div_zero = e_binop (e_num 10) "/" (e_num 0) in
    Alcotest.check_raises "division by zero raises exception"
      (Failure "Division by zero") (fun () ->
        ignore (Expr.evaluate div_zero empty_env)
    )

let test_evaluate_comparisons () =
  let cases =
    [
      ("equality", e_binop (e_num 5) "=" (e_num 5), EBoolean true);
      ("inequality", e_binop (e_num 5) "!=" (e_num 3), EBoolean true);
      ("less than", e_binop (e_num 3) "<" (e_num 5), EBoolean true);
      ("greater than", e_binop (e_num 5) ">" (e_num 3), EBoolean true);
      ("less than or equal", e_binop (e_num 3) "<=" (e_num 5), EBoolean true);
      ("greater than or equal", e_binop (e_num 5) ">=" (e_num 3), EBoolean true);
    ]
  in
  let empty_env _ = None in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr empty_env in
          Alcotest.(check bool)
            (name ^ " comparison evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_boolean_ops () =
  let empty_env _ = None in
  let cases =
    [
      (* Logical AND cases *)
      ("and_true", e_binop (EBoolean true) "&&" (EBoolean true), EBoolean true);
      ( "and_false",
        e_binop (EBoolean true) "&&" (EBoolean false),
        EBoolean false
      );
      (* Logical OR cases *)
      ("or_true", e_binop (EBoolean true) "||" (EBoolean false), EBoolean true);
      ( "or_false",
        e_binop (EBoolean false) "||" (EBoolean false),
        EBoolean false
      );
      (* Boolean equality case *)
      ("bool_eq", e_binop (EBoolean true) "=" (EBoolean true), EBoolean true);
      (* Boolean inequality case *)
      ("bool_neq", e_binop (EBoolean true) "!=" (EBoolean false), EBoolean true);
    ]
  in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr empty_env in
          Alcotest.(check bool)
            (name ^ " boolean operation evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_reflexive_var () =
  let empty_env _ = None in
  let cases =
    [
      ("equality", e_binop (e_var "x") "=" (e_var "x"), EBoolean true);
      ("inequality", e_binop (e_var "x") "!=" (e_var "x"), EBoolean false);
      ("less than", e_binop (e_var "x") "<" (e_var "x"), EBoolean false);
      ("greater than", e_binop (e_var "x") ">" (e_var "x"), EBoolean false);
      ("less than or equal", e_binop (e_var "x") "<=" (e_var "x"), EBoolean true);
      ( "greater than or equal",
        e_binop (e_var "x") ">=" (e_var "x"),
        EBoolean true
      );
    ]
  in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr empty_env in
          Alcotest.(check bool)
            (name ^ " with variable evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_reflexive_symbol () =
  let empty_env _ = None in
  let cases =
    [
      ("equality", e_binop (e_sym "α") "=" (e_sym "α"), EBoolean true);
      ("inequality", e_binop (e_sym "α") "!=" (e_sym "α"), EBoolean false);
      ("less than", e_binop (e_sym "α") "<" (e_sym "α"), EBoolean false);
      ("greater than", e_binop (e_sym "α") ">" (e_sym "α"), EBoolean false);
      ("less than or equal", e_binop (e_sym "α") "<=" (e_sym "α"), EBoolean true);
      ( "greater than or equal",
        e_binop (e_sym "α") ">=" (e_sym "α"),
        EBoolean true
      );
    ]
  in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr empty_env in
          Alcotest.(check bool)
            (name ^ " with symbol evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_with_variables () =
  let env v =
    match v with
    | "x" -> Some (e_num 5)
    | "y" -> Some (e_num 3)
    | _ -> None
  in
  let cases =
    [
      ("x + y", e_binop (e_var "x") "+" (e_var "y"), e_num 8);
      ("x - y", e_binop (e_var "x") "-" (e_var "y"), e_num 2);
      ("x * y", e_binop (e_var "x") "*" (e_var "y"), e_num 15);
      ("x / y", e_binop (e_var "x") "/" (e_var "y"), e_num 1);
      ("x > y", e_binop (e_var "x") ">" (e_var "y"), EBoolean true);
      ("x < y", e_binop (e_var "x") "<" (e_var "y"), EBoolean false);
    ]
  in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr env in
          Alcotest.(check bool)
            (name ^ " with variables evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_nested_expressions () =
  let empty_env _ = None in
  let cases =
    [
      ( "(2 + 3) * 4 = 20",
        e_binop (e_binop (e_num 2) "+" (e_num 3)) "*" (e_num 4),
        e_num 20
      );
      ( "(10 - 2) / 2 = 4",
        e_binop (e_binop (e_num 10) "-" (e_num 2)) "/" (e_num 2),
        e_num 4
      );
    ]
  in
    List.iter
      (fun (name, expr, expected) ->
        let result = Expr.evaluate expr empty_env in
          Alcotest.(check bool)
            (name ^ " nested expression evaluates correctly")
            true
            (Expr.equal result expected)
      )
      cases

let test_evaluate_unop () =
  let empty_env _ = None in
  (* UnOp with number *)
  let unop_num = Expr.unop "-" (e_num 5) in
  let result_unop = Expr.evaluate unop_num empty_env in
    (* UnOp doesn't actually evaluate the operation, just evaluates the operand *)
    Alcotest.(check bool)
      "unop evaluates operand" true
      ( match result_unop with
      | EUnOp ("-", ENum n) -> Z.equal n (Z.of_int 5)
      | _ -> false
      );

    (* UnOp with variable *)
    let env_x v = if v = "x" then Some (e_num 10) else None in
    let unop_var = Expr.unop "!" (e_var "x") in
    let result_var = Expr.evaluate unop_var env_x in
      Alcotest.(check bool)
        "unop with var substitution" true
        ( match result_var with
        | EUnOp ("!", ENum n) -> Z.equal n (Z.of_int 10)
        | _ -> false
        )

let test_evaluate_eor_clauses () =
  let env v = if v = "x" then Some (e_num 5) else None in
  (* EOr with simple clauses *)
  let clause1 = [ e_var "x"; e_num 1 ] in
  let clause2 = [ e_num 2; e_num 3 ] in
  let eor = EOr [ clause1; clause2 ] in
  let result = Expr.evaluate eor env in
    (* Variables should be substituted *)
    Alcotest.(check bool)
      "EOr evaluates clauses" true
      ( match result with
      | EOr [ [ ENum n1; ENum n2 ]; [ ENum n3; ENum n4 ] ] ->
          Z.equal n1 (Z.of_int 5)
          && Z.equal n2 (Z.of_int 1)
          && Z.equal n3 (Z.of_int 2)
          && Z.equal n4 (Z.of_int 3)
      | _ -> false
      )

let test_evaluate_partial () =
  let empty_env _ = None in
  (* When operands can't be fully evaluated, return binop with evaluated operands *)
  let expr = e_binop (e_var "x") "+" (e_num 5) in
  let result = Expr.evaluate expr empty_env in
    Alcotest.(check bool)
      "partial evaluation keeps structure" true
      ( match result with
      | EBinOp (EVar "x", "+", ENum n) -> Z.equal n (Z.of_int 5)
      | _ -> false
      );

    (* Unsupported operation on booleans *)
    let unsupported = e_binop (EBoolean true) "+" (EBoolean false) in
    let result_unsup = Expr.evaluate unsupported empty_env in
      Alcotest.(check bool)
        "unsupported op returns binop" true
        ( match result_unsup with
        | EBinOp (EBoolean true, "+", EBoolean false) -> true
        | _ -> false
        )

let test_evaluate_complex_with_env () =
  let env v =
    match v with
    | "a" -> Some (e_num 10)
    | "b" -> Some (e_num 20)
    | "c" -> Some (EBoolean true)
    | "d" -> Some (EBoolean false)
    | _ -> None
  in
  (* (a + b) * 2 = 60 *)
  let arith_expr =
    e_binop (e_binop (e_var "a") "+" (e_var "b")) "*" (e_num 2)
  in
  let result_arith = Expr.evaluate arith_expr env in
    Alcotest.(check bool)
      "(a + b) * 2 = 60 when a=10, b=20" true
      (Expr.equal result_arith (e_num 60));

    (* c && d = false *)
    let bool_expr = e_binop (e_var "c") "&&" (e_var "d") in
    let result_bool = Expr.evaluate bool_expr env in
      Alcotest.(check bool)
        "c && d = false when c=true, d=false" true
        (Expr.equal result_bool (EBoolean false));

      (* (a > 5) && c = true *)
      let mixed_expr =
        e_binop (e_binop (e_var "a") ">" (e_num 5)) "&&" (e_var "c")
      in
      let result_mixed = Expr.evaluate mixed_expr env in
        Alcotest.(check bool)
          "(a > 5) && c = true when a=10, c=true" true
          (Expr.equal result_mixed (EBoolean true))

(* Test suite *)
let suite =
  ( "Expressions",
    [
      (* Value tests *)
      Alcotest.test_case "Value equality" `Quick test_value_equality;
      Alcotest.test_case "Value to_string" `Quick test_value_to_string;
      Alcotest.test_case "Value get_symbols" `Quick test_value_get_symbols;
      Alcotest.test_case "Value substitution" `Quick test_value_subst;
      (* Expr tests *)
      Alcotest.test_case "Expr constructors" `Quick test_expr_constructors;
      Alcotest.test_case "Expr equality" `Quick test_expr_equality;
      Alcotest.test_case "Expr to_string" `Quick test_expr_to_string;
      Alcotest.test_case "Expr get_symbols" `Quick test_expr_get_symbols;
      Alcotest.test_case "Expr is_flat" `Quick test_expr_is_flat;
      Alcotest.test_case "Expr inverse" `Quick test_expr_inverse;
      Alcotest.test_case "Expr flipped" `Quick test_expr_flipped;
      Alcotest.test_case "Expr substitution" `Quick test_expr_subst;
      Alcotest.test_case "Expr flatten" `Quick test_expr_flatten;
      Alcotest.test_case "Expr is_tautology" `Quick test_expr_is_tautology;
      Alcotest.test_case "Expr is_contradiction" `Quick
        test_expr_is_contradiction;
      (* Helper function tests *)
      Alcotest.test_case "is_number helper" `Quick test_is_number;
      (* Evaluate function tests *)
      Alcotest.test_case "Evaluate literals" `Quick test_evaluate_literals;
      Alcotest.test_case "Evaluate variable lookup" `Quick
        test_evaluate_var_lookup;
      Alcotest.test_case "Evaluate arithmetic" `Quick test_evaluate_arithmetic;
      Alcotest.test_case "Evaluate division by zero" `Quick
        test_evaluate_division_by_zero;
      Alcotest.test_case "Evaluate comparisons" `Quick test_evaluate_comparisons;
      Alcotest.test_case "Evaluate boolean operations" `Quick
        test_evaluate_boolean_ops;
      Alcotest.test_case "Evaluate reflexive variable" `Quick
        test_evaluate_reflexive_var;
      Alcotest.test_case "Evaluate reflexive symbol" `Quick
        test_evaluate_reflexive_symbol;
      Alcotest.test_case "Evaluate with variables" `Quick
        test_evaluate_with_variables;
      Alcotest.test_case "Evaluate nested expressions" `Quick
        test_evaluate_nested_expressions;
      Alcotest.test_case "Evaluate unary operations" `Quick test_evaluate_unop;
      Alcotest.test_case "Evaluate EOr clauses" `Quick test_evaluate_eor_clauses;
      Alcotest.test_case "Evaluate partial evaluation" `Quick
        test_evaluate_partial;
      Alcotest.test_case "Evaluate complex with environment" `Quick
        test_evaluate_complex_with_env;
    ]
  )
