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

let test_value_constructors () =
  let n = v_num 42 in
  let s = v_sym "α" in
  let v = v_var "x" in
  let b = v_bool true in
    Alcotest.(check bool)
      "number is created" true
      ( match n with
      | VNumber _ -> true
      | _ -> false
      );
    Alcotest.(check bool)
      "symbol is created" true
      ( match s with
      | VSymbol _ -> true
      | _ -> false
      );
    Alcotest.(check bool)
      "var is created" true
      ( match v with
      | VVar _ -> true
      | _ -> false
      );
    Alcotest.(check bool)
      "boolean is created" true
      ( match b with
      | VBoolean _ -> true
      | _ -> false
      )

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
  let eq = e_binop (e_var "x") "=" (e_num 5) in
  let neq = Expr.inverse eq in
    Alcotest.(check bool)
      "inverse of =" true
      ( match neq with
      | EBinOp (_, "!=", _) -> true
      | _ -> false
      );

    let lt = e_binop (e_var "x") "<" (e_num 5) in
    let gte = Expr.inverse lt in
      Alcotest.(check bool)
        "inverse of <" true
        ( match gte with
        | EBinOp (_, ">=", _) -> true
        | _ -> false
        );

      let gt = e_binop (e_var "x") ">" (e_num 5) in
      let lte = Expr.inverse gt in
        Alcotest.(check bool)
          "inverse of >" true
          ( match lte with
          | EBinOp (_, "<=", _) -> true
          | _ -> false
          )

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

(* Test suite *)
let suite =
  ( "Expressions",
    [
      (* Value tests *)
      Alcotest.test_case "Value constructors" `Quick test_value_constructors;
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
    ]
  )
