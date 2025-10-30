(** Expression rewriting and simplification *)

open Types
open Expr
open Printf
open Lwt.Syntax

(** Basic rewrite rules *)
let rules =
  [ (* Identity rules *)
    (* a + 0 = a *)
    (* a - 0 = a *)
    (* a * 1 = a *)
    (* a / 1 = a *)
    (* a * 0 = 0 *)
    (* a - a = 0 *) ]

(** Simplify arithmetic expressions *)
let rec simplify_arith = function
  | EBinOp (ENum l, op, ENum r) when List.mem op [ "+"; "-"; "*"; "/" ] -> (
      match op with
      | "+" -> ENum (Z.add l r)
      | "-" -> ENum (Z.sub l r)
      | "*" -> ENum (Z.mul l r)
      | "/" when not (Z.equal r Z.zero) -> ENum (Z.div l r)
      | _ -> failwith "Division by zero"
    )
  | EBinOp (ENum l, op, r) when List.mem op [ "+"; "-"; "*"; "/" ] -> (
      match op with
      | "+" when Z.equal l Z.zero -> simplify_arith r
      | "-" when Z.equal l Z.zero -> simplify_arith r
      | "*" when Z.equal l Z.zero -> ENum Z.zero
      | "*" when Z.equal l Z.one -> simplify_arith r
      | "/" when Z.equal l Z.zero -> ENum Z.zero
      | _ ->
          let r' = simplify_arith r in
            EBinOp (ENum l, op, r')
    )
  | EBinOp (l, op, ENum r) when List.mem op [ "+"; "-"; "*"; "/" ] -> (
      match op with
      | "+" when Z.equal r Z.zero -> simplify_arith l
      | "*" when Z.equal r Z.zero -> ENum Z.zero
      | "*" when Z.equal r Z.one -> simplify_arith l
      | "/" when Z.equal r Z.zero -> failwith "Division by zero"
      | _ ->
          let l' = simplify_arith l in
            EBinOp (l', op, ENum r)
    )
  | EBinOp (lhs, op, rhs) ->
      let lhs' = simplify_arith lhs in
      let rhs' = simplify_arith rhs in
        EBinOp (lhs', op, rhs')
  | EUnOp (op, r) ->
      let r' = simplify_arith r in
        EUnOp (op, r')
  | e -> e

(** Sort expressions for canonical form *)
let sort_expr expr =
  (* Local function to convert value to string for comparison *)
  let rec value_to_string = function
    | VNumber n -> Z.to_string n
    | VSymbol s -> s
    | VVar v -> v
    | VBoolean b -> string_of_bool b
  and expr_to_string = function
    (* TODO duplicate *)
    | ENum n -> Z.to_string n
    | EBoolean b -> string_of_bool b
    | ESymbol s -> s
    | EVar v -> v
    | EBinOp (l, op, r) ->
        Printf.sprintf "(%s %s %s)" (expr_to_string l) op (expr_to_string r)
    | EUnOp (op, r) -> sprintf "%s(%s)" op (expr_to_string r)
    | EOr _ -> "or"
  in

  match expr with
  | EBinOp (lhs, op, rhs) when List.mem op [ "="; "!="; "+"; "*" ] ->
      (* Commutative operations - sort operands by swapping if needed *)
      if compare (expr_to_string lhs) (expr_to_string rhs) > 0 then
        EBinOp (rhs, op, lhs) (* Swap operands *)
      else expr
  | _ -> expr

(** Main rewriting function *)
let rewrite expr = expr |> simplify_arith |> sort_expr

(** Rewrite predicate (list of expressions) *)
let rewrite_pred_sync exprs = List.map rewrite exprs

let rewrite_pred exprs =
  let* _ = Lwt.return_unit in

  (* Filter tautologies *)
  let exprs =
    List.filter
      (fun e ->
        match e with
        | EBinOp (lhs, op, rhs) ->
            let is_taut =
              match (lhs, op, rhs) with
              | l, ("=" | "<=" | ">="), r when l = r -> true
              | _ -> false
            in
              not is_taut
        | _ -> true
      )
      exprs
  in

  (* Check for contradictions *)
  let has_contradiction =
    List.exists (fun e -> Expr.is_contradiction e) exprs
  in

  if has_contradiction then Lwt.return_none
  else
    (* Rewrite each expression *)
    let exprs' = rewrite_pred_sync exprs in

    (* Remove duplicates and sort *)
    let exprs'' =
      List.sort_uniq
        (fun e1 e2 -> String.compare (Expr.to_string e1) (Expr.to_string e2))
        exprs'
    in

    Lwt.return_some exprs''
