(** Expression rewriting and simplification *)

open Types
open Expr

type pattern =
  | PVar of string  (* Variable that matches anything *)
  | PLit of string  (* Literal that matches specific values *)
  | PNum of Z.t     (* Number pattern *)
  | PExpr of pattern * string * pattern  (* Expression pattern *)

type rewrite_rule = {
  pattern: pattern;
  rewrite: (string * value_type) list -> expr;
}

(** Basic rewrite rules *)
let rules = [
  (* Identity rules *)
  (* a + 0 = a *)
  (* a - 0 = a *)
  (* a * 1 = a *)
  (* a / 1 = a *)
  (* a * 0 = 0 *)
  (* a - a = 0 *)
]

(** Check if value matches pattern *)
let rec matches_pattern pat value bindings =
  (* Local value equality function *)
  let value_eq v1 v2 =
    match (v1, v2) with
    | VNumber n1, VNumber n2 -> Z.equal n1 n2
    | VSymbol s1, VSymbol s2 -> String.equal s1 s2
    | VVar v1, VVar v2 -> String.equal v1 v2
    | VBoolean b1, VBoolean b2 -> b1 = b2
    | VExpression e1, VExpression e2 -> e1 = e2  (* Structural equality *)
    | _ -> false
  in
  
  match pat with
  | PVar name ->
      (match List.assoc_opt name bindings with
       | Some v -> if value_eq v value then Some bindings else None
       | None -> Some ((name, value) :: bindings))
  | PLit s ->
      (match value with
       | VVar v when v = s -> Some bindings
       | VSymbol v when v = s -> Some bindings
       | _ -> None)
  | PNum n ->
      (match value with
       | VNumber m when Z.equal n m -> Some bindings
       | _ -> None)
  | PExpr (lpat, op, rpat) ->
      (match value with
       | VExpression (EBinOp (lhs, op', rhs)) when op = op' ->
           (match matches_pattern lpat lhs bindings with
            | Some b1 -> matches_pattern rpat rhs b1
            | None -> None)
       | _ -> None)

(** Apply rewrite rule *)
let apply_rule rule expr =
  match matches_pattern rule.pattern (VExpression expr) [] with
  | Some bindings -> Some (rule.rewrite bindings)
  | None -> None

(** Fixed point rewriting *)
let rec fixed_rewrite expr =
  let rec try_rules e = function
    | [] -> e
    | rule :: rest ->
        match apply_rule rule e with
        | Some e' -> fixed_rewrite e'
        | None -> try_rules e rest
  in
  
  (* Recursively rewrite subexpressions *)
  let e = match expr with
    | EBinOp (lhs, op, rhs) ->
        let lhs' = match lhs with
          | VExpression e -> VExpression (fixed_rewrite e)
          | _ -> lhs
        in
        let rhs' = match rhs with
          | VExpression e -> VExpression (fixed_rewrite e)
          | _ -> rhs
        in
        EBinOp (lhs', op, rhs')
    | _ -> expr
  in
  
  try_rules e rules

(** Simplify arithmetic expressions *)
let rec simplify_arith = function
  | EBinOp (VNumber l, "+", VNumber r) -> ENum (Z.add l r)
  | EBinOp (VNumber l, "-", VNumber r) -> ENum (Z.sub l r)
  | EBinOp (VNumber l, "*", VNumber r) -> ENum (Z.mul l r)
  | EBinOp (VNumber l, "/", VNumber r) when not (Z.equal r Z.zero) ->
      ENum (Z.div l r)
  | EBinOp (lhs, "+", VNumber n) when Z.equal n Z.zero ->
      (match lhs with VExpression e -> e | _ -> EVar "?")
  | EBinOp (_, "*", VNumber n) when Z.equal n Z.zero -> ENum Z.zero
  | EBinOp (lhs, "*", VNumber n) when Z.equal n Z.one ->
      (match lhs with VExpression e -> e | _ -> EVar "?")
  | EBinOp (lhs, op, rhs) ->
      let lhs' = match lhs with
        | VExpression e -> VExpression (simplify_arith e)
        | _ -> lhs
      in
      let rhs' = match rhs with
        | VExpression e -> VExpression (simplify_arith e)
        | _ -> rhs
      in
      EBinOp (lhs', op, rhs')
  | e -> e

(** Sort expressions for canonical form *)
let sort_expr expr =
  (* Local function to convert value to string for comparison *)
  let rec value_to_string = function
    | VNumber n -> Z.to_string n
    | VSymbol s -> s
    | VVar v -> v
    | VBoolean b -> string_of_bool b
    | VExpression e -> expr_to_string e
  and expr_to_string = function
    | ENum n -> Z.to_string n
    | EVar v -> v
    | EBinOp (l, op, r) -> Printf.sprintf "(%s %s %s)" (value_to_string l) op (value_to_string r)
    | EUnOp (op, r) -> Printf.sprintf "%s(%s)" op (value_to_string r)
    | EOr _ -> "or"
  in
  
  match expr with
  | EBinOp (lhs, op, rhs) when List.mem op ["="; "!="; "+"; "*"] ->
      (* Commutative operations - sort operands by swapping if needed *)
      if compare (value_to_string lhs) (value_to_string rhs) > 0 then
        EBinOp (rhs, op, lhs)  (* Swap operands *)
      else
        expr
  | _ -> expr

(** Main rewriting function *)
let rewrite expr =
  expr
  |> simplify_arith
  |> fixed_rewrite
  |> sort_expr

(** Rewrite predicate (list of expressions) *)
let rewrite_pred_sync exprs =
  List.map rewrite exprs

(** Async version with solver integration *)
open Lwt.Syntax

let rewrite_pred exprs =
  let* _ = Lwt.return_unit in
  
  (* Filter tautologies *)
  let exprs = List.filter (fun e -> 
    match e with
    | EBinOp (lhs, op, rhs) ->
        let is_taut = match (lhs, op, rhs) with
          | (l, ("=" | "<=" | ">="), r) when l = r -> true
          | _ -> false
        in
        not is_taut
    | _ -> true
  ) exprs in
  
  (* Check for contradictions *)
  let has_contradiction = List.exists (fun e ->
    match e with
    | EBinOp (VNumber l, op, VNumber r) ->
        let b = match op with
          | "=" -> Z.equal l r
          | "!=" -> not (Z.equal l r)
          | "<" -> Z.lt l r
          | ">" -> Z.gt l r
          | "<=" -> Z.leq l r
          | ">=" -> Z.geq l r
          | _ -> true
        in
        not b
    | EBinOp (l, ("<" | ">" | "!="), r) when l = r -> true
    | _ -> false
  ) exprs in
  
  if has_contradiction then
    Lwt.return_none
  else
    (* Rewrite each expression *)
    let exprs' = rewrite_pred_sync exprs in
    
    (* Remove duplicates and sort *)
    let exprs'' = 
      List.sort_uniq (fun e1 e2 ->
        String.compare (Expr.to_string e1) (Expr.to_string e2)
      ) exprs'
    in
    
    Lwt.return_some exprs''
