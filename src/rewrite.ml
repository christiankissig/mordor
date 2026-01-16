(** Expression rewriting and simplification *)

open Expr

(** Basic rewrite rules *)
let rules =
  [ (* Identity rules *)
    (* a + 0 = a *)
    (* a - 0 = a *)
    (* a * 1 = a *)
    (* a / 1 = a *)
    (* a * 0 = 0 *)
    (* a - a = 0 *) ]

(** Main rewriting function *)
let rewrite expr = Expr.evaluate expr |> Expr.sort_expr

(** Rewrite predicate (list of expressions) *)
let rewrite_pred_sync exprs = List.map rewrite exprs

let rewrite_pred exprs =
  if List.exists Expr.is_contradiction exprs then None
  else Some (rewrite_pred_sync exprs |> List.sort_uniq Expr.compare)
