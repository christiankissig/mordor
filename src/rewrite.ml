(** Expression rewriting and simplification *)

open Expr
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

(** Main rewriting function *)
let rewrite expr = Expr.evaluate expr (fun _ -> None) |> Expr.sort_expr

(** Rewrite predicate (list of expressions) *)
let rewrite_pred_sync exprs = List.map rewrite exprs

let rewrite_pred exprs =
  let* _ = Lwt.return_unit in

  (* REMOVED filter tautologies *)

  (* Check for contradictions *)
  if List.exists Expr.is_contradiction exprs then (
    Logs.debug (fun m -> m "Contradiction found during rewriting.\n");
    Lwt.return_none
  )
  else
    (* Rewrite each expression *)
    let exprs' = rewrite_pred_sync exprs in

    (* Remove duplicates and sort *)
    let exprs'' = List.sort_uniq Expr.compare exprs' in

    if List.length exprs'' < List.length exprs' then
      Logs.debug (fun m ->
          m
            "Found duplicates during rewriting. Reduced from %d to %d \
             expressions.\n"
            (List.length exprs) (List.length exprs'')
      );

    Lwt.return_some exprs''
