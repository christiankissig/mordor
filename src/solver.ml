(** Constraint solver using Z3 *)

open Types
open Expr
open Lwt.Syntax

(** Solver context *)
type context = {
  ctx : Z3.context;
  solver : Z3.Solver.solver;
  vars : (string, Z3.Expr.expr) Hashtbl.t;
}

(** Create new solver context *)
let create_context () =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_solver ctx None in
  let vars = Hashtbl.create 32 in
    { ctx; solver; vars }

(** Get or create Z3 variable *)
let get_var context name =
  try Hashtbl.find context.vars name
  with Not_found ->
    let sort = Z3.Arithmetic.Integer.mk_sort context.ctx in
    let var = Z3.Expr.mk_const_s context.ctx name sort in
      Hashtbl.add context.vars name var;
      var

(** Convert value to Z3 expression *)
let rec value_to_z3 context = function
  | VNumber n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | VSymbol s | VVar s -> get_var context s
  | VExpression e -> expr_to_z3 context e
  | VBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx

(** Convert expression to Z3 *)
and expr_to_z3 context = function
  | ENum n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | EVar v -> get_var context v
  | EBinOp (lhs, op, rhs) -> (
      let l = value_to_z3 context lhs in
      let r = value_to_z3 context rhs in
        match op with
        | "=" -> Z3.Boolean.mk_eq context.ctx l r
        | "!=" ->
            Z3.Boolean.mk_not context.ctx (Z3.Boolean.mk_eq context.ctx l r)
        | "<" -> Z3.Arithmetic.mk_lt context.ctx l r
        | ">" -> Z3.Arithmetic.mk_gt context.ctx l r
        | "<=" -> Z3.Arithmetic.mk_le context.ctx l r
        | ">=" -> Z3.Arithmetic.mk_ge context.ctx l r
        | "+" -> Z3.Arithmetic.mk_add context.ctx [ l; r ]
        | "-" -> Z3.Arithmetic.mk_sub context.ctx [ l; r ]
        | "*" -> Z3.Arithmetic.mk_mul context.ctx [ l; r ]
        | "/" -> Z3.Arithmetic.mk_div context.ctx l r
        | "&&" -> Z3.Boolean.mk_and context.ctx [ l; r ]
        | "||" -> Z3.Boolean.mk_or context.ctx [ l; r ]
        | "=>" -> Z3.Boolean.mk_implies context.ctx l r
        | _ -> failwith ("Unsupported operator: " ^ op)
    )
  | EUnOp ("!", rhs) ->
      let r = value_to_z3 context rhs in
        Z3.Boolean.mk_not context.ctx r
  | EUnOp ("~", rhs) ->
      let r = value_to_z3 context rhs in
        (* Bitwise not - simplified to arithmetic negation *)
        Z3.Arithmetic.mk_unary_minus context.ctx r
  | EOr clauses ->
      let clause_exprs =
        List.map
          (fun clause ->
            let exprs = List.map (expr_to_z3 context) clause in
              Z3.Boolean.mk_and context.ctx exprs
          )
          clauses
      in
        Z3.Boolean.mk_or context.ctx clause_exprs
  | _ -> failwith "Unsupported expression type"

(** Constraint type *)
type constraint_t = { op : string; value : Z.t option }

(** Solver type *)
type solver = {
  context : context;
  constraints : (string, constraint_t Uset.t) Hashtbl.t;
  expressions : expr list;
}

(** Create solver *)
let create exprs =
  let context = create_context () in
  let constraints = Hashtbl.create 32 in
    { context; constraints; expressions = exprs }

(** Check satisfiability *)
let check solver =
  let* _ = Lwt.return_unit in

  (* Convert expressions to Z3 *)
  let z3_exprs = List.map (expr_to_z3 solver.context) solver.expressions in

  (* Add to solver - Z3.Solver.add takes solver and list of exprs *)
  Z3.Solver.add solver.context.solver z3_exprs;

  (* Check *)
  let result = Z3.Solver.check solver.context.solver [] in

  match result with
  | Z3.Solver.SATISFIABLE -> Lwt.return_some true
  | Z3.Solver.UNSATISFIABLE -> Lwt.return_some false
  | Z3.Solver.UNKNOWN -> Lwt.return_none

(** Solve and get model *)
let solve solver =
  let* result = check solver in
    match result with
    | Some true -> (
        let model = Z3.Solver.get_model solver.context.solver in
          match model with
          | Some m ->
              let bindings = Hashtbl.create 16 in
                Hashtbl.iter
                  (fun name var ->
                    match Z3.Model.eval m var true with
                    | Some value -> (
                        let str = Z3.Expr.to_string value in
                          try
                            let n = Z.of_string str in
                              Hashtbl.add bindings name (VNumber n)
                          with _ -> Hashtbl.add bindings name (VVar str)
                      )
                    | None -> ()
                  )
                  solver.context.vars;
                Lwt.return_some bindings
          | None -> Lwt.return_none
      )
    | Some false -> Lwt.return_none
    | None -> Lwt.return_none

(** Get concrete value from solver result *)
let concrete_value bindings var =
  try Some (Hashtbl.find bindings var) with Not_found -> None

(** Simplify disjunction *)
let simplify_disjunction clauses =
  let* _ = Lwt.return_unit in
  (* Simplified version - just remove tautologies and contradictions *)
  let clauses' =
    List.filter
      (fun clause ->
        (not (List.exists Expr.is_contradiction clause))
        && not (List.for_all Expr.is_tautology clause)
      )
      clauses
  in

  if List.length clauses' = 0 then Lwt.return_none else Lwt.return_some clauses'
