(** solver.ml - Constraint solver using Z3 *)

open Expr
open Lwt.Syntax
open Printf
open Types
open Uset

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
  | VBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx

(** Convert expression to Z3 *)
and expr_to_z3 context = function
  | ENum n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | EVar v -> get_var context v
  | EBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx
  | ESymbol s -> get_var context s (* TODO this should fail *)
  | EBinOp (lhs, op, rhs) -> (
      let l = expr_to_z3 context lhs in
      let r = expr_to_z3 context rhs in
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
      let int_to_bool z3_expr =
        let zero = Z3.Arithmetic.Integer.mk_numeral_i context.ctx 0 in
          Z3.Boolean.mk_eq context.ctx z3_expr zero
      in
      let r = expr_to_z3 context rhs in
        if Z3.Boolean.is_bool r then Z3.Boolean.mk_not context.ctx r
        else
          (* Assume integer semantics: !x is true if x == 0, false otherwise *)
          let zero = Z3.Arithmetic.Integer.mk_numeral_i context.ctx 0 in
            Z3.Boolean.mk_eq context.ctx r zero
  | EUnOp ("~", rhs) ->
      let r = expr_to_z3 context rhs in
        Z3.Arithmetic.mk_unary_minus context.ctx r
  | EUnOp (op, _) -> failwith (sprintf "Unsupported unary operator %s" op)
  | EOr clauses ->
      List.map (expr_to_z3 context) clauses |> Z3.Boolean.mk_or context.ctx

(** Constraint type for range-based solving *)
type range = Z.t * Z.t (* (min, max) inclusive *)

(** Solver type *)
type solver = { context : context; expressions : expr list }

(** Create solver *)
let create exprs =
  let context = create_context () in
    { context; expressions = exprs }

(* TODO duplicate with is_tautology *)
(* TODO recursive evaluation over boolean expressions? *)

(** Evaluate constant expression if possible *)
let try_eval_constant = function
  | EBinOp (ENum a, "=", ENum b) -> Some (Z.equal a b)
  | EBinOp (ENum a, "!=", ENum b) -> Some (not (Z.equal a b))
  | EBinOp (ENum a, "<", ENum b) -> Some (Z.lt a b)
  | EBinOp (ENum a, ">", ENum b) -> Some (Z.gt a b)
  | EBinOp (ENum a, "<=", ENum b) -> Some (Z.leq a b)
  | EBinOp (ENum a, ">=", ENum b) -> Some (Z.geq a b)
  | _ -> None

(** Check satisfiability *)
let check solver =
  (* force into monadic context *)
  let* _ = Lwt.return_unit in

  (* Quick checks for contradictions and tautologies *)
  let has_contradiction =
    List.exists Expr.is_contradiction solver.expressions
  in
    if has_contradiction then Lwt.return_some false
    else if List.length solver.expressions = 0 then Lwt.return_some true
    else if List.for_all Expr.is_tautology solver.expressions then
      Lwt.return_some true
    else
      (* Quick constant check *)
      let all_constant_true =
        List.for_all
          (fun expr ->
            match try_eval_constant expr with
            | Some true -> true
            | Some false -> false
            | None -> true
          )
          solver.expressions
      in

      if not all_constant_true then Lwt.return_some false
      else
        (* Convert expressions to Z3 *)
        let z3_exprs =
          List.map (expr_to_z3 solver.context) solver.expressions
        in

        (* Add to solver *)
        try
          Z3.Solver.add solver.context.solver z3_exprs;
          (* Check *)
          let result = Z3.Solver.check solver.context.solver [] in

          match result with
          | Z3.Solver.SATISFIABLE -> Lwt.return_some true
          | Z3.Solver.UNSATISFIABLE -> Lwt.return_some false
          | Z3.Solver.UNKNOWN -> Lwt.return_none
        with e ->
          Logs.err (fun m ->
              m "Error adding expressions to Z3 solver: %s\n %s"
                (Printexc.to_string e)
                (String.concat "\n" (List.map Expr.to_string solver.expressions))
          );
          failwith "Z3 solver error"

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

(** Simplify disjunction using basic heuristics *)
let simplify_disjunction clauses =
  let* _ = Lwt.return_unit in

  (* Remove clauses containing contradictions *)
  let filtered_clauses =
    List.filter
      (fun clause -> not (List.exists Expr.is_contradiction clause))
      clauses
  in

  (* Remove tautological literals from each clause *)
  let filtered_clauses2 =
    List.map
      (fun clause -> List.filter (fun e -> not (Expr.is_tautology e)) clause)
      filtered_clauses
  in

  (* Remove empty clauses (all literals were tautologies) unless it means the whole thing is a tautology *)
  let has_empty_clause =
    List.exists (fun c -> List.length c = 0) filtered_clauses2
  in

  if has_empty_clause then
    (* Empty clause means that clause is a tautology, so entire disjunction is tautology *)
    Lwt.return_some [ [] ]
  else
    let non_empty =
      List.filter (fun c -> List.length c > 0) filtered_clauses2
    in

    (* Check if result is empty (unsatisfiable) *)
    if List.length non_empty = 0 then Lwt.return_none
    else Lwt.return_some non_empty

(** Get all symbols from a list of expressions *)
let get_all_symbols exprs =
  let symbols = List.flatten (List.map Expr.get_symbols exprs) in
  let uset = USet.of_list symbols in
    USet.values uset

(** Solve with Z3 and return ranges or concrete values *)
let solve_with_ranges solver =
  let* result = solve solver in
    match result with
    | None -> Lwt.return_none
    | Some bindings ->
        (* Convert bindings to range format *)
        let ranges = Hashtbl.create 16 in

        (* Get all symbols that appear in expressions *)
        let all_symbols = get_all_symbols solver.expressions in

        (* For each symbol, determine its range *)
        List.iter
          (fun symbol ->
            match concrete_value bindings symbol with
            | Some (VNumber n) ->
                (* Try to determine if this is the only possible value *)
                (* by checking if symbol != n is unsatisfiable *)
                let test_expr = Expr.binop (EVar symbol) "!=" (ENum n) in
                let test_solver = create (test_expr :: solver.expressions) in
                  (* For now, just return the single value as range *)
                  Hashtbl.add ranges symbol [ (n, n) ]
            | _ ->
                (* Unknown range - use unbounded *)
                let min_val = Z.of_int min_int in
                let max_val = Z.of_int max_int in
                  Hashtbl.add ranges symbol [ (min_val, max_val) ]
          )
          all_symbols;

        Lwt.return_some ranges

(** Check if all expressions are flat (for optimization) *)
let all_flat exprs = List.for_all Expr.is_flat exprs

(** Advanced solve that checks multiple strategies *)
let solve_advanced solver =
  (* First try: quick constant evaluation *)
  let has_contradiction =
    List.exists Expr.is_contradiction solver.expressions
  in
    if has_contradiction then Lwt.return_some false
    else
      (* Second try: all tautologies *)
      let all_taut = List.for_all Expr.is_tautology solver.expressions in
        if all_taut then Lwt.return_some true
        else
          (* Use Z3 for complex cases *)
          check solver

(** Create a solver and check satisfiability in one go *)
let quick_check exprs =
  let solver = create exprs in
    check solver

let quick_check_cache = ConjunctionCache.create 256

let quick_check_cached exprs =
  let landmark = Landmark.register "quick_check_cached" in
    Landmark.enter landmark;
    (* TODO exprs should already be normalized *)
    let exprs = USet.of_list exprs |> USet.values |> List.sort Expr.compare in
      match ConjunctionCache.find_opt quick_check_cache exprs with
      | Some result ->
          Landmark.exit landmark;
          Lwt.return result
      | None ->
          let* result = quick_check exprs in
            ConjunctionCache.add quick_check_cache exprs result;
            Landmark.exit landmark;
            Lwt.return result

(** Create a solver and get a model in one go *)
let quick_solve exprs =
  let solver = create exprs in
    solve solver

(** Check if a set of constraints implies another expression *)
let implies constraints conclusion =
  let negated = Expr.inverse conclusion in
  let solver = create (constraints @ [ negated ]) in
    let* result = check solver in
      match result with
      | Some false ->
          Lwt.return_true (* Negation is unsat, so implication holds *)
      | _ -> Lwt.return_false

(** Reset solver (create fresh context) *)
let reset solver = { solver with context = create_context () }

(** Push solver state (for backtracking) *)
let push solver =
  Z3.Solver.push solver.context.solver;
  solver

(** Pop solver state (for backtracking) *)
let pop solver =
  Z3.Solver.pop solver.context.solver 1;
  solver

(** Add assertions to existing solver *)
let add_assertions solver exprs =
  let z3_exprs = List.map (expr_to_z3 solver.context) exprs in
    Z3.Solver.add solver.context.solver z3_exprs;
    solver

(** Get statistics from solver *)
let get_statistics solver =
  Z3.Statistics.to_string (Z3.Solver.get_statistics solver.context.solver)

(** Convert Z3 model to readable string *)
let model_to_string bindings =
  let items =
    Hashtbl.fold
      (fun name value acc -> (name, Value.to_string value) :: acc)
      bindings []
  in
  let sorted = List.sort (fun (a, _) (b, _) -> String.compare a b) items in
    String.concat ", "
      (List.map
         (fun (name, value) -> Printf.sprintf "%s = %s" name value)
         sorted
      )

(** Check if expression list is satisfiable (simplified API) *)
let is_sat exprs =
  let* result = quick_check exprs in
    match result with
    | Some true -> Lwt.return_true
    | _ -> Lwt.return_false

(** Check if expression list is satisfiable (simplified API) *)
let is_sat_cached exprs =
  let* result = quick_check_cached exprs in
    match result with
    | Some true -> Lwt.return_true
    | _ -> Lwt.return_false

(** Check if expression list is unsatisfiable (simplified API) *)
let is_unsat exprs =
  let* result = quick_check exprs in
    match result with
    | Some false -> Lwt.return_true
    | _ -> Lwt.return_false

(** Check if expression list is unsatisfiable (simplified API) *)
let is_unsat_cached exprs =
  let* result = quick_check_cached exprs in
    match result with
    | Some false -> Lwt.return_true
    | _ -> Lwt.return_false

(** Solve and extract concrete values for specific variables *)
let solve_for_vars solver var_names =
  let* model_opt = solve solver in
    match model_opt with
    | None -> Lwt.return_none
    | Some bindings ->
        let results = Hashtbl.create (List.length var_names) in
          List.iter
            (fun var_name ->
              match concrete_value bindings var_name with
              | Some value -> Hashtbl.add results var_name value
              | None -> ()
            )
            var_names;
          Lwt.return_some results

(** Semantic equality checking *)

(** Check if two expressions are semantically equal (always equal under all
    interpretations) *)
let exeq ?(state = []) a b =
  if Expr.equal a b then Lwt.return_true
  else
    (* If state && (a != b) is unsatisfiable, a = b is true given state *)
    let neq_expr = Expr.binop a "!=" b in
      let* result =
        quick_check_cached (neq_expr :: state |> List.sort Expr.compare)
      in
        match result with
        | Some false -> Lwt.return_true
        | _ -> Lwt.return_false

(** Check if two expressions are potentially equal (equality is satisfiable) *)
let expoteq ?(state = []) a b =
  let landmark = Landmark.register "expoteq" in
    Landmark.enter landmark;
    if Expr.equal a b then (
      Landmark.exit landmark;
      Lwt.return_true
    )
    else
      (* Check if a = b is satisfiable *)
      let eq_expr = Expr.binop a "=" b in
        let* result =
          quick_check_cached (eq_expr :: state |> List.sort Expr.compare)
        in
          match result with
          | Some true ->
              Landmark.exit landmark;
              Lwt.return_true (* a = b is sat, so they could be equal *)
          | _ ->
              Landmark.exit landmark;
              Lwt.return_false

(** Semantic equality module with state management *)
module Semeq = struct
  (** Mutable state for semantic equality checking *)
  type state = { mutable context : expr list }

  (** Create new state *)
  let create_state () = { context = [] }

  (** Set global state *)
  let set_state state context = state.context <- context

  (** Check semantic equality with current state *)
  let exeq state a b = exeq ~state:state.context a b

  (** Check potential equality with current state *)
  let expoteq state a b = expoteq ~state:state.context a b

  (** Check potential equality of values *)
  let expoteq_value state (v1 : value_type) (v2 : value_type) =
    if Value.equal v1 v2 then Lwt.return true
    else
      (* For any two values, check if they could be equal by solving v1 = v2 *)
      let eq_expr = Expr.binop (Expr.of_value v1) "=" (Expr.of_value v2) in
      let solver = create (eq_expr :: state.context) in
        let* result = check solver in
          match result with
          | Some true -> Lwt.return true
          | _ -> Lwt.return false
end

(** Cache for semantic equality results *)
module SemeqCache = struct
  type cache = {
    eq_cache : (string, bool) Hashtbl.t;
    poteq_cache : (string, bool) Hashtbl.t;
  }

  let create () =
    { eq_cache = Hashtbl.create 256; poteq_cache = Hashtbl.create 256 }

  let key_of_exprs a b =
    Printf.sprintf "%s|%s" (Expr.to_string a) (Expr.to_string b)

  (** Cached semantic equality check *)
  let exeq_cached cache ?(state = []) a b =
    let key = key_of_exprs a b in
      match Hashtbl.find_opt cache.eq_cache key with
      | Some result -> Lwt.return result
      | None ->
          let* result = exeq ~state a b in
            Hashtbl.add cache.eq_cache key result;
            Lwt.return result

  (** Cached potential equality check *)
  let expoteq_cached cache ?(state = []) a b =
    let key = key_of_exprs a b in
      match Hashtbl.find_opt cache.poteq_cache key with
      | Some result -> Lwt.return result
      | None ->
          let* result = expoteq ~state a b in
            Hashtbl.add cache.poteq_cache key result;
            Lwt.return result

  (** Clear cache *)
  let clear cache =
    Hashtbl.clear cache.eq_cache;
    Hashtbl.clear cache.poteq_cache
end
