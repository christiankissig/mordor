(** {1 Constraint Solver Implementation}

    This module implements a constraint solver using the Z3 SMT solver. It
    provides functionality for satisfiability checking, model extraction, and
    semantic equality analysis.

    The implementation is organized into several logical sections:
    - Type definitions and context management
    - Z3 conversion functions
    - Solver creation and management
    - Satisfiability checking (with caching)
    - Model extraction and analysis
    - Semantic equality checking

    @author Your Name
    @version 1.0 *)

open Expr
open Lwt.Syntax
open Printf
open Types
open Uset

(** {1 Type Definitions} *)

(** Solver context encapsulating Z3 state.

    Contains the Z3 context, solver instance, and variable mappings. *)
type context = {
  ctx : Z3.context;  (** Z3 context for all operations *)
  solver : Z3.Solver.solver;  (** Z3 solver instance *)
  vars : (string, Z3.Expr.expr) Hashtbl.t;
      (** Variable name to Z3 expression mapping *)
}

(** Range type for interval-based solving. *)
type range = Z.t * Z.t (* (min, max) inclusive *)

(** Solver state with context and constraints. *)
type solver = {
  context : context;  (** The Z3 context *)
  expressions : expr list;  (** Constraint expressions to solve *)
}

(** {1 Context Management}

    Functions for creating and managing Z3 solver contexts. *)

(** Create a new solver context.

    Initializes a fresh Z3 context and solver with an empty variable table.

    @return A new context ready for use *)
let create_context () =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_solver ctx None in
  let vars = Hashtbl.create 32 in
    { ctx; solver; vars }

(** Get or create a Z3 variable by name.

    If the variable exists, returns it. Otherwise creates a new integer-typed Z3
    constant and registers it in the context's variable table.

    @param context The solver context
    @param name Variable name
    @return Z3 expression for this variable *)
let get_var context name =
  try Hashtbl.find context.vars name
  with Not_found ->
    let sort = Z3.Arithmetic.Integer.mk_sort context.ctx in
    let var = Z3.Expr.mk_const_s context.ctx name sort in
      Hashtbl.add context.vars name var;
      var

(** {1 Z3 Conversion Functions}

    Functions for converting internal representations to Z3 expressions. *)

(** Convert a bitvector-compatible expression to bitvector type.

    Handles conversion of booleans and integers to bitvectors of specified
    width.

    @param context The solver context
    @param expr Z3 expression to convert
    @param bitwidth Target bitvector width
    @return Z3 bitvector expression *)
and to_bitvec context expr bitwidth =
  if Z3.BitVector.is_bv expr then expr
  else if Z3.Boolean.is_bool expr then
    (* Convert boolean to bitvector: true -> 1, false -> 0 *)
    let zero_bv = Z3.BitVector.mk_numeral context.ctx "0" bitwidth in
    let one_bv = Z3.BitVector.mk_numeral context.ctx "1" bitwidth in
      Z3.Boolean.mk_ite context.ctx expr one_bv zero_bv
  else
    (* Integer to bitvector *)
    Z3.Arithmetic.Integer.mk_int2bv context.ctx bitwidth expr

(** Convert a value to Z3 expression.

    @param context The solver context
    @param value The value to convert
    @return Z3 expression representation *)
let rec value_to_z3 context value =
  match value with
  | VNumber n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | VSymbol s | VVar s -> get_var context s
  | VBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx

(** Convert an expression to Z3 representation.

    Recursively converts expression trees, handling:
    - Literals (numbers, booleans, variables, symbols)
    - Binary operations (arithmetic, comparison, logical, bitwise)
    - Unary operations (negation, logical not)
    - Disjunctions

    Special handling is provided for mixed integer/bitvector operations.

    @param context The solver context
    @param expr The expression to convert
    @return Z3 expression *)
and expr_to_z3 context expr =
  match expr with
  | ENum n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | EVar v -> get_var context v
  | EBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx
  | ESymbol s -> get_var context s
  | EBinOp (lhs, op, rhs) -> (
      let l = expr_to_z3 context lhs in
      let r = expr_to_z3 context rhs in
        match op with
        (* Comparison operators *)
        | "=" ->
            (* Handle mixed bitvector/integer comparisons *)
            if Z3.BitVector.is_bv l && not (Z3.BitVector.is_bv r) then
              let bitwidth = Z3.BitVector.get_size (Z3.Expr.get_sort l) in
              let r_bv = to_bitvec context r bitwidth in
                Z3.Boolean.mk_eq context.ctx l r_bv
            else if Z3.BitVector.is_bv r && not (Z3.BitVector.is_bv l) then
              let bitwidth = Z3.BitVector.get_size (Z3.Expr.get_sort r) in
              let l_bv = to_bitvec context l bitwidth in
                Z3.Boolean.mk_eq context.ctx l_bv r
            else Z3.Boolean.mk_eq context.ctx l r
        | "!=" ->
            Z3.Boolean.mk_not context.ctx (Z3.Boolean.mk_eq context.ctx l r)
        | "<" -> Z3.Arithmetic.mk_lt context.ctx l r
        | ">" -> Z3.Arithmetic.mk_gt context.ctx l r
        | "<=" -> Z3.Arithmetic.mk_le context.ctx l r
        | ">=" -> Z3.Arithmetic.mk_ge context.ctx l r
        (* Arithmetic operators *)
        | "+" -> Z3.Arithmetic.mk_add context.ctx [ l; r ]
        | "-" -> Z3.Arithmetic.mk_sub context.ctx [ l; r ]
        | "*" -> Z3.Arithmetic.mk_mul context.ctx [ l; r ]
        | "/" -> Z3.Arithmetic.mk_div context.ctx l r
        (* Bitwise operators (via bitvector conversion) *)
        | "&" ->
            let bitwidth = 64 in
            let l_bv = to_bitvec context l bitwidth in
            let r_bv = to_bitvec context r bitwidth in
            let result_bv = Z3.BitVector.mk_and context.ctx l_bv r_bv in
              (* Convert back to integer *)
              Z3.BitVector.mk_bv2int context.ctx result_bv false
        | "|" ->
            let bitwidth = 64 in
            let l_bv = to_bitvec context l bitwidth in
            let r_bv = to_bitvec context r bitwidth in
            let result_bv = Z3.BitVector.mk_or context.ctx l_bv r_bv in
              (* Convert back to integer *)
              Z3.BitVector.mk_bv2int context.ctx result_bv false
        (* Logical operators *)
        | "&&" -> Z3.Boolean.mk_and context.ctx [ l; r ]
        | "||" -> Z3.Boolean.mk_or context.ctx [ l; r ]
        | "=>" -> Z3.Boolean.mk_implies context.ctx l r
        | _ -> failwith ("Unsupported operator: " ^ op)
    )
  | EUnOp ("!", rhs) ->
      let r = expr_to_z3 context rhs in
        if Z3.Boolean.is_bool r then Z3.Boolean.mk_not context.ctx r
        else
          (* Integer semantics: !x is true iff x = 0 *)
          let zero = Z3.Arithmetic.Integer.mk_numeral_i context.ctx 0 in
            Z3.Boolean.mk_eq context.ctx r zero
  | EUnOp ("~", rhs) ->
      let r = expr_to_z3 context rhs in
        Z3.Arithmetic.mk_unary_minus context.ctx r
  | EUnOp (op, _) -> failwith (sprintf "Unsupported unary operator %s" op)
  | EOr clauses ->
      List.map (expr_to_z3 context) clauses |> Z3.Boolean.mk_or context.ctx

(** {1 Solver Creation and Management}

    Functions for creating and modifying solver instances. *)

(** Create a new solver from constraint expressions.

    @param exprs List of constraint expressions
    @return Fresh solver with these constraints *)
let create exprs =
  let context = create_context () in
    { context; expressions = exprs }

(** Reset solver with fresh context.

    Discards Z3 state while keeping the same expressions.

    @param solver The solver to reset
    @return New solver with fresh context *)
let reset solver = { solver with context = create_context () }

(** Push a new scope for backtracking.

    @param solver The solver to push
    @return The same solver (mutates state) *)
let push solver =
  Z3.Solver.push solver.context.solver;
  solver

(** Pop the most recent scope.

    @param solver The solver to pop
    @return The same solver (mutates state) *)
let pop solver =
  Z3.Solver.pop solver.context.solver 1;
  solver

(** Add assertions to existing solver.

    @param solver The solver to extend
    @param exprs New expressions to add
    @return Modified solver *)
let add_assertions solver exprs =
  let z3_exprs = List.map (expr_to_z3 solver.context) exprs in
    Z3.Solver.add solver.context.solver z3_exprs;
    solver

(** {1 Satisfiability Checking}

    Core satisfiability checking with various optimization strategies. *)

(** Evaluate constant boolean expressions if possible.

    Quick optimization for trivial constant comparisons.

    @param expr The expression to evaluate
    @return [Some true], [Some false], or [None] if not constant *)
let try_eval_constant = function
  | EBinOp (ENum a, "=", ENum b) -> Some (Z.equal a b)
  | EBinOp (ENum a, "!=", ENum b) -> Some (not (Z.equal a b))
  | EBinOp (ENum a, "<", ENum b) -> Some (Z.lt a b)
  | EBinOp (ENum a, ">", ENum b) -> Some (Z.gt a b)
  | EBinOp (ENum a, "<=", ENum b) -> Some (Z.leq a b)
  | EBinOp (ENum a, ">=", ENum b) -> Some (Z.geq a b)
  | _ -> None

(** Check satisfiability of solver's constraints.

    Performs several optimizations before invoking Z3: 1. Quick check for
    obvious contradictions 2. Quick check for tautologies 3. Constant expression
    evaluation 4. Full Z3 solving if needed

    @param solver The solver to check
    @return [Some true] if SAT, [Some false] if UNSAT, [None] if unknown *)
let check solver =
  (* Enter monadic context *)
  let* _ = Lwt.return_unit in

  (* Quick check: any contradictions? *)
  let has_contradiction =
    List.exists Expr.is_contradiction solver.expressions
  in
    if has_contradiction then Lwt.return_some false
    else if List.length solver.expressions = 0 then Lwt.return_some true
    else if List.for_all Expr.is_tautology solver.expressions then
      Lwt.return_some true
    else
      (* Try constant evaluation *)
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
        (* Convert to Z3 and solve *)
        let z3_exprs =
          List.map (expr_to_z3 solver.context) solver.expressions
        in

        try
          Z3.Solver.add solver.context.solver z3_exprs;
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

(** Quick satisfiability check (uncached).

    Creates a solver and immediately checks satisfiability.

    @param exprs Constraint expressions
    @return SAT/UNSAT/UNKNOWN result *)
let quick_check exprs =
  let solver = create exprs in
    check solver

(** Cache for conjunction satisfiability results. *)
let quick_check_cache = ConjunctionCache.create 256

(** Quick satisfiability check (cached).

    Like {!quick_check} but caches results based on normalized constraint sets.

    @param exprs Constraint expressions
    @return SAT/UNSAT/UNKNOWN result *)
let quick_check_cached exprs =
  let landmark = Landmark.register "quick_check_cached" in
    Landmark.enter landmark;
    (* Normalize expressions for consistent cache keys *)
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

(** Simplified satisfiability check.

    @param exprs Constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
let is_sat exprs =
  let* result = quick_check exprs in
    match result with
    | Some true -> Lwt.return_true
    | _ -> Lwt.return_false

(** Simplified satisfiability check (cached).

    @param exprs Constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
let is_sat_cached exprs =
  let* result = quick_check_cached exprs in
    match result with
    | Some true -> Lwt.return_true
    | _ -> Lwt.return_false

(** Simplified unsatisfiability check.

    @param exprs Constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
let is_unsat exprs =
  let* result = quick_check exprs in
    match result with
    | Some false -> Lwt.return_true
    | _ -> Lwt.return_false

(** Simplified unsatisfiability check (cached).

    @param exprs Constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
let is_unsat_cached exprs =
  let* result = quick_check_cached exprs in
    match result with
    | Some false -> Lwt.return_true
    | _ -> Lwt.return_false

(** Check if constraints imply a conclusion.

    Tests [constraints ⊢ conclusion] by checking if [constraints ∧ ¬conclusion]
    is unsatisfiable.

    @param constraints Antecedent expressions
    @param conclusion Consequent expression
    @return [true] if implication holds *)
let implies constraints conclusion =
  let negated = Expr.inverse conclusion in
  let solver = create (constraints @ [ negated ]) in
    let* result = check solver in
      match result with
      | Some false ->
          Lwt.return_true (* Negation is UNSAT => implication holds *)
      | _ -> Lwt.return_false

(** Advanced solve using multiple strategies.

    Tries constant evaluation, tautology checking, then Z3.

    @param solver The solver to check
    @return SAT/UNSAT/UNKNOWN result *)
let solve_advanced solver =
  (* Check for contradictions *)
  let has_contradiction =
    List.exists Expr.is_contradiction solver.expressions
  in
    if has_contradiction then Lwt.return_some false
    else
      (* Check if all tautologies *)
      let all_taut = List.for_all Expr.is_tautology solver.expressions in
        if all_taut then Lwt.return_some true
        else
          (* Use Z3 for complex cases *)
          check solver

(** {1 Model Extraction}

    Functions for extracting satisfying assignments and concrete values. *)

(** Solve and extract a satisfying model.

    If satisfiable, returns variable bindings from the model.

    @param solver The solver to solve
    @return [Some bindings] if SAT, [None] if UNSAT/UNKNOWN *)
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

(** Quick solve and model extraction.

    @param exprs Constraint expressions
    @return [Some bindings] if SAT, [None] otherwise *)
let quick_solve exprs =
  let solver = create exprs in
    solve solver

(** Get concrete value from model bindings.

    @param bindings Model from {!solve}
    @param var Variable name
    @return [Some value] if bound, [None] otherwise *)
let concrete_value bindings var =
  try Some (Hashtbl.find bindings var) with Not_found -> None

(** Solve and extract values for specific variables.

    More efficient than {!solve} when only interested in a subset of variables.

    @param solver The solver to solve
    @param var_names List of variable names to extract
    @return [Some bindings] for requested vars if SAT, [None] otherwise *)
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

(** Convert model to human-readable string.

    Formats as "var1 = value1, var2 = value2, ..." with sorted variables.

    @param bindings Model from {!solve}
    @return Formatted string representation *)
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

(** {1 Expression Analysis}

    Functions for analyzing and simplifying expressions. *)

(** Extract all symbol names from expressions.

    @param exprs The expressions to analyze
    @return List of unique symbol names *)
let get_all_symbols exprs =
  let symbols = List.flatten (List.map Expr.get_symbols exprs) in
  let uset = USet.of_list symbols in
    USet.values uset

(** Check if all expressions are flat.

    A flat expression has no nested subexpressions (all operands are literals or
    variables).

    @param exprs The expressions to check
    @return [true] if all flat, [false] otherwise *)
let all_flat exprs = List.for_all Expr.is_flat exprs

(** Simplify disjunctive normal form expression.

    Applies heuristics to simplify (clause1 OR clause2 OR ...):
    - Removes contradictory clauses
    - Removes tautological literals
    - Handles empty clauses

    @param clauses List of clauses (each is a conjunction)
    @return [Some simplified] if SAT, [None] if UNSAT *)
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

  (* Check for empty clauses (all literals were tautologies) *)
  let has_empty_clause =
    List.exists (fun c -> List.length c = 0) filtered_clauses2
  in

  if has_empty_clause then
    (* Empty clause => that clause is a tautology => entire disjunction is tautology *)
    Lwt.return_some [ [] ]
  else
    let non_empty =
      List.filter (fun c -> List.length c > 0) filtered_clauses2
    in

    (* Empty result means unsatisfiable *)
    if List.length non_empty = 0 then Lwt.return_none
    else Lwt.return_some non_empty

(** Solve with Z3 and return ranges for each variable.

    Attempts to determine possible value ranges rather than just concrete
    values.

    @param solver The solver to solve
    @return [Some ranges] mapping vars to range lists if SAT, [None] if UNSAT *)
let solve_with_ranges solver =
  let* result = solve solver in
    match result with
    | None -> Lwt.return_none
    | Some bindings ->
        let ranges = Hashtbl.create 16 in
        let all_symbols = get_all_symbols solver.expressions in

        (* For each symbol, determine its range *)
        List.iter
          (fun symbol ->
            match concrete_value bindings symbol with
            | Some (VNumber n) ->
                (* Return single value as range *)
                (* TODO: Check if other values are possible *)
                Hashtbl.add ranges symbol [ (n, n) ]
            | _ ->
                (* Unknown range - use unbounded *)
                let min_val = Z.of_int min_int in
                let max_val = Z.of_int max_int in
                  Hashtbl.add ranges symbol [ (min_val, max_val) ]
          )
          all_symbols;

        Lwt.return_some ranges

(** {1 Solver Introspection} *)

(** Get statistics from Z3 solver.

    Returns performance information like decisions, conflicts, propagations.

    @param solver The solver to inspect
    @return Formatted statistics string *)
let get_statistics solver =
  Z3.Statistics.to_string (Z3.Solver.get_statistics solver.context.solver)

(** {1 Semantic Equality}

    Functions for checking semantic and potential equality of expressions. *)

(** Check if two expressions are semantically equal.

    Returns [true] if [a] and [b] are logically equivalent given state
    constraints.

    Implementation: checks if [state ∧ (a ≠ b)] is unsatisfiable.

    @param state Optional additional constraints (default: [])
    @param a First expression
    @param b Second expression
    @return [true] if semantically equal *)
let exeq ?(state = []) a b =
  if Expr.equal a b then Lwt.return_true
  else
    (* Check if state && (a != b) is UNSAT *)
    let neq_expr = Expr.binop a "!=" b in
      let* result =
        quick_check_cached (neq_expr :: state |> List.sort Expr.compare)
      in
        match result with
        | Some false -> Lwt.return_true
        | _ -> Lwt.return_false

(** Check if two expressions could potentially be equal.

    Returns [true] if there exists an assignment (consistent with state) where
    [a = b].

    Implementation: checks if [state ∧ (a = b)] is satisfiable.

    @param state Optional additional constraints (default: [])
    @param a First expression
    @param b Second expression
    @return [true] if potentially equal *)
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
              Lwt.return_true
          | _ ->
              Landmark.exit landmark;
              Lwt.return_false

(** {2 Semantic Equality with State Management} *)

module Semeq = struct
  (** Mutable state for semantic equality checking.

      Stores a context of constraint expressions applied to all checks. *)
  type state = { mutable context : expr list }

  (** Create a new empty state.

      @return Fresh state with empty context *)
  let create_state () = { context = [] }

  (** Update the constraint context.

      @param state The state to modify
      @param context New constraint expressions *)
  let set_state state context = state.context <- context

  (** Check semantic equality using state's context.

      @param state State providing constraints
      @param a First expression
      @param b Second expression
      @return [true] if semantically equal *)
  let exeq state a b = exeq ~state:state.context a b

  (** Check potential equality using state's context.

      @param state State providing constraints
      @param a First expression
      @param b Second expression
      @return [true] if potentially equal *)
  let expoteq state a b = expoteq ~state:state.context a b

  (** Check potential equality of two values.

      Converts values to expressions and checks satisfiability of equality.

      @param state State providing constraints
      @param v1 First value
      @param v2 Second value
      @return [true] if values could be equal *)
  let expoteq_value state (v1 : value_type) (v2 : value_type) =
    if Value.equal v1 v2 then Lwt.return true
    else
      let eq_expr = Expr.binop (Expr.of_value v1) "=" (Expr.of_value v2) in
      let solver = create (eq_expr :: state.context) in
        let* result = check solver in
          match result with
          | Some true -> Lwt.return true
          | _ -> Lwt.return false
end

(** {2 Cached Semantic Equality} *)

module SemeqCache = struct
  (** Cache type storing equality check results. *)
  type cache = {
    eq_cache : (string, bool) Hashtbl.t;  (** Semantic equality cache *)
    poteq_cache : (string, bool) Hashtbl.t;  (** Potential equality cache *)
  }

  (** Create a new empty cache.

      @return Fresh cache *)
  let create () =
    { eq_cache = Hashtbl.create 256; poteq_cache = Hashtbl.create 256 }

  (** Generate cache key from two expressions.

      @param a First expression
      @param b Second expression
      @return Cache key string *)
  let key_of_exprs a b =
    Printf.sprintf "%s|%s" (Expr.to_string a) (Expr.to_string b)

  (** Cached semantic equality check.

      Looks up result in cache; computes and stores if not found.

      @param cache The cache to use
      @param state Optional additional constraints (default: [])
      @param a First expression
      @param b Second expression
      @return [true] if semantically equal *)
  let exeq_cached cache ?(state = []) a b =
    let key = key_of_exprs a b in
      match Hashtbl.find_opt cache.eq_cache key with
      | Some result -> Lwt.return result
      | None ->
          let* result = exeq ~state a b in
            Hashtbl.add cache.eq_cache key result;
            Lwt.return result

  (** Cached potential equality check.

      Looks up result in cache; computes and stores if not found.

      @param cache The cache to use
      @param state Optional additional constraints (default: [])
      @param a First expression
      @param b Second expression
      @return [true] if potentially equal *)
  let expoteq_cached cache ?(state = []) a b =
    let key = key_of_exprs a b in
      match Hashtbl.find_opt cache.poteq_cache key with
      | Some result -> Lwt.return result
      | None ->
          let* result = expoteq ~state a b in
            Hashtbl.add cache.poteq_cache key result;
            Lwt.return result

  (** Clear all cached results.

      @param cache The cache to clear *)
  let clear cache =
    Hashtbl.clear cache.eq_cache;
    Hashtbl.clear cache.poteq_cache
end
