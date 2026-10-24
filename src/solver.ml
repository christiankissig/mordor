(** {1 Constraint Solver Implementation}

    This module implements a constraint solver on top of the platform's SMT
    backend ({!Smt_backend}; Z3 natively). It provides functionality for
    satisfiability checking, model extraction, and semantic equality analysis.

    The implementation is organized into several logical sections:
    - Type definitions
    - Solver creation and management
    - Satisfiability checking (with caching)
    - Model extraction and analysis
    - Semantic equality checking *)

open Expr
open Types
open Uset

(** {1 Type Definitions} *)

(** Solver state: the platform's solver ({!Smt_backend}), and the constraint
    expressions {!check} asks it about. *)
type solver = {
  context : Smt_backend.solver;  (** The backend's solver *)
  expressions : expr list;  (** Constraint expressions to solve *)
}

(** {1 Solver Creation and Management}

    Functions for creating and modifying solver instances. *)

(** Create a new solver from constraint expressions.

    @param exprs List of constraint expressions
    @return Fresh solver with these constraints *)
let create exprs =
  let context = Smt_backend.create () in
    { context; expressions = exprs }

(** Reset solver with fresh context.

    Discards the backend's state while keeping the same expressions.

    @param solver The solver to reset
    @return New solver with fresh context *)
let reset solver = { solver with context = Smt_backend.create () }

(** Push a new scope for backtracking.

    @param solver The solver to push
    @return The same solver (mutates state) *)
let push solver =
  Smt_backend.push solver.context;
  solver

(** Pop the most recent scope.

    @param solver The solver to pop
    @return The same solver (mutates state) *)
let pop solver =
  Smt_backend.pop solver.context;
  solver

(** Add assertions to existing solver.

    @param solver The solver to extend
    @param exprs New expressions to add
    @return Modified solver *)
let add_assertions solver exprs =
  Smt_backend.add solver.context exprs;
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
let trivially exprs =
  (* Quick check: any contradictions? *)
  let has_contradiction = List.exists Expr.is_contradiction exprs in
    if has_contradiction then Some false
    else if List.length exprs = 0 then Some true
    else if List.for_all Expr.is_tautology exprs then Some true
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
          exprs
      in
        if not all_constant_true then Some false else None

let check_asserted solver = Smt_backend.check solver.context

let check solver =
  match trivially solver.expressions with
  | Some answer -> Some answer
  | None -> (
      (* Translating raises on an unsupported operator, before the solver is
         asked, as it did when the translation lived here. *)
      Smt_backend.add solver.context solver.expressions;
      try check_asserted solver
      with e ->
        Logs_safe.err (fun m ->
            m "Error checking expressions with the SMT solver: %s\n %s"
              (Printexc.to_string e)
              (String.concat "\n" (List.map Expr.to_string solver.expressions))
        );
        failwith "SMT solver error"
    )

(** {1 Scoped Solving} *)

(** This domain's long-lived solver: a Z3 solver that queries are pushed onto
    and popped off, and the variables they have named. *)
let scoped_solver_key = Domain.DLS.new_key (fun () -> create [])

let fresh_solvers = ref (Option.is_some (Sys.getenv_opt "MORDOR_FRESH_SOLVER"))

let scoped f =
  let solver = Domain.DLS.get scoped_solver_key in
    ignore (push solver);
    Fun.protect ~finally:(fun () -> ignore (pop solver)) (fun () -> f solver)

(** Quick satisfiability check (uncached).

    Checks [exprs] in a scope of this domain's long-lived solver, or, with
    {!fresh_solvers}, in a fresh one. Building a Z3 solver costs about as much
    as the queries asked here take to solve, and a scope gives the same answers:
    S7 (#19) replayed 1.13 million queries from real runs both ways.

    @param exprs Constraint expressions
    @return SAT/UNSAT/UNKNOWN result *)
let quick_check exprs =
  if !fresh_solvers then check (create exprs)
  else scoped (fun solver -> check { solver with expressions = exprs })

(** Cache for conjunction satisfiability results, in two generations.

    Unbounded, it grew about 20MB a second on rcu-2: a read-from enumeration
    there asks hundreds of thousands of conjunctions, most of them once, and an
    entry holds its conjunction, several KB. New entries go to the young
    generation; when that is full it becomes the old one and the old one is
    dropped, and an entry hit in the old one moves back to the young. So what is
    asked again stays, and at most twice {!generation_size} entries are held. *)
module GenerationalCache = struct
  type t = {
    mutable young : bool option ConjunctionCache.t;
    mutable old : bool option ConjunctionCache.t;
  }

  let generation_size = 1 lsl 16

  let create () =
    { young = ConjunctionCache.create 256; old = ConjunctionCache.create 1 }

  let add cache exprs result =
    if ConjunctionCache.length cache.young >= generation_size then (
      cache.old <- cache.young;
      cache.young <- ConjunctionCache.create 256
    );
    ConjunctionCache.replace cache.young exprs result

  let find_opt cache exprs =
    match ConjunctionCache.find_opt cache.young exprs with
    | Some _ as hit -> hit
    | None ->
        let hit = ConjunctionCache.find_opt cache.old exprs in
          Option.iter (add cache exprs) hit;
          hit
end

let quick_check_cache = GenerationalCache.create ()
let cache_mutex = Mutex.create ()

(** S7 (#19): with [MORDOR_S7_TRACE] set to a path, every query to
    {!quick_check_cached} is written there, in the order asked: where it was
    asked from, whether the cache answered it, and the conjunction as the caller
    built it, before sorting. [Marshal]led, one record per query. *)
module S7 = struct
  type record = { site : string; hit : bool; exprs : expr list }

  let out =
    Option.map
      (fun path ->
        let oc = open_out_bin path in
          at_exit (fun () -> close_out oc);
          oc
      )
      (Sys.getenv_opt "MORDOR_S7_TRACE")

  let record ~hit exprs =
    Option.iter
      (fun oc ->
        let r = { site = Call_site.caller (); hit; exprs } in
          Mutex.protect cache_mutex (fun () -> Marshal.to_channel oc r [])
      )
      out
end

let quick_check_cached exprs =
  let asked = exprs in
  let exprs = USet.of_list exprs |> USet.values |> List.sort Expr.compare in
  (* The Z3 call stays outside the lock: a miss that two domains take at once
     costs a duplicated query, which is cheaper than holding the cache while
     solving. *)
  let cached_result =
    Mutex.protect cache_mutex (fun () ->
        GenerationalCache.find_opt quick_check_cache exprs
    )
  in
    S7.record ~hit:(Option.is_some cached_result) asked;
    match cached_result with
    | Some result -> result
    | None ->
        let result = quick_check exprs in
          Mutex.protect cache_mutex (fun () ->
              GenerationalCache.add quick_check_cache exprs result
          );
          result

(** Simplified satisfiability check.

    @param exprs Constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
let is_sat exprs = quick_check exprs |> Option.value ~default:false

(** Simplified satisfiability check (cached).

    @param exprs Constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
let is_sat_cached exprs =
  quick_check_cached exprs |> Option.value ~default:false

(** Simplified unsatisfiability check.

    @param exprs Constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
let is_unsat exprs = quick_check exprs |> Option.value ~default:true |> not

(** Simplified unsatisfiability check (cached).

    @param exprs Constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
let is_unsat_cached exprs =
  quick_check_cached exprs |> Option.value ~default:true |> not

(** Check if constraints imply a conclusion.

    Tests [constraints ⊢ conclusion] by checking if [constraints ∧ ¬conclusion]
    is unsatisfiable.

    @param constraints Antecedent expressions
    @param conclusion Consequent expression
    @return [true] if implication holds *)
let implies constraints conclusion =
  let negated = Expr.inverse conclusion in
  let solver = create (constraints @ [ negated ]) in
  let result = check solver in
    match result with
    | Some false -> true (* Negation is UNSAT => implication holds *)
    | _ -> false

(** Advanced solve using multiple strategies.

    Tries constant evaluation, tautology checking, then Z3.

    @param solver The solver to check
    @return SAT/UNSAT/UNKNOWN result *)
let solve_advanced solver =
  (* Check for contradictions *)
  let has_contradiction =
    List.exists Expr.is_contradiction solver.expressions
  in
    if has_contradiction then Some false
    else
      (* Check if all tautologies *)
      let all_taut = List.for_all Expr.is_tautology solver.expressions in
        if all_taut then Some true
        else
          (* Use Z3 for complex cases *)
          check solver

(** {1 Model Extraction}

    Functions for extracting satisfying assignments and concrete values. *)

(* The model of a solver [check] found satisfiable, as bindings. *)
let model_bindings solver = Smt_backend.model solver.context

(** Solve and extract a satisfying model.

    If satisfiable, returns variable bindings from the model.

    @param solver The solver to solve
    @return [Some bindings] if SAT, [None] if UNSAT/UNKNOWN *)
let solve solver =
  match check solver with
  | Some true -> model_bindings solver
  | Some false | None -> None

(** Quick solve and model extraction.

    @param exprs Constraint expressions
    @return [Some bindings] if SAT, [None] otherwise *)
let quick_solve exprs =
  let solver = create exprs in
    solve solver

type outcome = Model of (string, value_type) Hashtbl.t | Unsat | Unknown

let quick_solve_outcome exprs =
  let solver = create exprs in
    match check solver with
    | Some false -> Unsat
    | None -> Unknown
    | Some true -> (
        match model_bindings solver with
        | Some bindings -> Model bindings
        | None -> Unknown
      )

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
  let model_opt = solve solver in
    match model_opt with
    | None -> None
    | Some bindings ->
        let results = Hashtbl.create (List.length var_names) in
          List.iter
            (fun var_name ->
              match concrete_value bindings var_name with
              | Some value -> Hashtbl.add results var_name value
              | None -> ()
            )
            var_names;
          Some results

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
  let _ = () in

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
    Some [ [] ]
  else
    let non_empty =
      List.filter (fun c -> List.length c > 0) filtered_clauses2
    in

    (* Empty result means unsatisfiable *)
    if List.length non_empty = 0 then None else Some non_empty

(** {1 Solver Introspection} *)

(** Get statistics from the SMT backend.

    Returns performance information like decisions, conflicts, propagations.

    @param solver The solver to inspect
    @return Formatted statistics string *)
let get_statistics solver = Smt_backend.statistics solver.context

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
  if Expr.equal a b then true
  else
    (* Check if state && (a != b) is UNSAT *)
    let neq_expr = Expr.binop a "!=" b in
      is_unsat_cached (neq_expr :: state |> List.sort Expr.compare)

(** Check if two expressions could potentially be equal.

    Returns [true] if there exists an assignment (consistent with state) where
    [a = b].

    Implementation: checks if [state ∧ (a = b)] is satisfiable.

    @param state Optional additional constraints (default: [])
    @param a First expression
    @param b Second expression
    @return [true] if potentially equal *)
let expoteq ?(state = []) a b =
  let result =
    (* Check if a = b is satisfiable *)
    Expr.equal a b
    || is_sat_cached (Expr.binop a "=" b :: state |> List.sort Expr.compare)
  in

  result
