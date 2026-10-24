(** {1 Constraint Solver Interface}

    This module provides a constraint solver interface built on top of the
    platform's SMT backend ({!Smt_backend}; Z3 natively). It supports constraint
    satisfaction problems with integer, boolean, and bitvector operations.

    The solver can:
    - Check satisfiability of constraint expressions
    - Extract concrete models (variable assignments)
    - Perform semantic equality checks
    - Solve in scopes of a long-lived solver, one per domain
    - Cache results for performance

    @author Your Name
    @version 1.0 *)

open Types

(** {1 Core Types} *)

(** Solver state: the platform's solver ({!Smt_backend}) and the constraint
    expressions {!check} asks it about. *)
type solver = {
  context : Smt_backend.solver;  (** The backend's solver *)
  expressions : expr list;  (** The constraint expressions to solve *)
}

(** {1 Solver Creation and Management}

    Functions for creating and modifying solver instances. *)

(** Create a new solver from a list of constraint expressions.

    The constraints are not immediately added to the backend's solver; they are
    stored and will be added when checking satisfiability.

    @param exprs The list of constraint expressions
    @return A new solver containing these constraints *)
val create : expr list -> solver

(** Reset a solver by creating a fresh context.

    This discards the backend solver's assertions and the variable mappings,
    keeping the same constraint expressions. (Natively, the underlying
    [Z3.context] is this domain's and is not rebuilt.)

    @param solver The solver to reset
    @return A new solver with fresh context and the same expressions *)
val reset : solver -> solver

(** Push a new scope onto the solver stack for backtracking.

    This saves the current solver state. Subsequent assertions can be undone by
    calling {!pop}.

    @param solver The solver to push
    @return The same solver (mutates the backend's state) *)
val push : solver -> solver

(** Pop the most recent scope from the solver stack.

    This undoes all assertions added since the last {!push}.

    @param solver The solver to pop
    @return The same solver (mutates the backend's state) *)
val pop : solver -> solver

(** Add new constraint expressions to an existing solver.

    Translates the expressions for the backend and immediately asserts them.

    @param solver The solver to extend
    @param exprs The expressions to add
    @return The modified solver *)
val add_assertions : solver -> expr list -> solver

(** {1 Satisfiability Checking}

    Functions for checking constraint satisfiability with various strategies. *)

(** Check satisfiability of the solver's constraints.

    This performs several optimizations before calling Z3:
    - Quick checks for obvious contradictions (e.g., false)
    - Quick checks for tautologies (e.g., true)
    - Constant expression evaluation
    - Only calls Z3 if necessary

    @param solver The solver containing constraints to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown/timeout *)
val check : solver -> bool option

(** [trivially exprs] is what {!check} decides of [exprs] without Z3: [false]
    for a contradiction or a false constant comparison, [true] for none or only
    tautologies, and [None] otherwise. *)
val trivially : expr list -> bool option

(** [check_asserted solver] asks the backend about what has been asserted in
    [solver]'s backend solver, by {!add_assertions} or earlier checks, and
    nothing else: no syntactic shortcut and nothing added. *)
val check_asserted : solver -> bool option

(** {1 Scoped Solving} *)

(** [scoped f] is [f] applied to this domain's long-lived solver, in a scope of
    its own: whatever [f] asserts is retracted when [f] returns or raises. What
    [f] finds asserted when it starts is what enclosing scopes asserted, which
    at the outermost is nothing. A domain's solver is its own, so domains
    solving at once do not share one. *)
val scoped : (solver -> 'a) -> 'a

(** Whether {!quick_check} builds a fresh backend solver per query instead of
    solving in a scope of this domain's long-lived one. Off unless
    [MORDOR_FRESH_SOLVER] is set. The answers are the same; the fresh solver is
    slower. *)
val fresh_solvers : bool ref

(** Quick satisfiability check without caching.

    Creates a solver and immediately checks satisfiability. Convenient for
    one-off checks.

    @param exprs The constraint expressions to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown *)
val quick_check : expr list -> bool option

(** Quick satisfiability check with result caching.

    Like {!quick_check} but caches results based on the normalized constraint
    set. Subsequent calls with equivalent constraints return cached results.

    @param exprs The constraint expressions to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown *)
val quick_check_cached : expr list -> bool option

(** S7 (#19): with [MORDOR_S7_TRACE] set to a path, every query to
    {!quick_check_cached} is written there in the order asked, one [Marshal]led
    [record] each. *)
module S7 : sig
  type record = {
    site : string;  (** The function it was asked from. *)
    hit : bool;  (** Whether the cache answered it. *)
    exprs : expr list;  (** The conjunction as the caller built it. *)
  }
end

(** Check if constraint expressions are satisfiable.

    Simplified API that returns true if satisfiable, false otherwise (including
    unknown cases).

    @param exprs The constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
val is_sat : expr list -> bool

(** Check if constraint expressions are satisfiable (cached).

    Like {!is_sat} but with result caching.

    @param exprs The constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
val is_sat_cached : expr list -> bool

(** Check if constraint expressions are unsatisfiable.

    Simplified API that returns true if definitely unsatisfiable, false
    otherwise (including satisfiable and unknown cases).

    @param exprs The constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
val is_unsat : expr list -> bool

(** Check if constraint expressions are unsatisfiable (cached).

    Like {!is_unsat} but with result caching.

    @param exprs The constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
val is_unsat_cached : expr list -> bool

(** Advanced solve using multiple strategies.

    Tries different solving strategies including:
    - Constant evaluation
    - Tautology checking
    - Full Z3 solving

    @param solver The solver to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown *)
val solve_advanced : solver -> bool option

(** Check if constraints imply a conclusion.

    Tests whether [constraints ⊢ conclusion] by checking if
    [constraints ∧ ¬conclusion] is unsatisfiable.

    @param constraints The antecedent constraint expressions
    @param conclusion The consequent expression to prove
    @return [true] if the implication holds, [false] otherwise *)
val implies : expr list -> expr -> bool

(** {1 Solution Extraction}

    Functions for extracting concrete models and variable assignments. *)

(** Solve constraints and extract a satisfying model.

    If the constraints are satisfiable, returns a hash table mapping variable
    names to their assigned values in the model.

    @param solver The solver containing constraints
    @return
      [Some bindings] if satisfiable (where bindings map variables to values),
      [None] if unsatisfiable or unknown *)
val solve : solver -> (string, value_type) Hashtbl.t option

(** Quick solve and model extraction.

    Creates a solver and immediately extracts a model if satisfiable.

    @param exprs The constraint expressions
    @return [Some bindings] if satisfiable, [None] otherwise *)
val quick_solve : expr list -> (string, value_type) Hashtbl.t option

(** What {!quick_solve_outcome} found. *)
type outcome =
  | Model of (string, value_type) Hashtbl.t  (** Satisfiable, with a model. *)
  | Unsat
  | Unknown  (** Z3 gave up, or the model could not be read back. *)

(** [quick_solve_outcome exprs] is {!quick_solve} keeping apart what
    {!quick_solve} folds together: unsatisfiable, which proves something, and
    unknown, which does not. *)
val quick_solve_outcome : expr list -> outcome

(** Extract a concrete value for a variable from a model.

    @param bindings The model bindings from {!solve}
    @param var The variable name to look up
    @return [Some value] if the variable is bound, [None] otherwise *)
val concrete_value :
  (string, value_type) Hashtbl.t -> string -> value_type option

(** Solve and extract values for specific variables only.

    More efficient than {!solve} when you only need values for a subset of
    variables. Unbounded variables are omitted from the result.

    @param solver The solver containing constraints
    @param var_names The list of variable names to extract
    @return
      [Some bindings] for the requested variables if satisfiable, [None] if
      unsatisfiable *)
val solve_for_vars :
  solver -> string list -> (string, value_type) Hashtbl.t option

(** Convert a model to a human-readable string.

    Formats the variable bindings as "var1 = value1, var2 = value2, ..." with
    variables sorted alphabetically.

    @param bindings The model bindings from {!solve}
    @return A formatted string representation *)
val model_to_string : (string, value_type) Hashtbl.t -> string

(** {1 Expression Analysis}

    Functions for analyzing and simplifying expressions. *)

(** Extract all symbol/variable names from expressions.

    Traverses the expression list and collects all unique symbol and variable
    names that appear.

    @param exprs The expressions to analyze
    @return A list of unique symbol/variable names *)
val get_all_symbols : expr list -> string list

(** Check if all expressions are flat (contain no nested subexpressions).

    A flat expression is one where all operands are constants or variables, with
    no nested operations. Useful for optimization.

    @param exprs The expressions to check
    @return [true] if all expressions are flat, [false] otherwise *)
val all_flat : expr list -> bool

(** Simplify a disjunctive normal form (DNF) expression.

    Takes a list of clause lists (representing (clause1 OR clause2 OR ...)) and
    applies simplification heuristics:
    - Removes tautological clauses
    - Removes contradictory clauses
    - Checks satisfiability if needed

    @param clauses The list of clauses (each clause is a list of expressions)
    @return [Some simplified_clauses] if satisfiable, [None] if unsatisfiable *)
val simplify_disjunction : expr list list -> expr list list option

(** {1 Solver Introspection}

    Functions for inspecting solver state and performance. *)

(** Get statistics from the SMT backend.

    Returns information about the solver's performance, such as number of
    decisions, conflicts, and propagations.

    @param solver The solver to inspect
    @return A formatted string of solver statistics *)
val get_statistics : solver -> string

(** {1 Semantic Equality}

    Functions for checking semantic equality and potential equality of
    expressions.

    Semantic equality means two expressions are equivalent under all possible
    variable assignments (i.e., they are logically equivalent).

    Potential equality means there exists at least one variable assignment where
    the two expressions have the same value (i.e., equality is satisfiable). *)

(** Check if two expressions are semantically equal.

    Returns [true] if [a] and [b] are logically equivalent (always have the same
    value under any interpretation), given the optional state constraints.

    Implementation: checks if [state ∧ (a ≠ b)] is unsatisfiable.

    @param state Optional additional constraints (default: [])
    @param a The first expression
    @param b The second expression
    @return [true] if semantically equal, [false] otherwise *)
val exeq : ?state:expr list -> expr -> expr -> bool

(** Check if two expressions could potentially be equal.

    Returns [true] if there exists some variable assignment (consistent with
    state constraints) where [a = b], i.e., equality is satisfiable.

    Implementation: checks if [state ∧ (a = b)] is satisfiable.

    @param state Optional additional constraints (default: [])
    @param a The first expression
    @param b The second expression
    @return [true] if potentially equal, [false] if never equal *)
val expoteq : ?state:expr list -> expr -> expr -> bool
