(** {1 Constraint Solver Interface}

    This module provides a constraint solver interface built on top of the Z3
    SMT solver. It supports constraint satisfaction problems with integer,
    boolean, and bitvector operations.

    The solver can:
    - Check satisfiability of constraint expressions
    - Extract concrete models (variable assignments)
    - Perform semantic equality checks
    - Support incremental solving with push/pop
    - Cache results for performance

    @author Your Name
    @version 1.0 *)

open Types

(** {1 Core Types} *)

(** Solver context containing Z3 state and variable mappings.

    This type encapsulates the Z3 context, solver instance, and a mapping from
    variable names to Z3 expressions. Each context maintains its own namespace
    of variables. *)
type context = {
  ctx : Z3.context;  (** The Z3 context for all operations *)
  solver : Z3.Solver.solver;  (** The Z3 solver instance *)
  vars : (string, Z3.Expr.expr) Hashtbl.t;
      (** Mapping from variable names to Z3 expressions *)
}

(** Range type for interval-based solving.

    Represents a closed interval [min, max] for integer values. *)
type range = Z.t * Z.t

(** Solver state containing context and constraint expressions.

    This type packages together a Z3 context with the list of constraint
    expressions that have been added to it. *)
type solver = {
  context : context;  (** The underlying Z3 context *)
  expressions : expr list;  (** The constraint expressions to solve *)
}

(** {1 Context Management}

    Functions for creating and managing Z3 solver contexts. *)

(** Create a new solver context with fresh Z3 state.

    This initializes a new Z3 context and solver, with an empty variable table.

    @return A new context ready for solving *)
val create_context : unit -> context

(** Get or create a Z3 variable by name.

    If the variable already exists in the context, returns the existing Z3
    expression. Otherwise, creates a new integer-typed Z3 constant and adds it
    to the context's variable table.

    @param context The solver context
    @param name The variable name
    @return The Z3 expression representing this variable *)
val get_var : context -> string -> Z3.Expr.expr

(** {1 Z3 Conversion}

    Functions for converting between internal representations and Z3
    expressions. *)

(** Convert a value to its Z3 expression representation.

    Handles conversion of numbers, symbols, variables, and booleans to their
    corresponding Z3 representations.

    @param context The solver context for creating Z3 expressions
    @param value The value to convert
    @return The Z3 expression representing the value *)
val value_to_z3 : context -> value_type -> Z3.Expr.expr

(** Convert an expression to its Z3 expression representation.

    Recursively converts expression trees to Z3, handling:
    - Numbers, variables, booleans, and symbols
    - Binary operations (arithmetic, comparison, logical, bitwise)
    - Unary operations (negation, logical not)
    - Disjunctions (OR of multiple clauses)

    Special handling for mixed integer/bitvector operations.

    @param context The solver context for creating Z3 expressions
    @param expr The expression to convert
    @return The Z3 expression representing the input expression *)
val expr_to_z3 : context -> expr -> Z3.Expr.expr

(** {1 Solver Creation and Management}

    Functions for creating and modifying solver instances. *)

(** Create a new solver from a list of constraint expressions.

    The constraints are not immediately added to the Z3 solver; they are stored
    and will be added when checking satisfiability.

    @param exprs The list of constraint expressions
    @return A new solver containing these constraints *)
val create : expr list -> solver

(** Reset a solver by creating a fresh context.

    This discards all Z3 state and variable mappings, creating a new context
    while keeping the same constraint expressions.

    @param solver The solver to reset
    @return A new solver with fresh context and the same expressions *)
val reset : solver -> solver

(** Push a new scope onto the solver stack for backtracking.

    This saves the current solver state. Subsequent assertions can be undone by
    calling {!pop}.

    @param solver The solver to push
    @return The same solver (mutates Z3 state) *)
val push : solver -> solver

(** Pop the most recent scope from the solver stack.

    This undoes all assertions added since the last {!push}.

    @param solver The solver to pop
    @return The same solver (mutates Z3 state) *)
val pop : solver -> solver

(** Add new constraint expressions to an existing solver.

    Converts the expressions to Z3 and immediately adds them to the Z3 solver.

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
val check : solver -> bool option Lwt.t

(** Quick satisfiability check without caching.

    Creates a solver and immediately checks satisfiability. Convenient for
    one-off checks.

    @param exprs The constraint expressions to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown *)
val quick_check : expr list -> bool option Lwt.t

(** Quick satisfiability check with result caching.

    Like {!quick_check} but caches results based on the normalized constraint
    set. Subsequent calls with equivalent constraints return cached results.

    @param exprs The constraint expressions to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown *)
val quick_check_cached : expr list -> bool option Lwt.t

(** Check if constraint expressions are satisfiable.

    Simplified API that returns true if satisfiable, false otherwise (including
    unknown cases).

    @param exprs The constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
val is_sat : expr list -> bool Lwt.t

(** Check if constraint expressions are satisfiable (cached).

    Like {!is_sat} but with result caching.

    @param exprs The constraint expressions
    @return [true] if satisfiable, [false] otherwise *)
val is_sat_cached : expr list -> bool Lwt.t

(** Check if constraint expressions are unsatisfiable.

    Simplified API that returns true if definitely unsatisfiable, false
    otherwise (including satisfiable and unknown cases).

    @param exprs The constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
val is_unsat : expr list -> bool Lwt.t

(** Check if constraint expressions are unsatisfiable (cached).

    Like {!is_unsat} but with result caching.

    @param exprs The constraint expressions
    @return [true] if unsatisfiable, [false] otherwise *)
val is_unsat_cached : expr list -> bool Lwt.t

(** Advanced solve using multiple strategies.

    Tries different solving strategies including:
    - Constant evaluation
    - Tautology checking
    - Full Z3 solving

    @param solver The solver to check
    @return
      [Some true] if satisfiable, [Some false] if unsatisfiable, [None] if
      unknown *)
val solve_advanced : solver -> bool option Lwt.t

(** Check if constraints imply a conclusion.

    Tests whether [constraints ⊢ conclusion] by checking if
    [constraints ∧ ¬conclusion] is unsatisfiable.

    @param constraints The antecedent constraint expressions
    @param conclusion The consequent expression to prove
    @return [true] if the implication holds, [false] otherwise *)
val implies : expr list -> expr -> bool Lwt.t

(** {1 Solution Extraction}

    Functions for extracting concrete models and variable assignments. *)

(** Solve constraints and extract a satisfying model.

    If the constraints are satisfiable, returns a hash table mapping variable
    names to their assigned values in the model.

    @param solver The solver containing constraints
    @return
      [Some bindings] if satisfiable (where bindings map variables to values),
      [None] if unsatisfiable or unknown *)
val solve : solver -> (string, value_type) Hashtbl.t option Lwt.t

(** Quick solve and model extraction.

    Creates a solver and immediately extracts a model if satisfiable.

    @param exprs The constraint expressions
    @return [Some bindings] if satisfiable, [None] otherwise *)
val quick_solve : expr list -> (string, value_type) Hashtbl.t option Lwt.t

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
  solver -> string list -> (string, value_type) Hashtbl.t option Lwt.t

(** Solve with Z3 and return ranges or concrete values.

    For each variable, attempts to determine possible value ranges rather than
    just a single concrete value. Useful for constraint analysis.

    @param solver The solver containing constraints
    @return
      [Some ranges] mapping variables to lists of possible ranges, [None] if
      unsatisfiable *)
val solve_with_ranges : solver -> (string, range list) Hashtbl.t option Lwt.t

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
val simplify_disjunction : expr list list -> expr list list option Lwt.t

(** {1 Solver Introspection}

    Functions for inspecting solver state and performance. *)

(** Get statistics from the Z3 solver.

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
val exeq : ?state:expr list -> expr -> expr -> bool Lwt.t

(** Check if two expressions could potentially be equal.

    Returns [true] if there exists some variable assignment (consistent with
    state constraints) where [a = b], i.e., equality is satisfiable.

    Implementation: checks if [state ∧ (a = b)] is satisfiable.

    @param state Optional additional constraints (default: [])
    @param a The first expression
    @param b The second expression
    @return [true] if potentially equal, [false] if never equal *)
val expoteq : ?state:expr list -> expr -> expr -> bool Lwt.t

(** {2 Semantic Equality with State Management}

    A module for semantic equality checking with mutable state context. *)
module Semeq : sig
  (** Mutable state for semantic equality checking.

      Stores a context of constraint expressions that are applied to all
      equality checks. *)
  type state = { mutable context : expr list }

  (** Create a new empty state.

      @return A state with empty context *)
  val create_state : unit -> state

  (** Update the constraint context for a state.

      @param state The state to modify
      @param context The new constraint expressions *)
  val set_state : state -> expr list -> unit

  (** Check semantic equality using the state's context.

      Equivalent to [exeq ~state:state.context a b].

      @param state The state providing context constraints
      @param a The first expression
      @param b The second expression
      @return [true] if semantically equal, [false] otherwise *)
  val exeq : state -> expr -> expr -> bool Lwt.t

  (** Check potential equality using the state's context.

      Equivalent to [expoteq ~state:state.context a b].

      @param state The state providing context constraints
      @param a The first expression
      @param b The second expression
      @return [true] if potentially equal, [false] otherwise *)
  val expoteq : state -> expr -> expr -> bool Lwt.t

  (** Check potential equality of two values.

      Converts values to expressions and checks if they could be equal given the
      state's constraints.

      @param state The state providing context constraints
      @param v1 The first value
      @param v2 The second value
      @return [true] if the values could be equal, [false] otherwise *)
  val expoteq_value : state -> value_type -> value_type -> bool Lwt.t
end

(** {2 Cached Semantic Equality}

    A module providing cached versions of semantic equality checks for
    performance optimization. *)
module SemeqCache : sig
  (** Cache type storing equality check results.

      Maintains separate caches for semantic equality (exeq) and potential
      equality (expoteq) checks. *)
  type cache = {
    eq_cache : (string, bool) Hashtbl.t;
        (** Cache for semantic equality results *)
    poteq_cache : (string, bool) Hashtbl.t;
        (** Cache for potential equality results *)
  }

  (** Create a new empty cache.

      @return A fresh cache with no stored results *)
  val create : unit -> cache

  (** Cached semantic equality check.

      Checks the cache first; if not found, computes the result and stores it.

      @param cache The cache to use
      @param state Optional additional constraints (default: [])
      @param a The first expression
      @param b The second expression
      @return [true] if semantically equal, [false] otherwise *)
  val exeq_cached : cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

  (** Cached potential equality check.

      Checks the cache first; if not found, computes the result and stores it.

      @param cache The cache to use
      @param state Optional additional constraints (default: [])
      @param a The first expression
      @param b The second expression
      @return [true] if potentially equal, [false] otherwise *)
  val expoteq_cached : cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

  (** Clear all cached results.

      @param cache The cache to clear *)
  val clear : cache -> unit
end
