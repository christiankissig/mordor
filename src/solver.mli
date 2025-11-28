(** solver.mli - Interface for constraint solver using Z3 *)

open Types

(** Solver context *)
type context = {
  ctx : Z3.context;
  solver : Z3.Solver.solver;
  vars : (string, Z3.Expr.expr) Hashtbl.t;
}

(** Range type for interval-based solving *)
type range = Z.t * Z.t

(** Solver type *)
type solver = { context : context; expressions : expr list }

(** {1 Context Management} *)

(** Create new solver context *)
val create_context : unit -> context

(** Get or create Z3 variable *)
val get_var : context -> string -> Z3.Expr.expr

(** {1 Z3 Conversion} *)

(** Convert value to Z3 expression *)
val value_to_z3 : context -> value_type -> Z3.Expr.expr

(** Convert expression to Z3 *)
val expr_to_z3 : context -> expr -> Z3.Expr.expr

(** {1 Solver Creation and Management} *)

(** Create a new solver from a list of constraint expressions *)
val create : expr list -> solver

(** Reset solver (create fresh context) *)
val reset : solver -> solver

(** Push solver state (for backtracking) *)
val push : solver -> solver

(** Pop solver state (for backtracking) *)
val pop : solver -> solver

(** Add assertions to existing solver *)
val add_assertions : solver -> expr list -> solver

(** {1 Satisfiability Checking} *)

(** Check satisfiability of constraints. Returns Some true if satisfiable, Some
    false if unsatisfiable, None if unknown *)
val check : solver -> bool option Lwt.t

(** Quick satisfiability check - creates solver and checks in one call *)
val quick_check : expr list -> bool option Lwt.t

(** Quick satisfiability check - creates solver and checks in one call. Cached
*)
val quick_check_cached : expr list -> bool option Lwt.t

(** Check if expression list is satisfiable *)
val is_sat : expr list -> bool Lwt.t

(** Check if expression list is satisfiable. Cached *)
val is_sat_cached : expr list -> bool Lwt.t

(** Check if expression list is unsatisfiable *)
val is_unsat : expr list -> bool Lwt.t

(** Check if expression list is unsatisfiable. Cached *)
val is_unsat_cached : expr list -> bool Lwt.t

(** Advanced solve that checks multiple strategies *)
val solve_advanced : solver -> bool option Lwt.t

(** Check if a set of constraints implies another expression *)
val implies : expr list -> expr -> bool Lwt.t

(** {1 Solution Extraction} *)

(** Solve and get model. Returns Some bindings if satisfiable, None otherwise *)
val solve : solver -> (string, value_type) Hashtbl.t option Lwt.t

(** Quick solve - creates solver and gets model in one call *)
val quick_solve : expr list -> (string, value_type) Hashtbl.t option Lwt.t

(** Get concrete value from solver result *)
val concrete_value :
  (string, value_type) Hashtbl.t -> string -> value_type option

(** Solve and extract concrete values for specific variables *)
val solve_for_vars :
  solver -> string list -> (string, value_type) Hashtbl.t option Lwt.t

(** Solve with Z3 and return ranges or concrete values *)
val solve_with_ranges : solver -> (string, range list) Hashtbl.t option Lwt.t

(** Convert Z3 model to readable string *)
val model_to_string : (string, value_type) Hashtbl.t -> string

(** {1 Expression Analysis} *)

(** Get all symbols from a list of expressions *)
val get_all_symbols : expr list -> string list

(** Check if all expressions are flat (for optimization) *)
val all_flat : expr list -> bool

(** Simplify disjunction using basic heuristics. Returns Some simplified_clauses
    or None if unsatisfiable *)
val simplify_disjunction : expr list list -> expr list list option Lwt.t

(** {1 Solver Introspection} *)

(** Get statistics from solver *)
val get_statistics : solver -> string

(** {1 Semantic Equality} *)

(** Check if two expressions are semantically equal (always equal under all
    interpretations). Optional state parameter provides additional constraints
*)
val exeq : ?state:expr list -> expr -> expr -> bool Lwt.t

(** Check if two expressions are potentially equal (equality is satisfiable).
    Optional state parameter provides additional constraints *)
val expoteq : ?state:expr list -> expr -> expr -> bool Lwt.t

(** Semantic equality module with state management *)
module Semeq : sig
  (** Mutable state for semantic equality checking *)
  type state = { mutable context : expr list }

  (** Create new state *)
  val create_state : unit -> state

  (** Set global state *)
  val set_state : state -> expr list -> unit

  (** Check semantic equality with current state *)
  val exeq : state -> expr -> expr -> bool Lwt.t

  (** Check potential equality with current state *)
  val expoteq : state -> expr -> expr -> bool Lwt.t

  (** Check potential equality of values *)
  val expoteq_value : state -> value_type -> value_type -> bool Lwt.t
end

(** Cache for semantic equality results *)
module SemeqCache : sig
  (** Cache type *)
  type cache = {
    eq_cache : (string, bool) Hashtbl.t;
    poteq_cache : (string, bool) Hashtbl.t;
  }

  (** Create new cache *)
  val create : unit -> cache

  (** Cached semantic equality check *)
  val exeq_cached : cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

  (** Cached potential equality check *)
  val expoteq_cached : cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

  (** Clear cache *)
  val clear : cache -> unit
end
