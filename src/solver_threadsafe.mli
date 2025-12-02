(** solver_threadsafe.mli - Thread-safe interface for constraint solver *)

open Types

(** Thread-safe solver handle Each handle maintains its own Z3 context for
    thread safety *)
type t

(** {1 Thread-Safe Solver Creation} *)

(** Create a new thread-safe solver instance. Each instance has its own Z3
    context and is safe to use from a single thread. For multi-threaded usage,
    create one instance per thread. *)
val create : expr list -> t

(** Create a new empty thread-safe solver instance *)
val create_empty : unit -> t

(** {1 Solver Management} *)

(** Reset solver (creates fresh context) *)
val reset : t -> t

(** Push solver state (for backtracking) *)
val push : t -> t

(** Pop solver state (for backtracking) *)
val pop : t -> t

(** Add assertions to existing solver *)
val add_assertions : t -> expr list -> t

(** {1 Satisfiability Checking} *)

(** Check satisfiability of constraints. Returns Some true if satisfiable, Some
    false if unsatisfiable, None if unknown *)
val check : t -> bool option Lwt.t

(** Quick satisfiability check - creates solver and checks in one call.
    Thread-safe: creates a new context for this operation *)
val quick_check : expr list -> bool option Lwt.t

(** Quick satisfiability check with caching. WARNING: Uses a global cache that
    is NOT thread-safe. Do not use this from multiple threads concurrently. For
    thread-safe cached operations, use SemeqCache with thread-local instances.
*)
val quick_check_cached : expr list -> bool option Lwt.t

(** Check if expression list is satisfiable. Thread-safe: creates a new context
    for this operation *)
val is_sat : expr list -> bool Lwt.t

(** Check if expression list is satisfiable with caching. WARNING: Uses a global
    cache that is NOT thread-safe. Do not use this from multiple threads
    concurrently. *)
val is_sat_cached : expr list -> bool Lwt.t

(** Check if expression list is unsatisfiable. Thread-safe: creates a new
    context for this operation *)
val is_unsat : expr list -> bool Lwt.t

(** Check if expression list is unsatisfiable with caching. WARNING: Uses a
    global cache that is NOT thread-safe. Do not use this from multiple threads
    concurrently. *)
val is_unsat_cached : expr list -> bool Lwt.t

(** Advanced solve that checks multiple strategies *)
val solve_advanced : t -> bool option Lwt.t

(** Check if a set of constraints implies another expression. Thread-safe:
    creates a new context for this operation *)
val implies : expr list -> expr -> bool Lwt.t

(** {1 Solution Extraction} *)

(** Solve and get model. Returns Some bindings if satisfiable, None otherwise *)
val solve : t -> (string, value_type) Hashtbl.t option Lwt.t

(** Quick solve - creates solver and gets model in one call. Thread-safe:
    creates a new context for this operation *)
val quick_solve : expr list -> (string, value_type) Hashtbl.t option Lwt.t

(** Get concrete value from solver result *)
val concrete_value :
  (string, value_type) Hashtbl.t -> string -> value_type option

(** Solve and extract concrete values for specific variables *)
val solve_for_vars :
  t -> string list -> (string, value_type) Hashtbl.t option Lwt.t

(** Solve with Z3 and return ranges or concrete values *)
val solve_with_ranges : t -> (string, (Z.t * Z.t) list) Hashtbl.t option Lwt.t

(** Convert Z3 model to readable string *)
val model_to_string : (string, value_type) Hashtbl.t -> string

(** {1 Expression Analysis} *)

(** Get all symbols from a list of expressions *)
val get_all_symbols : expr list -> string list

(** Check if all expressions are flat (for optimization) *)
val all_flat : expr list -> bool

(** Simplify disjunction using basic heuristics. Returns Some simplified_clauses
    or None if unsatisfiable. Thread-safe: creates a new context for this
    operation *)
val simplify_disjunction : expr list list -> expr list list option Lwt.t

(** {1 Solver Introspection} *)

(** Get statistics from solver *)
val get_statistics : t -> string

(** {1 Semantic Equality - Thread-Safe} *)

(** Check if two expressions are semantically equal (always equal under all
    interpretations). Optional state parameter provides additional constraints.
    Thread-safe: creates a new context for this operation *)
val exeq : ?state:expr list -> expr -> expr -> bool Lwt.t

(** Check if two expressions are potentially equal (equality is satisfiable).
    Optional state parameter provides additional constraints. Thread-safe:
    creates a new context for this operation *)
val expoteq : ?state:expr list -> expr -> expr -> bool Lwt.t

(** Thread-safe semantic equality module with isolated state per instance *)
module Semeq : sig
  (** Thread-safe state for semantic equality checking Each state maintains its
      own Z3 context *)
  type state

  (** Create new state with its own Z3 context *)
  val create_state : unit -> state

  (** Set state constraints *)
  val set_state : state -> expr list -> unit

  (** Check semantic equality with current state *)
  val exeq : state -> expr -> expr -> bool Lwt.t

  (** Check potential equality with current state *)
  val expoteq : state -> expr -> expr -> bool Lwt.t

  (** Check potential equality of values *)
  val expoteq_value : state -> value_type -> value_type -> bool Lwt.t
end

(** Thread-safe cache for semantic equality results Note: This cache should not
    be shared between threads. Create one cache instance per thread for
    thread-safe operation. *)
module SemeqCache : sig
  (** Cache type *)
  type cache

  (** Create new cache *)
  val create : unit -> cache

  (** Cached semantic equality check. Thread-safe: creates a new context for
      this operation *)
  val exeq_cached : cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

  (** Cached potential equality check. Thread-safe: creates a new context for
      this operation *)
  val expoteq_cached : cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

  (** Clear cache *)
  val clear : cache -> unit
end

(** {1 Thread Pool Utilities} *)

(** Module for running solver operations across multiple threads *)
module Pool : sig
  (** Execute a solver operation in a thread pool. Each thread gets its own
      solver instance with independent Z3 context.

      @param n_threads Number of worker threads to use
      @param tasks List of expression lists to solve
      @return List of results in the same order as tasks *)
  val parallel_check : int -> expr list list -> bool option list Lwt.t

  (** Execute solve operations in parallel *)
  val parallel_solve :
    int -> expr list list -> (string, value_type) Hashtbl.t option list Lwt.t

  (** Map a function over a list using parallel solver instances

      @param n_threads Number of worker threads
      @param f Function that takes a thread-safe solver and an item
      @param items List of items to process
      @return List of results *)
  val parallel_map : int -> (t -> 'a -> 'b Lwt.t) -> 'a list -> 'b list Lwt.t
end
