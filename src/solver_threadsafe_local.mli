(** solver_threadsafe_local.mli - Thread-safe solver with thread-local caching
*)

open Types

(** Thread-local solver context This module provides thread-local storage for
    solver caches, making cached operations safe for concurrent use. *)

(** {1 Thread-Local Cache Management} *)

(** Thread-local cache type *)
type local_cache

(** Initialize thread-local caching for the current thread. Call this once per
    thread before using cached operations. Returns a cache handle for this
    thread. *)
val init_thread_cache : unit -> local_cache

(** Clear the cache for the current thread *)
val clear_thread_cache : local_cache -> unit

(** Get cache statistics for the current thread *)
val cache_stats : local_cache -> string

(** {1 Thread-Safe Cached Operations} *)

(** Quick satisfiability check with thread-local caching. Safe to call from
    multiple threads when each thread has its own local_cache. *)
val quick_check_cached : local_cache -> expr list -> bool option Lwt.t

(** Check if expression list is satisfiable with thread-local caching. *)
val is_sat_cached : local_cache -> expr list -> bool Lwt.t

(** Check if expression list is unsatisfiable with thread-local caching. *)
val is_unsat_cached : local_cache -> expr list -> bool Lwt.t

(** {1 Thread-Safe Semantic Equality with Thread-Local Caching} *)

(** Thread-local semantic equality cache *)
type semeq_cache

(** Create a new thread-local semantic equality cache *)
val create_semeq_cache : unit -> semeq_cache

(** Cached semantic equality check with thread-local cache *)
val exeq_cached : semeq_cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

(** Cached potential equality check with thread-local cache *)
val expoteq_cached :
  semeq_cache -> ?state:expr list -> expr -> expr -> bool Lwt.t

(** Clear semantic equality cache *)
val clear_semeq_cache : semeq_cache -> unit

(** {1 Parallel Execution with Automatic Thread-Local Caching} *)

module ParallelCached : sig
  (** Execute parallel operations with automatic thread-local caching. Each
      worker thread automatically gets its own cache. *)

  (** Parallel check with automatic thread-local caching *)
  val parallel_check : int -> expr list list -> bool option list Lwt.t

  (** Parallel solve with automatic thread-local caching *)
  val parallel_solve :
    int -> expr list list -> (string, value_type) Hashtbl.t option list Lwt.t

  (** Parallel map with automatic thread-local caching and custom function *)
  val parallel_map :
    int -> (local_cache -> 'a -> 'b Lwt.t) -> 'a list -> 'b list Lwt.t
end
