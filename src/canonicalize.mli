(** Canonicalization of symbolic executions (from S9; productized by R1).

    Order- and id-independent rendering of executions and execution sets, so
    two pipeline runs can be compared for equivalence regardless of internal
    enumeration order. See the module implementation for the full contract and
    known limitations (syntactic predicate comparison; [co] excluded). *)

open Types

(** Canonical form of a single execution: renumbered, sorted data compared by
    ordinary structural equality. *)
type t = {
  events : string list;
  po : (int * int) list;
  rf : (int * int) list;
  dp : (int * int) list;
  ppo : (int * int) list;
  rmw : (int * int) list;
  predicates : string list;
}

(** [canonicalize structure exec] renders one execution into canonical form. *)
val canonicalize : symbolic_event_structure -> symbolic_execution -> t

(** [canonicalize_set structure execs] canonicalizes and sorts an execution
    set into a canonical, order-independent list. *)
val canonicalize_set :
  symbolic_event_structure -> symbolic_execution list -> t list

(** Canonical string for one execution. Path predicates are excluded unless
    [with_predicates] is true. *)
val signature : ?with_predicates:bool -> t -> string

(** Canonical string for a whole execution set (order-independent). *)
val set_signature : ?with_predicates:bool -> t list -> string

(** Equality of two canonical execution sets. *)
val equal_sets : ?with_predicates:bool -> t list -> t list -> bool
