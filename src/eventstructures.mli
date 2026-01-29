open Types

(** {1 Symbolic Event Structure} *)

(** Symbolic event structure: type and operations *)
module SymbolicEventStructure : sig
  (** Symbolic event structure type alias *)
  type t = symbolic_event_structure

  (** Create an empty symbolic event structure *)
  val create : unit -> t

  (** Prefix symbolic operation with event *)
  val dot : event -> t -> expr list -> expr list -> t

  (** Disjoint union of two symbolic event structures; intended for branching.
  *)
  val plus : t -> t -> t

  (** Cross product of two symbolic event structures; intended for parallel
      composition. *)
  val cross : t -> t -> t

  (** Get events in a loop by loop ID *)
  val events_in_loop : t -> int -> int uset

  (** Get program order predecessors of an event *)
  val events_po_before : t -> int -> int uset
end

(** {1 Types} *)

(** Path information containing event sequence and predicates *)
type path_info = {
  path : int uset;  (** Sequence of event labels in the path *)
  p : expr list;  (** List of predicate lists for path constraints *)
}

(** {1 Utility Functions} *)

(** [structure name] finds the origin event of a symbol.

    Looks up origin in event structures' origin hashtable.

    @param structure The symbolic event structure
    @param name The symbol name
    @return [Some event_label] if found, [None] otherwise *)
val origin : symbolic_event_structure -> string -> int option

(** {1 Path Generation} *)

(** [structure] Generate maximal conflict-free sets of events as paths through
    the symbolic event structure.

    The algorithm
    - implements a depth-first search
    - assumes acyclicity of the event structure
    - uses conflict relation in the event structure.

    @param structure The symbolic event structure
    @return
      List of path information records, each containing a maximal conflict-free
      set of events and the associated predicates *)
val generate_max_conflictfree_sets : symbolic_event_structure -> path_info list

(** [structure write read] Checks downward-closed same-location writes beofre
    conditon of write-read pairs.

    The condition holds for a pair (w,r) of write and read events if there is
    not other write po-between w and r to the same location as w relative to the
    constraints of r.

    @param structure The symbolic event structure
    @param write The write event label
    @param read The read event label
    @return [Lwt.t] of [true] if condition holds, [false] otherwise *)
val dslwb : symbolic_event_structure -> int -> int -> bool Lwt.t
