open Types

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
