open Types

(** {1 Symbolic Event Structure} *)

(** Symbolic event structure: type and operations *)
module SymbolicEventStructure : sig
  (** Symbolic event structure type alias *)
  type t = symbolic_event_structure

  (** Create an empty symbolic event structure *)
  val create : unit -> t

  (** [dot ?env ?loops ?thread event structure phi defacto] prefixes [structure]
      with [event], under path condition [phi] and de facto constraints
      [defacto]. [structure] is left as it was.

      The result's per-event tables learn of [event]: [events] binds its label
      to it, [origin] binds the symbol it reads or allocates, if any, and [p],
      [loop_indices] and [thread_index] bind its label to [env], [loops] and
      [thread] where given. *)
  val dot :
    ?env:(string, expr) Hashtbl.t ->
    ?loops:int list ->
    ?thread:int ->
    event ->
    t ->
    expr list ->
    expr list ->
    t

  (** Disjoint union of two symbolic event structures; intended for branching.
  *)
  val plus : t -> t -> t

  (** Cross product of two symbolic event structures; intended for parallel
      composition. *)
  val cross : t -> t -> t

  (** [seq a b] is [a] followed by [b]: every event of [a] is po-before every
      event of [b], and the same pairs join [fj]. Intended for the join of a
      parallel block with the statements that follow it. *)
  val seq : t -> t -> t

  (** The events of one loop: those of [e] that [loop_indices] records as
      enclosed by [loop_id]. Nested loops are enclosed by their parents, so an
      inner loop's events are also the outer loop's. *)
  val events_in_loop : t -> int -> int uset

  (** Get program order predecessors of an event *)
  val events_po_before : t -> int -> int uset
end

(** {1 The Algebra of Event Structures} *)

(** What a program denotes, built from {!empty} and {!singleton} with {!seq},
    {!choice} and {!par} and nothing else.

    A facade over {!SymbolicEventStructure}'s combinators, adding no behaviour
    of its own. The classic recursion builds a structure from the end, one
    prefixed event at a time; a bottom-up construction builds fragments and
    joins them. Both can say what they build in these five operations, and this
    is the seam between the two.

    The laws, up to {!equal}: [seq], [choice] and [par] are associative with
    [empty ()] their unit, [choice] and [par] are commutative, and {!relabel}
    distributes over all three. *)
module EventStructure : sig
  type t = symbolic_event_structure

  (** The structure with no events. A function, since a structure's tables are
      mutable and two structures must not share them. *)
  val empty : unit -> t

  (** [singleton ?env ?loops ?thread event phi defacto] is the structure of
      [event] alone, under path condition [phi] and de facto constraints
      [defacto]; the optional arguments are {!SymbolicEventStructure.dot}'s. *)
  val singleton :
    ?env:(string, expr) Hashtbl.t ->
    ?loops:int list ->
    ?thread:int ->
    event ->
    expr list ->
    expr list ->
    t

  (** [seq ?join a b] is [a] followed by [b]: every event of [a] is po-before
      every event of [b]. With [~join:true] the same pairs are recorded in [fj],
      as the join of a parallel block with its continuation needs.

      [b] is not copied. Where [a] ends in a choice, [b] follows every branch of
      it at once, which is what the classic recursion avoids by interpreting the
      continuation once per branch; sequencing with copies is the bottom-up
      construction's to add. *)
  val seq : ?join:bool -> t -> t -> t

  (** [choice a b] is [a] or [b]: every event of one conflicts with every event
      of the other. *)
  val choice : t -> t -> t

  (** [par a b] is [a] beside [b], unordered and without conflict. *)
  val par : t -> t -> t

  (** [relabel ?off ?relab ?env_key ?thread s] is [s] with every event label
      shifted by [off], every symbol renamed by [relab], and every indexed event
      moved to [thread]. Labels and symbols are rewritten wherever they occur:
      in the sets and relations, as keys and values of the tables, and inside
      events, conditions, environments and constraints.

      [env_key] rewrites the keys of the register environments, for the ones
      that spell out a symbol's name, which no traversal of an expression finds.
      [loop_conditions] is left as it is: it is keyed by loop. *)
  val relabel :
    ?off:int ->
    ?relab:(string -> string option) ->
    ?env_key:(string -> string) ->
    ?thread:int ->
    t ->
    t

  (** Extensional equality: the same events, relations and table bindings,
      whatever order the underlying hash tables hold them in. [constraints] is
      compared as a set, since its order and repetitions record only the order
      in which structures were combined. *)
  val equal : t -> t -> bool
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

    [exclude] names events that are not in the caller's execution, so that a
    write it has elided cannot shadow anything. It defaults to empty, which
    reads the condition off the structure alone.

    [state] is the solver state location equality is decided under. It defaults
    to the branch conditions guarding the read; a caller that has already
    checked the rf edge's own location under stronger predicates should pass
    those, so both tests on the edge see the same assumptions.

    @param exclude Events the execution does not contain
    @param state Predicates to decide location equality under
    @param structure The symbolic event structure
    @param write The write event label
    @param read The read event label
    @return [true] if condition holds, [false] otherwise *)
val dslwb :
  ?exclude:int uset ->
  ?state:expr list ->
  symbolic_event_structure ->
  int ->
  int ->
  bool

(** [structure] Get PPO relation from initial events and to terminal events.

    The PPO relation is initialized by relating all initial events and terminal
    events to other events along program order edges.

    @param structure The symbolic event structure
    @return A set of pairs of event labels representing the initial PPO relation
*)
val init_ppo : symbolic_event_structure -> (int * int) uset

(** [structure e] Get symbols associated with events in a loop.

    The function retrieves the set of symbols associated with the event e which
    have been read before the loop of the event e.

    @param structure The symbolic event structure
    @param loop_id The identifier of the loop
    @return A set of symbol names associated with events in the specified loop
*)
val symbols_in_loop : symbolic_event_structure -> int -> string uset
