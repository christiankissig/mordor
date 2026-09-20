(** Program interpreter for concurrent programs with memory operations.

    Interprets intermediate representation (IR) programs as symbolic event
    structures, under step-counter, symbolic or generic loop semantics.

    This interface pins the surface the rest of the code base uses today, ahead
    of the bottom-up refactor: the pipeline step, the pieces of interpreter
    state {!Executions} and the unit tests reach for, and nothing else. The
    statement semantics, the loop semantics modules and the terminal-structure
    construction are internal. *)

open Context
open Eventstructures
open Types
open Uset

(** {1 Event and Symbol Allocation} *)

(** Allocator of event labels and fresh symbols.

    One allocator is made for each interpretation and handed down the recursion
    inside {!events_t}, so labels and symbols are fresh within an interpretation
    and start over with the next one. Each thread of a parallel block is
    interpreted with labels of its own and relabelled into place. *)
module Allocator : sig
  type t

  (** [create ()] is an allocator that has handed out nothing. *)
  val create : unit -> t

  (** [next_label t] is the next unused event label, counting from [0]. *)
  val next_label : t -> int

  (** [next_greek t] is the next Greek letter symbol, with a numeric suffix once
      the alphabet is exhausted (e.g. "α", "β", ..., "α1", "β1", ...). *)
  val next_greek : t -> string

  (** [next_zh t] is the next Chinese character symbol, with a numeric suffix
      once the alphabet is exhausted. *)
  val next_zh : t -> string
end

(** {1 Event Structure Tracking} *)

(** The interpreter's working record of an interpretation: every event it has
    created, in the order it created them.

    Events and symbols are enumerated from the start of the program, while event
    structures are constructed from the end, as continuations, so an event is
    labelled and recorded here before the structure it will be prefixed to
    exists. The structure's own tables are built as events are prefixed to it
    and describe the events that made it in, which these tables do not promise.
*)
type events_t = {
  defacto : expr list;  (** Optional de facto constraints from litmus tests. *)
  events : (int, event) Hashtbl.t;  (** Events indexed by label. *)
  origin : (string, int) Hashtbl.t;
      (** Origin mapping for symbols to event labels. *)
  env_by_evt : (int, (string, expr) Hashtbl.t) Hashtbl.t;
      (** Register environment at each event label. *)
  thread_index : (int, int) Hashtbl.t;
      (** Mapping from event labels to thread indices. An event is added to
          thread [0], the thread being interpreted: the program's own outside
          every parallel block, or the fragment's inside one, which relabelling
          moves to the thread's index. *)
  mutable threads_allocated : int;
      (** The last thread index handed out, counting from [1] for the first
          thread of the first parallel block interpreted, nested ones included.
      *)
  loop_indices : (int, int list) Hashtbl.t;
      (** Mapping from event labels to loop indices. *)
  loop_conditions : (int, expr list) Hashtbl.t;
      (** Mapping from a loop index to the continuation guards recorded for it,
          one per interpreted occurrence of the loop. Used with symbolic loop
          semantics. *)
  source_spans : (int, source_span) Hashtbl.t;
      (** Mapping from event labels to source code spans. *)
  globals : string USet.t;  (** Set of global variable names. *)
  ubopt : bool;  (** Whether the model exploits undefined behaviour. *)
  alloc : Allocator.t;  (** Source of event labels and fresh symbols. *)
}

(** [create_events ?ubopt defacto] is a fresh [events_t] with empty tables and
    an allocator of its own. *)
val create_events : ?ubopt:bool -> expr list -> events_t

(** Prefix of the environment keys under which a path's undefined-behaviour
    assumptions are recorded. A key carrying this prefix is not a register, and
    {!Executions} keeps such keys out of an execution's final environment. *)
val ub_fact_prefix : string

(** [add_event events event env annotation] adds [event] to [events] under the
    next label, recording [env] and the annotation's source span, thread and
    loop context.
    @return The event with its newly assigned label. *)
val add_event :
  events_t -> event -> (string, expr) Hashtbl.t -> ir_node_ann -> event

(** {1 Interpretation} *)

(** [interpret_statements stmts env phi events] interprets [stmts] with no
    special handling of while loops: every statement except an unbounded loop,
    which is left uninterpreted.

    @param env The initial register environment.
    @param phi The initial path condition.
    @param events The global events structure. *)
val interpret_statements :
  ir_node list ->
  (string, expr) Hashtbl.t ->
  expr list ->
  events_t ->
  SymbolicEventStructure.t

(** [interpret_generic ?ubopt ~stmt_semantics ~defacto ~constraints stmts]
    interprets [stmts] under [stmt_semantics], prefixes the initial event and
    attaches the tables of the events context.
    @return The symbolic event structure and the source spans table. *)
val interpret_generic :
  ?ubopt:bool ->
  stmt_semantics:
    ('a ->
    (string, expr) Hashtbl.t ->
    'b list ->
    events_t ->
    SymbolicEventStructure.t
    ) ->
  defacto:expr list ->
  constraints:'c ->
  'a ->
  symbolic_event_structure * (int, source_span) Hashtbl.t

(** [interpret ?ubopt ?defacto ?constraints stmts] is {!interpret_generic} under
    {!interpret_statements}. *)
val interpret :
  ?ubopt:bool ->
  ?defacto:expr list option ->
  ?constraints:'a option ->
  ir_node list ->
  symbolic_event_structure * (int, source_span) Hashtbl.t

(** {1 Spike Instrumentation} *)

(** S8 (#20): with [compositional_po_iter] set, each interpreted occurrence of a
    loop produces the [po_iter] pairs of its own body, and symbolic loop
    semantics keeps those rather than rebuilding [po_iter] from [loop_indices].
    Enabled via [MORDOR_S8_COMPOSITIONAL_PO_ITER]. *)
module S8 : sig
  val compositional_po_iter : bool ref
end

(** {1 Pipeline Step} *)

(** Main interpretation pipeline step. Selects the loop semantics from the
    context's options and interprets the program. *)
val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t
