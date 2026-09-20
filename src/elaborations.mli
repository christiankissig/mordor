(** Elaboration algorithms for symbolic event structures.

    Transforms and refines justifications by value assignment, forwarding,
    lifting and weakening, iterated to a fixed point.

    This interface pins the surface the rest of the code base uses today, ahead
    of the bottom-up refactor: the pipeline step, and the elaboration operators
    the unit tests exercise one at a time. The fixed-point driver itself
    ([batch_elaborations], [generate_justifications]) has no caller outside the
    module and is internal. *)

open Context
open Forwarding
open Types
open Uset

(** {1 Foundational Types} *)

(** Elaboration operation, recorded for tracing. *)
type op

(** Thread-safe table of the operations performed on each justification. *)
module OpTrace : sig
  type 'a t

  (** [create n] is an empty trace with initial capacity [n]. *)
  val create : int -> 'a t
end

(** Elaboration context: the event structure being elaborated and the state
    shared across elaboration rounds. *)
type context = {
  structure : symbolic_event_structure;
      (** The symbolic event structure being elaborated. *)
  fwd_es_ctx : Forwarding.event_structure_context;
  fj : (int * int) USet.t;  (** Fork-join edges that constrain forwarding. *)
  op_trace : op OpTrace.t;
      (** Operations already performed on justifications, to avoid redundancy.
      *)
}

(** [pred elab_ctx ctx p ?ppo ()] is the predecessor function: it maps each
    event to its set of immediate predecessors in the preserved program order.

    @param ctx Optional forwarding context for computing PPO.
    @param p Optional predicate list for computing PPO.
    @param ppo Optional pre-computed PPO relation to avoid recomputation. *)
val pred :
  context ->
  ForwardingContext.t option ->
  expr list option ->
  ?ppo:(int * int) uset ->
  unit ->
  int ->
  int USet.t

(** [pre_justifications structure] is the initial pre-justifications for the
    write, allocation and free events of [structure], each with an empty
    forwarding context. *)
val pre_justifications : symbolic_event_structure -> justification list

(** {1 Value Assignment Elaboration} *)

module ValueAssignElab : sig
  (** [elab elab_ctx just] finds a satisfying model for [just] and assigns
      concrete values to symbolic write values where possible. *)
  val elab : context -> justification -> justification list
end

(** {1 Forwarding Elaboration} *)

module ForwardElab : sig
  (** [fprime elab_ctx pred_fn ppo_loc just e1 e2] is the forwarding prime
      condition: [e1] and [e2] are ordered in [ppo_loc], [e1] is a predecessor
      of [e2], and their locations are equal under [just]'s predicates. *)
  val fprime :
    context ->
    (int -> int USet.t) ->
    (int * int) USet.t ->
    justification ->
    int ->
    int ->
    bool

  (** [fwd elab_ctx pred_fn ctx ppo_loc just] is the set of forwarding edges
      between write/read events satisfying {!fprime}. *)
  val fwd :
    context ->
    (int -> int USet.t) ->
    'a ->
    (int * int) USet.t ->
    justification ->
    (int * int) USet.t

  (** [we elab_ctx pred_fn ctx ppo_loc just] is the set of write-exclusion edges
      between write events. *)
  val we :
    context ->
    (int -> int USet.t) ->
    'a ->
    (int * int) USet.t ->
    justification ->
    int URelation.t

  (** [elab elab_ctx just] extends [just] by every valid forwarding and
      write-exclusion edge, each validated for consistency before it is added.
  *)
  val elab : context -> justification -> justification list
end

(** {1 Lifting Elaboration} *)

module LiftElab : sig
  (** [elab ctx j1 j2] lifts justifications [j1] and [j2] of conflicting writes:
      it finds the relabelings that make them equivalent and produces the lifted
      justifications. *)
  val elab : context -> justification -> justification -> justification list

  (** [find_distinguishing_predicate p1 p2] finds a predicate that is positive
      in [p1] and negative in [p2], or vice versa, along with the common
      predicates. Both lists are in CNF.
      @return [Some (distinguishing, common)] if found, [None] otherwise. *)
  val find_distinguishing_predicate :
    expr list -> expr list -> (expr list * expr list) option

  (** [generate_relabelings ctx j1 j2 ppo1 ppo2 con1 con2] is every valid symbol
      relabeling that could make [j1] and [j2] equivalent under their respective
      PPO relations. *)
  val generate_relabelings :
    context ->
    justification ->
    justification ->
    (int * int) USet.t ->
    (int * int) USet.t ->
    ForwardingContext.t ->
    ForwardingContext.t ->
    (string, string) Hashtbl.t uset
end

(** {1 Weakening Elaboration} *)

module WeakElab : sig
  (** [elab elab_ctx just] removes from [just] the predicates implied by
      program-wide guarantees. *)
  val elab : context -> justification -> justification list
end

(** {1 Pipeline Step} *)

(** [step_generate_justifications ?collapse_forwarding lwt_ctx] takes the event
    structure from the context, initialises the forwarding context if necessary,
    and generates the justifications. *)
val step_generate_justifications :
  ?collapse_forwarding:bool -> mordor_ctx Lwt.t -> mordor_ctx Lwt.t
