(** Coherence checking for memory models.

    This interface pins the surface the rest of the code base uses today, ahead
    of the bottom-up refactor: the model signature and registry, the entry
    points {!Executions} calls, and the models and shared checks the unit tests
    instantiate directly. Every other model is reached through
    {!ModelRegistry.lookup} by name, and the search over coherence orders is
    internal. *)

open Types
open Uset

(** S4 (measure the waste ratio): when enabled, emit pipeline-stage and
    per-location coherence-permutation counts at info level. Off by default;
    enabled via the [MORDOR_S4_COUNTERS] environment variable or by setting this
    ref. Shared by {!Executions}. *)
val s4_counters : bool ref

(** S6 (branch and bound over coherence orders): when [prune] is set, the search
    abandons a partial coherence order the model already rejects. Enabled via
    [MORDOR_S6_PRUNE]; the counters record what the search did.

    Sound only for a model whose violations grow with co. od-lso's do not: its
    C++11 release sequence subtracts [coe;coe], so more co can mean less hb.
    Slower than the exhaustive search on every corpus measured; see
    spike/s6_coherence_bb/RESULTS.md on the bottom-up-refactor branch. *)
module S6 : sig
  val prune : bool ref
  val min_leaves : int ref
  val partial_checks : int ref
  val pruned : int ref
  val leaf_checks : int ref
  val reset : unit -> unit
end

(** {1 Core Abstractions} *)

module type MEMORY_MODEL = sig
  type cache
  type config

  val name : string
  val default_config : config

  val build_cache :
    symbolic_execution ->
    symbolic_event_structure ->
    ((int * int) uset -> (int * int) uset) ->
    cache

  val check_coherence : cache -> (int * int) uset -> bool

  (** One candidate coherence order, with the cache it is checked against and
      the relations the axioms derive from the two. Each is computed once, and
      only if an axiom asks for it. *)
  type candidate

  val candidate : cache -> (int * int) uset -> candidate

  (** The model's axioms, by name, in the order [check_coherence] asks them:
      [check_coherence cache co] holds when every one holds of
      [candidate cache co]. Each can be asked on its own. *)
  val axioms : (string * (candidate -> bool)) list

  val check_thin_air : cache -> symbolic_execution -> bool

  (** Whether [check_coherence] reads the coherence order it is given. A model
      whose axioms quantify over orders of their own -- a view per process, an
      arbitration per session -- does not, and the search then asks it once
      rather than once per candidate order. *)
  val uses_co : bool

  (** Whether allocations and deallocations are writes to the coherence order,
      as RC11z makes them. *)
  val orders_allocations : bool

  (** [Error reason] when the model cannot answer for this program at all. It is
      asked once, before any execution is, and the pipeline fails with the
      reason rather than returning a verdict that is not the model's. *)
  val check_program : symbolic_event_structure -> (unit, string) result

  val compute_dependencies :
    symbolic_execution ->
    (int, event) Hashtbl.t ->
    (int * int) uset ->
    int uset ->
    (int, expr list) Hashtbl.t ->
    (int * int) uset
end

(** A model that can be asked about a coherence order while it is being built.

    [start] is what is known before any edge; [extend] adds edges and answers
    [None] once no completion can be coherent, so that a search can stop there;
    [finalize] decides the complete order. {!Incremental} is the adapter every
    model has until it says more: it never prunes, and decides at the end with
    {!MEMORY_MODEL.check_coherence}. *)
module type INCREMENTAL_MODEL = sig
  include MEMORY_MODEL

  type partial

  val start : cache -> partial
  val extend : partial -> (int * int) uset -> partial option
  val finalize : partial -> (int * int) uset -> bool
end

(** The default adapter: nothing is known of a partial order but the cache. *)
module Incremental (M : MEMORY_MODEL) :
  INCREMENTAL_MODEL with type cache = M.cache and type partial = M.cache

(** {1 Shared Logic} *)

module ModelUtils : sig
  (** Event matching, shared across all models: the identity pairs over the
      events of [e] with the given type, access mode, mode comparison operator
      and second mode. *)
  val match_events :
    (int, event) Hashtbl.t ->
    int uset ->
    event_type ->
    mode option ->
    string option ->
    mode option ->
    (int * int) uset
end

module CoherenceChecks : sig
  (** Coherence axiom check: [hb;eco ∪ hb] is irreflexive, where [eco] defaults
      to [(rf ∪ co ∪ rb)⁺] for [rb = rf⁻¹;co]. *)
  val coherence_axiom :
    ?eco:'a URelation.t ->
    rf:('a * 'a) USet.t ->
    rfi:'a URelation.t ->
    co:'a URelation.t ->
    hb:'a URelation.t ->
    unit ->
    bool
end

(** {1 Memory Model Implementations} *)

module IMM : MEMORY_MODEL

(** RC11 and the models that are configurations of it. *)
module RC11Config : sig
  (** Which release sequence [rs] a model synchronises over.

      - [Rc11]: [[W];(sb ∩ loc)?;[W_rlx⁺];(rf;rmw)*], as herd's [rc11.cat].
      - [Rc17]: [[W_rlx⁺];(rf;rmw)*], C++17's ([rc17.cat]).
      - [Cpp11]: RC11's, less the pairs another thread's write intervenes in
        ([cpp11.cat]). *)
  type release_sequence = Rc11 | Rc17 | Cpp11

  type t = {
    with_consume : bool;
    name : string;
    release_sequence : release_sequence;
    allocations_are_writes : bool;
        (** RC11z: allocations and deallocations are writes to the location they
            allocate or free, ordered by [co] with the stores to it. *)
    no_thin_air : [ `Hb_rf | `Sb_rf ];
        (** [acyclic(hb ∪ rf)], or the literal [acyclic(sb ∪ rf)] of Ou and
            Demsky's load-store ordering. *)
  }

  val default : t
  val with_consume : t
end

module RC11 (_ : sig
  val config : RC11Config.t
end) : MEMORY_MODEL

module Undefined : MEMORY_MODEL

(** {1 Model Selection} *)

type restrictions = { coherent : string }

(** Registry of the memory models, by name. *)
module ModelRegistry : sig
  val lookup : string -> (module MEMORY_MODEL) option

  (** [lookup_incremental name] is the model [name] as an {!INCREMENTAL_MODEL}:
      the one registered for it, or else {!Incremental} of the model. *)
  val lookup_incremental : string -> (module INCREMENTAL_MODEL) option

  (** The names models are registered under. *)
  val names : unit -> string list
end

(** {1 Coherence Checking Entry Points} *)

(** [check_for_coherence structure execution restrictions] is the coherence
    order under which the model admits [execution], or [None] if it does not. *)
val check_for_coherence :
  symbolic_event_structure ->
  symbolic_execution ->
  restrictions ->
  int URelation.t option

(** [rejected_by_one_location structure execution restrictions]: the model
    rejects [execution] whatever the coherence order at other locations: its
    thin-air check fails, or some location has no po-respecting order the
    axioms accept with every other location unordered. For a model whose
    violations only grow with co, rf and hb, it holds of every completion of a
    partial execution it holds of, when the completion's predicates include the
    partial one's. *)
val rejected_by_one_location :
  ?eqlocs:(int * int) uset ->
  symbolic_event_structure ->
  symbolic_execution ->
  restrictions ->
  bool

(** [location_equality structure execution] is the pairs of [execution]'s
    events whose locations its predicates entail equal. More predicates only
    add pairs, so the relation of a partial execution's predicates can stand in
    for a completion's in {!rejected_by_one_location}. *)
val location_equality :
  symbolic_event_structure -> symbolic_execution -> (int * int) uset

(** [rejects_partial_executions name]: {!rejected_by_one_location} holding of a
    partial execution means model [name] rejects every completion of it. True
    of every registered model but od-lso (S6). *)
val rejects_partial_executions : string -> bool

(** [check_model_program structure name] fails, with the model's reason, when
    the coherence model [name] cannot answer for the program [structure] is the
    event structure of. Unknown names are left to {!check_for_coherence}. *)
val check_model_program : symbolic_event_structure -> string -> unit
