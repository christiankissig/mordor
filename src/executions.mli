open Context
open Eventstructures
open Types
open Uset

(** {1 Compute Abstraction} *)

(** Abstract parallel computation strategy.

    Encapsulates the choice between single-threaded and parallel execution.
    Pipeline stages use [compute_fn] to map a pure worker over a list of items.

    Use [sequential_compute] for single-threaded operation, or
    [parallel_compute pool] to dispatch work across a domain pool. *)
type compute_fn = { run : 'a 'b. ('a -> 'b) -> 'a list -> 'b list Lwt.t }

(** [sequential_compute] runs items sequentially with no parallelism. *)
val sequential_compute : compute_fn

(** [parallel_compute pool] dispatches items to [pool] via [Lwt_domain.detach].
*)
val parallel_compute : Lwt_domain.pool -> compute_fn

(** {1 Execution Generation for Symbolic Memory Model Checking}

    This module provides facilities for generating and analyzing symbolic
    executions. *)

(** {2 Validation} *)

(** The checks an execution's read-from relation is validated by, over explicit
    inputs, as {!Freeze.freeze} asks them.

    Each has a [_delta] form, shaped for a fragment merge that knows what it is
    adding to relations already checked: the plain arguments are what was
    checked, and the [d] arguments what is added. Those are stubs: they check
    the union from scratch. *)
module Validation : sig
  (** [rf_respects_ppo ~rf ~ppo]: every rf edge [(w, r)] that is in [ppo] has
      [r] among [w]'s successors in [ppo]. As stated this never fails. *)
  val rf_respects_ppo : rf:(int * int) uset -> ppo:(int * int) uset -> bool

  val rf_respects_ppo_delta :
    rf:(int * int) uset ->
    ppo:(int * int) uset ->
    drf:(int * int) uset ->
    dppo:(int * int) uset ->
    bool

  (** [rf_not_elided ~rf ~delta]: no read reads from a write that [delta], the
      forwarding and write-elision edges, elides. *)
  val rf_not_elided : rf:(int * int) uset -> delta:(int * int) uset -> bool

  val rf_not_elided_delta :
    rf:(int * int) uset ->
    delta:(int * int) uset ->
    drf:(int * int) uset ->
    ddelta:(int * int) uset ->
    bool

  (** [rf_total ~rf ~reads ~delta]: every read of [reads] that [delta] does not
      elide reads from something. *)
  val rf_total :
    rf:(int * int) uset -> reads:int uset -> delta:(int * int) uset -> bool

  val rf_total_delta :
    rf:(int * int) uset ->
    reads:int uset ->
    delta:(int * int) uset ->
    drf:(int * int) uset ->
    dreads:int uset ->
    ddelta:(int * int) uset ->
    bool

  (** [rhb ~dp ~ppo ~rf] is reads-happen-before, [dp ∪ ppo ∪ rf]. *)
  val rhb :
    dp:(int * int) uset ->
    ppo:(int * int) uset ->
    rf:(int * int) uset ->
    (int * int) uset

  (** [rhb_acyclic rhb]: no event reads-happens-before itself. *)
  val rhb_acyclic : (int * int) uset -> bool

  val rhb_acyclic_delta : (int * int) uset -> drhb:(int * int) uset -> bool

  (** [rf_closes_rhb_cycle ~succ ~rf (w, r)]: adding the read-from edge
      [(w, r)] closes a cycle, [r] reaching [w] through [succ], the successors
      in [dp ∪ ppo], and [rf], the edges already chosen as [(read, write)]
      pairs. What {!rhb_acyclic} rejects of every completion, decided as each
      edge is chosen. *)
  val rf_closes_rhb_cycle :
    succ:(int, int uset) Hashtbl.t -> rf:(int * int) list -> int * int -> bool
end

(** {2 Freeze Module} *)

module FreezeResult : sig
  (** Freeze result type containing execution relations and constraints. *)
  type t = {
    e : int uset;  (** Event set. *)
    dp : (int * int) uset;  (** Dependency relation. *)
    ppo : (int * int) uset;  (** Preserved program order. *)
    rf : (int * int) uset;  (** Read-from relation. *)
    rmw : (int * int) uset;  (** Read-modify-write pairs. *)
    fwd : (int * int) uset;
        (** Forwarding edges of the justification combination this came from.
            Outside {!equal}, {!hash} and {!contains}, so results that agree on
            the relations above still deduplicate; the survivor absorbs the
            others' contexts. *)
    we : (int * int) uset;  (** Write elisions, on the same terms as [fwd]. *)
    mutable justs : justification list;
        (** The justification combination this result was frozen from, on the
            same terms as [fwd]. *)
    pp : expr list;  (** Path predicates that must be satisfied. *)
    conds : expr list;  (** Additional conditions. *)
  }

  (** [merge_justs kept fr] folds [fr]'s justifications into [kept]'s, skipping
      ones it already has. *)
  val merge_justs : t -> t -> unit
end

module Freeze : sig
  (** What an enumeration of read-from relations ranges over: the reads it
      chooses a write for, and the writes it chooses among. *)
  type scope = { reads : int uset; writes : int uset }

  (** [path_scope structure path ~elided] is the scope of a whole path: every
      read of [path] that is not elided, and every write and free of it that is
      not, with the initial write. *)
  val path_scope :
    symbolic_event_structure -> path_info -> elided:int uset -> scope

  (** [compute_path_rf structure path ~scope ~elided ~constraints statex ppo dp
       p_combined] is every read-from relation, as lists of [(read, write)]
      pairs, that gives each read of [scope] one write of [scope] -- at a
      location it can share, not po-after it and not shadowed -- consistent with
      [p_combined]. {!freeze} asks for the scope of the whole path. *)
  val compute_path_rf :
    symbolic_event_structure ->
    path_info ->
    scope:scope ->
    elided:int uset ->
    constraints:expr list ->
    expr list ->
    (int * int) uset ->
    (int * int) uset ->
    expr list ->
    (int * int) list list

  (** [fold_path_rf ... f init] folds [f] over the relations
      {!compute_path_rf} lists, as each is built, depth-first and in a different
      order: [f acc indices rf], where
      {!Algorithms.ListMapCombinationBuilder.compare_build_order} on [indices]
      gives back the list's order. [shuffle] and [inspect] are S10's: each
      read's alternatives in a random order, and a look at them. *)
  val fold_path_rf :
    ?shuffle:Random.State.t ->
    ?inspect:((int, int list) Hashtbl.t -> int list -> unit) ->
    symbolic_event_structure ->
    path_info ->
    scope:scope ->
    elided:int uset ->
    constraints:expr list ->
    expr list ->
    (int * int) uset ->
    (int * int) uset ->
    expr list ->
    ('a -> int list -> (int * int) list -> 'a) ->
    'a ->
    'a

  (** [freeze structure context path justs statex ~elided ~constraints
       ~include_rf] freezes executions to dependency relations.

      @param structure
        The symbolic event structure containing events and metadata
      @param context Event structure context with forwarding information
      @param path
        Information about the path through the event structure, including event
        sequence and predicates
      @param justs
        List of justifications for symbolic reads, representing possible values
        read from memory locations
      @param statex
        List of state predicates (expressions) that must hold for the execution
        to be valid
      @param elided
        Set of event labels that are elided (not included in the final
        execution)
      @param constraints
        List of additional constraints (expressions) that must hold for the
        execution to be valid
      @param include_rf
        Whether to include the reads-from relation in the output (default is
        typically true)
      @return Lwt promise resolving to a list of frozen execution candidates *)
  val freeze :
    symbolic_event_structure ->
    Forwarding.event_structure_context ->
    path_info ->
    justification list ->
    expr list ->
    elided:int USet.t ->
    constraints:expr list ->
    include_rf:bool ->
    FreezeResult.t list

  (** [freeze_dp structure justs] computes the semantic dependency relation for
      a justification.

      This function analyzes the justifications and event structure to determine
      the data and control dependencies between events in the frozen execution.

      @param structure
        The symbolic event structure containing events and metadata
      @param justs
        List of justifications for symbolic reads, representing possible values
        read from memory locations
      @return Set of event ID pairs representing the dependency relations *)
  val freeze_dp :
    symbolic_event_structure -> justification -> (int * int) USet.t
end

(** {2 Justification Combinations} *)

(** [justifiable structure path] is every event of [path] a justification is
    chosen for: its writes, allocations and frees. *)
val justifiable : symbolic_event_structure -> path_info -> int uset

(** [compute_justification_combinations compute structure paths ~scope justmap]
    is, for each of [paths], every combination of one justification from
    [justmap] for each event of [scope path] that the combination checks accept,
    paired with the path. {!generate_executions} asks for the scope
    {!justifiable}. *)
val compute_justification_combinations :
  compute_fn ->
  symbolic_event_structure ->
  path_info list ->
  scope:(path_info -> int uset) ->
  (int, justification list) Hashtbl.t ->
  (path_info * justification list) list Lwt.t

(** {2 Execution Module} *)

module Execution : sig
  (** Type representing a symbolic execution.

      A symbolic execution captures a particular ordering of memory events
      (reads, writes, fences) that is consistent with the program order and
      memory model constraints. *)
  type t = symbolic_execution

  (** [equal exec1 exec2] checks if two executions are equivalent.

      @param exec1 First execution to compare
      @param exec2 Second execution to compare
      @return [true] if the executions are equal, [false] otherwise *)
  val equal : t -> t -> bool

  (** [contains exec1 exec2] checks if [exec1] contains all events and orderings
      of [exec2].

      This is useful for determining if one execution is a refinement or
      extension of another.

      @param exec1 The potentially containing execution
      @param exec2 The execution to check for containment
      @return [true] if [exec1] contains [exec2], [false] otherwise *)
  val contains : t -> t -> bool

  (** [to_string exec] converts an execution to a human-readable string
      representation.

      The string typically includes the reads-from relation, coherence order,
      and other relevant orderings.

      @param exec The execution to convert
      @return String representation of the execution *)
  val to_string : t -> string

  (** [get_relation name structure exec] retrieves a named relation from the
      execution.

      Relations typically include:
      - "rf" (reads-from)
      - "co" (coherence order)
      - "fr" (from-reads)
      - "po" (program order)
      - and various model-specific relations

      @param name The name of the relation to retrieve
      @param structure The symbolic event structure containing event metadata
      @param exec The execution containing the relation
      @return Set of integer pairs representing the relation as event ID tuples
  *)
  val get_relation :
    string -> symbolic_event_structure -> symbolic_execution -> (int * int) uset

  (** [get_writes_in_rhb_order structure exec] returns write events ordered by
      the "release-happens-before" relation.

      This ordering is crucial for determining visibility and synchronization in
      relaxed memory models.

      @param structure The symbolic event structure
      @param exec The execution to query
      @return List of write event IDs in rhb order *)
  val get_writes_in_rhb_order : symbolic_event_structure -> t -> int list
end

(** {2 Main Execution Generation} *)

(** [generate_executions ?include_rf structure context final_justs statex
     ~restrictions] generates all valid executions for the given symbolic event
    structure.

    This is the primary entry point for execution enumeration. The generation
    process:

    + Enumerates all paths through the control flow graph
    + Computes initial reads-from (RF) candidate sets
    + Builds combinations of justifications for symbolic reads
    + Enumerates all possible RF relations
    + Validates each candidate execution against memory model constraints
    + Converts valid frozen results to complete executions
    + Performs coherence checking to filter out invalid orderings

    @param include_rf
      Whether to include reads-from relation in the output (default is typically
      true)
    @param structure
      Symbolic event structure containing program order (PO), read-modify-write
      (RMW) pairs, and event metadata
    @param context Event structure context with forwarding information
    @param final_justs
      Set of final justifications for write events, representing possible values
      written to memory locations
    @param statex List of state predicates (expressions) that must hold
    @param restrictions
      Coherence model restrictions specifying the memory model (e.g., SC, TSO,
      ARM, POWER)
    @param compare_models
      Further coherence models to check every execution against. They filter
      nothing.
    @param admissions
      Filled with, for each execution reaching the coherence stage, the models
      of [compare_models] that admit it, including executions [restrictions]
      rejects
    @return Lwt promise resolving to a list of valid symbolic executions *)
val generate_executions :
  ?include_rf:bool ->
  ?compute:compute_fn ->
  ?compare_models:string list ->
  ?admissions:(int, string list) Hashtbl.t ->
  ?model_executions:(string, symbolic_execution list) Hashtbl.t ->
  symbolic_event_structure ->
  Forwarding.event_structure_context ->
  justification list ->
  expr list ->
  restrictions:Coherence.restrictions ->
  symbolic_execution list Lwt.t

(** [calculate_dependencies ?include_rf structure final_justs context
     ~exhaustive ~restrictions] computes dependency information for symbolic
    executions.

    This function analyzes data dependencies, address dependencies, and control
    dependencies between events. The [exhaustive] flag controls whether to
    explore all possible dependency graphs or use heuristics for efficiency.

    Dependencies are crucial for:
    - Determining which events must be ordered
    - Computing happens-before relations
    - Validating compiler optimizations
    - Model-specific constraint checking

    @param include_rf
      Whether to include reads-from relation in dependency analysis
    @param structure The symbolic event structure to analyze
    @param final_justs Set of justifications for writes
    @param context Event structure context with forwarding information
    @param exhaustive
      If [true], exhaustively explore all dependency combinations; if [false],
      use pruning heuristics for better performance
    @param restrictions Memory model restrictions
    @return
      Lwt promise resolving to executions with computed dependency information
*)
val calculate_dependencies :
  ?include_rf:bool ->
  ?num_threads:int ->
  ?compare_models:string list ->
  ?admissions:(int, string list) Hashtbl.t ->
  ?model_executions:(string, symbolic_execution list) Hashtbl.t ->
  symbolic_event_structure ->
  justification list ->
  Forwarding.event_structure_context ->
  exhaustive:bool ->
  restrictions:Coherence.restrictions ->
  symbolic_execution list Lwt.t

(** [step_calculate_dependencies ctx] performs one step of dependency
    calculation within a Mordor context.

    This function is part of the incremental execution generation pipeline. It
    processes the Mordor (symbolic execution) context to advance the state of
    dependency calculation, typically as part of an iterative solver loop.

    The function operates within the Lwt monad to support asynchronous
    computation, which is important for responsive verification of large
    concurrent programs.

    @param ctx
      Lwt promise of a Mordor context containing partial execution state
    @return
      Lwt promise of an updated Mordor context with advanced dependency state *)
val step_calculate_dependencies : mordor_ctx Lwt.t -> mordor_ctx Lwt.t
