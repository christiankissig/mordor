open Context
open Eventstructures
open Types
open Uset

(** {1 Execution Generation for Symbolic Memory Model Checking}

    This module provides facilities for generating and analyzing symbolic
    executions. *)

(** {2 Freeze Module} *)

module FreezeResult : sig
  (** Freeze result type containing execution relations and constraints. *)
  type t = {
    e : int uset;  (** Event set. *)
    dp : (int * int) uset;  (** Dependency relation. *)
    ppo : (int * int) uset;  (** Preserved program order. *)
    rf : (int * int) uset;  (** Read-from relation. *)
    rmw : (int * int) uset;  (** Read-modify-write pairs. *)
    pp : expr list;  (** Path predicates that must be satisfied. *)
    conds : expr list;  (** Additional conditions. *)
  }
end

module Freeze : sig
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
    FreezeResult.t list Lwt.t

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
    @return Lwt promise resolving to a list of valid symbolic executions *)
val generate_executions :
  ?include_rf:bool ->
  symbolic_event_structure ->
  Forwarding.event_structure_context ->
  justification uset ->
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
  symbolic_event_structure ->
  justification uset ->
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
