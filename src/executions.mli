open Types
open Eventstructures

(** Execution generation for symbolic memory model checking *)

module Execution : sig
  type t = symbolic_execution

  val contains : t -> t -> bool
  val to_string : t -> string
end

(** {1 Types} *)

(** Result of freezing a justification combination with an RF relation *)
type freeze_result = {
  e : int uset;  (** Event set *)
  dp : (int * int) uset;  (** Dependency relation *)
  ppo : (int * int) uset;  (** Preserved program order *)
  rf : (int * int) uset;  (** Reads-from relation *)
  rmw : (int * int) uset;  (** Read-modify-write pairs *)
  pp : expr list;  (** Path predicates *)
  conds : expr list;  (** Combined conditions *)
}

(** [disjoint (loc1, val1) (loc2, val2)] creates a disjoint predicate for two
    (location, value) pairs. Returns an expression asserting that [loc1 ≠ loc2].
*)
val disjoint : expr * expr -> expr * expr -> expr

(** {1 RF Validation} *)

(** [validate_rf structure path ppo dp j_list pp p_combined rf] validates a
    reads-from relation for a justification combination.

    Performs multiple checks:
    - RF edges are valid (elided RF subset of RF)
    - No downward-closed same-location writes before reads
    - Predicates are satisfiable
    - All constraints are met

    @param structure Symbolic event structure
    @param path Path information
    @param ppo Preserved program order relation
    @param dp Dependency relation (as hashtable)
    @param j_list List of justifications
    @param pp Path predicates
    @param p_combined Combined predicates
    @param rf Reads-from relation to validate
    @return [Lwt.t] of [Some freeze_result] if valid, [None] otherwise *)
val validate_rf :
  Types.symbolic_event_structure ->
  path_info ->
  (int * int) Uset.USet.t ->
  (int * int) Uset.USet.t ->
  (int * int) Uset.USet.t ->
  Types.justification list ->
  Types.expr list ->
  Types.expr list ->
  int Uset.URelation.t ->
  freeze_result option Lwt.t

(** {1 Freeze Function Creation} *)

(** [create_freeze structure path j_list init_ppo statex] creates a freeze
    function that validates RF sets for a justification combination.

    The freeze function encapsulates all the constraints from the justifications
    and path predicates, and can be called with different RF relations to check
    validity.

    @param structure Symbolic event structure
    @param path Path information
    @param j_list List of justifications for writes in path
    @param init_ppo Initial preserved program order
    @param statex State predicates
    @return [Lwt.t] of [Some freeze_fn] if valid combination, [None] otherwise

    The returned freeze function has type:
    [(int * int) uset -> freeze_result option Lwt.t] *)
val freeze :
  symbolic_event_structure ->
  path_info ->
  justification list ->
  (int * int) uset ->
  expr list ->
  elided:int uset ->
  constraints:expr list ->
  freeze_result list Lwt.t

(** {1 Justification Combinations} *)

(** [build_justcombos structure paths init_ppo statex justmap] builds all valid
    justification combinations for all paths.

    For each path: 1. Filters to write events in the path 2. Finds compatible
    justification combinations 3. Creates freeze functions for each combination

    @param structure Symbolic event structure
    @param paths List of all paths
    @param init_ppo Initial preserved program order
    @param statex State predicates
    @param justmap Map from write labels to justifications
    @return [Lwt.t] of stream of (path, justification list) pairs *)
val build_justcombos :
  Types.symbolic_event_structure ->
  path_info list ->
  (int * int) Uset.USet.t ->
  Types.expr list ->
  (int, Types.justification list) Hashtbl.t ->
  (path_info * Types.justification list) Lwt_stream.t

(** {1 Main Execution Generation} *)

(** [generate_executions structure final_justs statex init_ppo
     ~include_dependencies ~restrictions] generates all valid executions for the
    given symbolic event structure.

    This is the main entry point for execution generation. It: 1. Generates all
    paths through the control flow 2. Computes initial RF candidates 3. Builds
    justification combinations 4. Enumerates RF relations and validates each 5.
    Converts valid freeze results to executions 6. Filters through coherence
    checking

    @param structure Symbolic event structure with PO, RMW, etc.
    @param final_justs Set of final justifications for writes
    @param statex State predicates
    @param init_ppo Initial preserved program order
    @param include_dependencies Whether to include dependency calculations
    @param restrictions Coherence model restrictions
    @return [Lwt.t] of list of valid symbolic executions *)
val generate_executions :
  symbolic_event_structure ->
  justification uset ->
  expr list ->
  (int * int) uset ->
  include_dependencies:bool ->
  restrictions:Coherence.restrictions ->
  symbolic_execution list Lwt.t
