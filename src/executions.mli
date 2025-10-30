open Types

(** Execution generation for symbolic memory model checking *)

(** {1 Types} *)

(** Path information containing event sequence and predicates *)
type path_info = {
  path : int list;  (** Sequence of event labels in the path *)
  p : expr list list;  (** List of predicate lists for path constraints *)
}

(** Result of freezing a justification combination with an RF relation *)
type freeze_result = {
  justs : justification list;  (** Justifications for writes *)
  e : int uset;  (** Event set *)
  dp : (int * int) uset;  (** Dependency relation *)
  ppo : (int * int) uset;  (** Preserved program order *)
  rf : (int * int) uset;  (** Reads-from relation *)
  rmw : (int * int) uset;  (** Read-modify-write pairs *)
  pp : expr list list;  (** Path predicates *)
  conds : expr list;  (** Combined conditions *)
}

(** {1 Utility Functions} *)

(** [disjoint (loc1, val1) (loc2, val2)] creates a disjoint predicate for two
    (location, value) pairs. Returns an expression asserting that [loc1 ≠ loc2].
*)
val disjoint : expr * expr -> expr * expr -> expr

(** [origin events read_events malloc_events symbol] finds the origin event of a
    symbol. First searches in read events, then in malloc events.
    @param events Hash table of all events
    @param read_events Set of read event labels
    @param malloc_events Set of malloc event labels
    @param symbol Symbol name to find
    @return [Some event_label] if found, [None] otherwise *)
val origin :
  (int, event) Hashtbl.t -> int uset -> int uset -> string -> int option

(** {1 Path Generation} *)

(** [gen_paths events structure restrict] generates all execution paths through
    the control flow structure.

    For each branch event, generates separate paths for both branch outcomes.
    Paths are built recursively from root events (those with no predecessors).

    @param events Hash table of all events
    @param structure Symbolic event structure with PO and constraints
    @param restrict Restriction map for events
    @return List of path information records
    @raise Failure if no events in structure or branch has invalid successors *)
val gen_paths :
  (int, event) Hashtbl.t ->
  symbolic_event_structure ->
  (int, expr list) Hashtbl.t ->
  path_info list

(** {1 Justification Selection} *)

(** [choose justmap path_events] selects compatible justifications for events in
    a path.

    Chooses one justification per write event such that the forwarding (fwd) and
    write-elision (we) relations are compatible (no conflicts).

    @param justmap Map from event labels to lists of justifications
    @param path_events Set of event labels in the path
    @return List of compatible justification combinations *)
val choose :
  (int, justification list) Hashtbl.t -> int uset -> justification list list

(** {1 RF Validation} *)

(** [validate_rf events structure e elided elided_rf ppo_loc ppo_loc_tree dp
     dp_ppo j_list pp p_combined rf write_events read_events po] validates a
    reads-from relation for a justification combination.

    Performs multiple checks:
    - RF edges are valid (elided RF subset of RF)
    - No downward-closed same-location writes before reads
    - Predicates are satisfiable
    - All constraints are met

    @return [Lwt.t] of [Some freeze_result] if valid, [None] otherwise *)
val validate_rf :
  (int, event) Hashtbl.t ->
  symbolic_event_structure ->
  int uset ->
  int uset ->
  (int * int) uset ->
  (int * int) uset ->
  (int, int uset) Hashtbl.t ->
  (int * int) uset ->
  (int * int) uset ->
  justification list ->
  expr list list ->
  expr list ->
  (int * int) uset ->
  int uset ->
  int uset ->
  (int * int) uset ->
  freeze_result option Lwt.t

(** {1 Freeze Function Creation} *)

(** [create_freeze events structure path j_list write_events read_events
     init_ppo statex] creates a freeze function that validates RF sets for a
    justification combination.

    The freeze function encapsulates all the constraints from the justifications
    and path predicates, and can be called with different RF relations to check
    validity.

    @param events Hash table of all events
    @param structure Symbolic event structure
    @param path Path information
    @param j_list List of justifications for writes in path
    @param write_events Set of write event labels
    @param read_events Set of read event labels
    @param init_ppo Initial preserved program order
    @param statex State predicates
    @return [Lwt.t] of [Some freeze_fn] if valid combination, [None] otherwise

    The returned freeze function has type:
    [(int * int) uset -> freeze_result option Lwt.t] *)
val create_freeze :
  (int, event) Hashtbl.t ->
  symbolic_event_structure ->
  path_info ->
  justification list ->
  int uset ->
  int uset ->
  (int * int) uset ->
  expr list ->
  ((int * int) uset -> freeze_result option Lwt.t) option Lwt.t

(** {1 Justification Combinations} *)

(** [build_justcombos events structure paths write_events read_events init_ppo
     statex justmap] builds all valid justification combinations for all paths.

    For each path: 1. Filters to write events in the path 2. Finds compatible
    justification combinations 3. Creates freeze functions for each combination

    @param events Hash table of all events
    @param structure Symbolic event structure
    @param paths List of all paths
    @param write_events Set of write event labels
    @param read_events Set of read event labels
    @param init_ppo Initial preserved program order
    @param statex State predicates
    @param justmap Map from write labels to justifications
    @return [Lwt.t] of hash table mapping path event sets to freeze functions *)
val build_justcombos :
  (int, event) Hashtbl.t ->
  symbolic_event_structure ->
  path_info list ->
  int uset ->
  int uset ->
  (int * int) uset ->
  expr list ->
  (int, justification list) Hashtbl.t ->
  (int uset, ((int * int) uset -> freeze_result option Lwt.t) list) Hashtbl.t
  Lwt.t

(** {1 Main Execution Generation} *)

(** [generate_executions events structure final_justs statex e_set po rmw
     write_events read_events init_ppo ~include_dependencies ~restrictions]
    generates all valid executions for the given symbolic event structure.

    This is the main entry point for execution generation. It: 1. Generates all
    paths through the control flow 2. Computes initial RF candidates 3. Builds
    justification combinations 4. Enumerates RF relations and validates each 5.
    Converts valid freeze results to executions 6. Filters through coherence
    checking

    @param events Hash table of all events
    @param structure Symbolic event structure with PO, RMW, etc.
    @param final_justs Set of final justifications for writes
    @param statex State predicates
    @param e_set Set of all event labels
    @param po Program order relation
    @param rmw Read-modify-write relation
    @param write_events Set of write event labels
    @param read_events Set of read event labels
    @param init_ppo Initial preserved program order
    @param include_dependencies Whether to include dependency calculations
    @param restrictions Coherence model restrictions
    @return [Lwt.t] of list of valid symbolic executions *)
val generate_executions :
  (int, event) Hashtbl.t ->
  symbolic_event_structure ->
  justification uset ->
  expr list ->
  int uset ->
  (int * int) uset ->
  (int * int) uset ->
  int uset ->
  int uset ->
  (int * int) uset ->
  include_dependencies:bool ->
  restrictions:Coherence.restrictions ->
  symbolic_execution list Lwt.t
