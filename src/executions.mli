open Types

(** Execution generation for symbolic memory model checking *)

module Execution : sig
  type t = symbolic_execution

  val equal : t -> t -> bool
  val contains : t -> t -> bool
  val to_string : t -> string
end

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
