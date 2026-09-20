(** Assertion checking and refinement for symbolic memory model checking.

    Validates litmus test assertions against generated executions: outcome
    assertions (allow/forbid with conditions), undefined behaviour detection
    (use-after-free, unbounded pointer dereference), and refinement checking
    between programs.

    This interface pins the surface the rest of the code base uses today, ahead
    of the bottom-up refactor: the pipeline steps, the assertion entry point and
    its result, and the few helpers the parser, the visualiser and the unit
    tests reach for. The checkers themselves -- UB validation, execution
    analysis, per-execution checking, refinement -- are internal. *)

open Context
open Executions
open Types

(** {1 Assertion Result Type} *)

(** Result of checking an assertion against executions. *)
type assertion_result = {
  valid : bool;  (** Whether the assertion holds for all checked executions. *)
  ub : bool;  (** Whether any undefined behavior was detected. *)
  ub_reasons : ub_reason list;
      (** List of all undefined behavior instances found. *)
  checked_executions : execution_info list option;
      (** Per-execution results with satisfaction and UB status. *)
  assertion_instances : Context.assertion_instance list option;
      (** Detailed assertion instance tracking. *)
}

(** {1 Outcome Conversions} *)

(** [outcome_of_string s] is the outcome [s] names ("allow" or "forbid").
    @raise Failure if [s] names neither. *)
val outcome_of_string : string -> Ir.ir_assertion_outcome

(** {1 Set Operations} *)

(** Set membership operations for assertions, such as [(e1, e2) in .rf]. *)
module SetOperations : sig
  (** [has_set_operation expr] holds when [expr] contains a set membership test
      anywhere within it. *)
  val has_set_operation : expr -> bool

  (** [eval_tuple expr] is the pair of event ids of a tuple expression [(a, b)].
      @raise Failure if [expr] is not a tuple of integers. *)
  val eval_tuple : expr -> int * int

  (** [eval_set_expr expr structure execution] evaluates a set membership
      expression, or a boolean combination of them, against the relations of
      [execution].
      @raise Failure if the expression cannot be evaluated. *)
  val eval_set_expr :
    expr -> symbolic_event_structure -> symbolic_execution -> bool
end

(** {1 Assertion Checking} *)

(** [check_assertion ?ctx assertion executions structure ~exhaustive] validates
    [assertion] against [executions]. Main entry point for assertion checking.
*)
val check_assertion :
  ?ctx:mordor_ctx ->
  ir_node_ann Ir.ir_assertion ->
  Execution.t list ->
  symbolic_event_structure ->
  exhaustive:bool ->
  assertion_result Lwt.t

(** [ub_reasons_to_yojson ubs] converts a UB reason list to Yojson. *)
val ub_reasons_to_yojson : ub_reason list -> Yojson.Safe.t

(** {1 Pipeline Steps} *)

(** [step_check_assertions ctx] validates the context's assertions against its
    generated executions. Always runs UB detection, even without explicit
    assertions. *)
val step_check_assertions : mordor_ctx Lwt.t -> mordor_ctx Lwt.t

(** [step_send_assertion_results ~send_data lwt_ctx] serialises the assertion
    results to JSON and sends them to the client, leaving the context unchanged.
*)
val step_send_assertion_results :
  send_data:(string -> unit Lwt.t) -> mordor_ctx Lwt.t -> mordor_ctx Lwt.t
