open Ir
open Types
open Uset

(** configuration options *)

type output_mode = Json | Html | Dot | Isa

type options = {
  dependencies : bool;
  just_structure : bool; (* TODO deprecate *)
  exhaustive : bool;
  forcerc11 : bool;
  forceimm : bool;
  forcenocoh : bool;
  coherent : string;
}

let default_options =
  {
    dependencies = true;
    just_structure = false;
    exhaustive = false;
    forcerc11 = false;
    forceimm = false;
    forcenocoh = false;
    coherent = "rc11";
  }

(** context for pipeline *)

type mordor_ctx = {
  (* pipeline config *)
  options : options;
  (* inputs *)
  mutable litmus_name : string option;
  mutable litmus_file : string option;
  mutable litmus : string option;
  (* parser *)
  mutable litmus_constraints : expr list option;
  mutable program_stmts : ir_stmt list option;
  (* event structures *)
  mutable events : (int, event) Hashtbl.t option;
  mutable structure : symbolic_event_structure option;
  (* justifications *)
  mutable justifications : justification USet.t option;
  (* executions *)
  mutable executions : symbolic_execution USet.t option;
  (* futures *)
  mutable futures : future USet.t option;
  (* visualisation *)
  mutable output : string option;
  output_mode : output_mode;
  output_file : string;
  (* verification results could be added here *)
  mutable valid : bool option;
  mutable undefined_behaviour : bool option;
}

let make_context options ?(output_mode = Json) ?(output_file = "stdout") () =
  {
    options;
    litmus_name = None;
    litmus_file = None;
    litmus = None;
    litmus_constraints = None;
    program_stmts = None;
    events = None;
    structure = None;
    justifications = None;
    executions = None;
    futures = None;
    output = None;
    output_mode;
    output_file;
    valid = None;
    undefined_behaviour = None;
  }

(** result type *)

(* TODO deprecate this in favor of mordor_ctx *)

type result = {
  ast : expr list; (* Simplified AST *)
  structure : symbolic_event_structure;
  events : (int, event) Hashtbl.t;
  executions : symbolic_execution list;
  valid : bool;
  ub : bool; (* undefined behavior *)
}
