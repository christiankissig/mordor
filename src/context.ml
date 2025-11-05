open Types
open Uset
open Ir

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
  (* verification results could be added here *)
  mutable valid : bool option;
  mutable undefined_beahviour : bool option;
}

let make_context options =
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
    valid = None;
    undefined_beahviour = None;
  }

type result = {
  ast : expr list; (* Simplified AST *)
  structure : symbolic_event_structure;
  events : (int, event) Hashtbl.t;
  executions : symbolic_execution list;
  valid : bool;
  ub : bool; (* undefined behavior *)
}
