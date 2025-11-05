open Types
open Uset
open Ir

type mordor_ctx = {
  (* pipeline config *)
  opts : options;
  (* inputs *)
  litmus_name : string option;
  litmus_file : string option;
  litmus : string option;
  (* parser *)
  litmus_constraints : expr list option;
  program_stmts : ir_stmt list option;
  (* event structures *)
  event_ids : int USet.t option;
  events : (int, event) Hashtbl.t option;
  (* justifications *)
  justifications : justification USet.t option;
  (* executions *)
  executions : symbolic_execution USet.t option;
  (* futures *)
  futures : future USet.t option;
  (* visualisation *)
  output : string option;
}

let make_context opts =
  {
    opts;
    litmus_name = None;
    litmus_file = None;
    litmus = None;
    litmus_constraints = None;
    program_stmts = None;
    event_ids = None;
    events = None;
    justifications = None;
    executions = None;
    futures = None;
    output = None;
  }
