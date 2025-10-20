open Types
open Justifications

(** Symbolic Execution *)
type symbolic_execution = {
  ex_e : int uset; (* Event set *)
  rf : (int * int) uset; (* Reads-from relation *)
  dp : (int * int) uset; (* Dependencies *)
  ppo : (int * int) uset; (* Preserved program order *)
  ex_rmw : (int * int) uset; (* RMW pairs *)
  ex_p : expr list; (* Predicates *)
  conds : expr list; (* Conditions *)
  fix_rf_map : (string, value_type) Hashtbl.t; (* Fixed RF mappings *)
  justs : justification list; (* Justifications *)
  pointer_map : (int, value_type) Hashtbl.t option; (* Pointer mappings *)
}
