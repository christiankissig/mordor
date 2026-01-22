open Ast
open Types
open Uset

type ir_node_ann = {
  source_span : source_span option;
  thread_ctx : thread_ctx option;
  loop_ctx : loop_ctx option;
}

type ir_stmt = ir_node_ann Ir.ir_stmt
type ir_node = ir_node_ann Ir.ir_node
type ir_assertion = ir_node_ann Ir.ir_assertion
type ir_litmus = ir_node_ann Ir.ir_litmus

(** configuration options *)

type output_mode = Json | Html | Dot | Isa

type loop_semantics =
  | Symbolic
  | FiniteStepCounter
  | StepCounterPerLoop
  | Generic

let parse_output_mode s =
  match String.lowercase_ascii s with
  | "json" -> Json
  | "html" -> Html
  | "dot" -> Dot
  | "isa" | "isabelle" -> Isa
  | _ ->
      Printf.eprintf
        "Error: Invalid output mode '%s' (must be json, html, dot, or isa)\n" s;
      exit 1

type options = {
  mutable model : string;
  mutable dependencies : bool;
  mutable exhaustive : bool;
  mutable forcerc11 : bool;
  mutable forceimm : bool;
  mutable forcenocoh : bool;
  mutable coherent : string;
  mutable ubopt : bool;
  mutable loop_semantics : loop_semantics;
  mutable step_counter : int;
}

let default_options =
  {
    model = "undefined";
    dependencies = true;
    exhaustive = false;
    forcerc11 = false;
    forceimm = false;
    forcenocoh = false;
    coherent = "undefined";
    loop_semantics = StepCounterPerLoop;
    step_counter = 2;
    ubopt = false;
  }

(** {1 Types for Checked Executions} *)

type uaf_ub_reason = (int * int) uset
type upd_ub_reason = (int * int) uset
type ub_reason = UAF of uaf_ub_reason | UPD of upd_ub_reason
type ub_reasons = (int * ub_reason) list

type execution_info = {
  exec_id : int;
  satisfied : bool;
  ub_reasons : ub_reason list;
}

(** {1 Types for Episodicity Tests} *)

type register_condition_violation =
  | RegisterReadBeforeWrite of string (* register name *) * source_span option
[@@deriving show, yojson]

type write_condition_violation =
  | WriteFromPreviousIteration of
      string (* location expression as string *)
      * source_span option
      (*read source span *)
      * source_span option (* write source span *)
[@@deriving show, yojson]

type branch_condition_violation =
  | BranchConstraintsSymbol of
      string (* symbol name *) * int (* symbol origin
  *) * source_span option
[@@deriving show, yojson]

type loop_condition_violation =
  | LoopIterationOrderingViolation of
      int (* iteration *)
      * source_span option (* from source span *)
      * source_span option (* to source span *)
[@@deriving show, yojson]

(** Episodicity violation types *)
type episodicity_violation =
  | RegisterConditionViolation of register_condition_violation
  | WriteConditionViolation of write_condition_violation
  | BranchConditionViolation of branch_condition_violation
  | LoopConditionViolation of loop_condition_violation
[@@deriving show, yojson]

(** Result of episodicity check for a single condition *)
type condition_result = {
  satisfied : bool;
  violations : episodicity_violation list;
}
[@@deriving show, yojson]

(** Complete episodicity analysis result for a loop *)
type loop_episodicity_result = {
  loop_id : int;
  condition1 : condition_result; (* Register access *)
  condition2 : condition_result; (* Memory read sources *)
  condition3 : condition_result; (* Branch conditions *)
  condition4 : condition_result; (* Inter-iteration ordering *)
  is_episodic : bool;
}
[@@deriving show, yojson]

type loop_episodicity_result_summary = {
  type_ : string; [@key "type"]
  loop_episodicity_results : loop_episodicity_result list;
}
[@@deriving show, yojson]

(** context for pipeline *)
type mordor_ctx = {
  (* pipeline config *)
  options : options;
  (* inputs *)
  mutable litmus_name : string;
  mutable litmus_file : string option;
  mutable litmus : string option;
  (* parser *)
  mutable litmus_constraints : expr list option;
  mutable program_stmts : ir_node list option;
  mutable assertions : ir_assertion option;
  (* event structures *)
  step_counter : int;
  mutable events : (int, event) Hashtbl.t option;
  mutable structure : symbolic_event_structure option;
  mutable source_spans : event_source_code_span option;
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
  mutable checked_executions : execution_info list option;
  (* episodicity per loop index *)
  mutable is_episodic : (int, bool) Hashtbl.t option;
  mutable episodicity_results : loop_episodicity_result_summary option;
}

let make_context options ?(output_mode = Json) ?(output_file = "stdout")
    ?(step_counter = 2) () =
  {
    options;
    litmus_name = "";
    litmus_file = None;
    litmus = None;
    litmus_constraints = None;
    assertions = None;
    program_stmts = None;
    step_counter;
    events = None;
    structure = None;
    source_spans = None;
    justifications = None;
    executions = None;
    futures = None;
    output = None;
    output_mode;
    output_file;
    valid = None;
    undefined_behaviour = None;
    checked_executions = None;
    is_episodic = None;
    episodicity_results = None;
  }

(** {1 Model Options} *)

type model_options = { coherent : string option; ubopt : bool }

let model_options_table : (string, model_options) Hashtbl.t =
  let tbl = Hashtbl.create 20 in
    Hashtbl.add tbl "power" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "sevcik" { coherent = None; ubopt = false };
    Hashtbl.add tbl "problem" { coherent = None; ubopt = false };
    Hashtbl.add tbl "jr" { coherent = None; ubopt = false };
    Hashtbl.add tbl "rc11" { coherent = Some "rc11"; ubopt = false };
    Hashtbl.add tbl "rc11c" { coherent = Some "rc11c"; ubopt = false };
    Hashtbl.add tbl "bridging" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "bubbly" { coherent = None; ubopt = false };
    Hashtbl.add tbl "grounding" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "promising" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "soham" { coherent = None; ubopt = false };
    Hashtbl.add tbl "imm" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "rc11ub" { coherent = Some "rc11"; ubopt = true };
    Hashtbl.add tbl "immub" { coherent = Some "imm"; ubopt = true };
    Hashtbl.add tbl "ub11" { coherent = None; ubopt = true };
    Hashtbl.add tbl "_" { coherent = None; ubopt = false };
    tbl

let get_model_options name =
  Hashtbl.find_opt model_options_table (String.lowercase_ascii name)

let model_names =
  [
    "Power";
    "Sevcik";
    "Problem";
    "JR";
    "RC11";
    "RC11c";
    "Bridging";
    "Bubbly";
    "Grounding";
    "Promising";
    "Soham";
    "IMM";
    "RC11UB";
    "IMMUB";
    "UB11";
    "_";
  ]

let apply_model_options (ctx : mordor_ctx) (model : string) : unit =
  ctx.options.model <- model;
  Logs.info (fun m -> m "applying model options for model %s" model);
  Hashtbl.find_opt model_options_table model
  |> Option.map (fun options -> options.coherent)
  |> Option.value ~default:None
  |> Option.iter (fun coherent ->
      Logs.debug (fun m -> m "setting coherent %s" coherent);
      ctx.options.coherent <- coherent
  )
