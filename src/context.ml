open Ir
open Types
open Uset

type ir_stmt = unit Ir.ir_stmt
type ir_node = unit Ir.ir_node

(** configuration options *)

type output_mode = Json | Html | Dot | Isa

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
  (* step counter semantics of loops *)
  mutable use_finite_step_counter_semantics : bool;
  mutable use_step_counter_per_loop : bool;
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
    use_finite_step_counter_semantics = false;
    use_step_counter_per_loop = true;
    ubopt = false;
  }

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
  mutable assertions : unit ir_assertion option;
  (* event structures *)
  step_counter : int;
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
  (* episodicity checks *)
  mutable is_episodic : bool option;
}

let make_context options ?(output_mode = Json) ?(output_file = "stdout")
    ?(step_counter = 5) () =
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
    justifications = None;
    executions = None;
    futures = None;
    output = None;
    output_mode;
    output_file;
    valid = None;
    undefined_behaviour = None;
    is_episodic = None;
  }

(** {1 Model Options} *)

type model_options = { coherent : string option; ubopt : bool }

let model_options_table : (string, model_options) Hashtbl.t =
  let tbl = Hashtbl.create 20 in
    Hashtbl.add tbl "Power" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Sevcik" { coherent = None; ubopt = false };
    Hashtbl.add tbl "Problem" { coherent = None; ubopt = false };
    Hashtbl.add tbl "JR" { coherent = None; ubopt = false };
    Hashtbl.add tbl "RC11" { coherent = Some "rc11"; ubopt = false };
    Hashtbl.add tbl "RC11c" { coherent = Some "rc11c"; ubopt = false };
    Hashtbl.add tbl "Bridging" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Bubbly" { coherent = None; ubopt = false };
    Hashtbl.add tbl "Grounding" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Promising" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Soham" { coherent = None; ubopt = false };
    Hashtbl.add tbl "IMM" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "RC11UB" { coherent = Some "rc11"; ubopt = true };
    Hashtbl.add tbl "IMMUB" { coherent = Some "imm"; ubopt = true };
    Hashtbl.add tbl "UB11" { coherent = None; ubopt = true };
    Hashtbl.add tbl "_" { coherent = None; ubopt = false };
    tbl

let get_model_options name = Hashtbl.find_opt model_options_table name

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
  Hashtbl.find_opt model_options_table model
  |> Option.map (fun options -> options.coherent)
  |> Option.value ~default:None
  |> Option.iter (fun coherent -> ctx.options.coherent <- coherent)
