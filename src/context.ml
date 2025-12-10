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
  mutable model_name : string option;
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
    model_name = None;
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
  mutable litmus_name : string option;
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
    litmus_name = None;
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

let apply_model_options (ctx : mordor_ctx) (model_name : string) : unit =
  ctx.options.model_name <- Some model_name;
  match model_name with
  | "Power" -> ctx.options.coherent <- "imm"
  | "RC11" -> ctx.options.coherent <- "rc11"
  | "RC11c" -> ctx.options.coherent <- "rc11c"
  | "Bridging" | "Grounding" | "Promising" | "IMM" ->
      ctx.options.coherent <- "imm"
  | "RC11UB" ->
      ctx.options.coherent <- "rc11";
      ctx.options.ubopt <- true
  | "IMMUB" ->
      ctx.options.coherent <- "imm";
      ctx.options.ubopt <- true
  | "UB11" -> ctx.options.ubopt <- true
  | "Sevcik" | "Problem" | "JR" | "Bubbly" | "Soham" | "_" -> ()
  | _ -> Logs.warn (fun m -> m "Unknown model: %s" model_name)
