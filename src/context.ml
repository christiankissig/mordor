(** {1 Context Module}

    This module defines the core types and configuration structures used
    throughout the Mordor verification tool, including:
    - IR (Intermediate Representation) node annotations
    - Configuration options for analysis
    - Pipeline context that flows through verification stages
    - Memory model configurations

    @author Mordor Team *)

open Ast
open Types
open Uset

(** {1 Intermediate Representation Annotations} *)

(** Annotations attached to each IR node during parsing and interpretation.

    These annotations track contextual information needed for analysis:
    - Source code location for error reporting
    - Thread context for concurrent programs
    - Loop context for episodicity analysis *)
type ir_node_ann = {
  source_span : source_span option;  (** Location in the original source code *)
  thread_ctx : thread_ctx option;  (** Which thread this node belongs to *)
  loop_ctx : loop_ctx option;  (** Loop nesting and iteration information *)
}

(** IR statement with annotations. *)
type ir_stmt = ir_node_ann Ir.ir_stmt

(** IR node with annotations. *)
type ir_node = ir_node_ann Ir.ir_node

(** IR assertion with annotations. *)
type ir_assertion = ir_node_ann Ir.ir_assertion

(** Complete litmus test with annotations. *)
type ir_litmus = ir_node_ann Ir.ir_litmus

(** {1 Configuration Options} *)

(** Output format for visualizations and exports. *)
type output_mode =
  | Json  (** JSON format for machine-readable output *)
  | Html  (** HTML format for interactive visualizations *)
  | Dot  (** GraphViz DOT format for graph rendering *)
  | Isa  (** Isabelle/HOL format for theorem prover *)

(** Loop interpretation semantics mode.

    Controls how loops are handled during symbolic execution and verification:

    - {b Symbolic}: Represents loops symbolically without unrolling. Used for
      episodicity checking where we need to reason about arbitrary iterations.
      Creates symbolic event structures where loop iterations are parameterized.
    - {b FiniteStepCounter}: Unrolls all loops a fixed number of times globally.
      All loops in the program execute exactly [step_counter] iterations. Used
      for bounded model checking with a single iteration bound.
    - {b StepCounterPerLoop}: Each loop can have its own iteration bound. Allows
      fine-grained control over loop unrolling per loop construct. Default mode
      with 2 iterations per loop.
    - {b Generic}: Standard loop handling without special semantics. Falls back
      to default interpretation strategy.

    Example usage:
    {[
      (* Bounded verification with 3 iterations *)
      { options with loop_semantics = FiniteStepCounter; step_counter = 3 }
        (* Episodicity checking with symbolic loops *)
        { options with loop_semantics = Symbolic }
    ]} *)
type loop_semantics =
  | Symbolic  (** Symbolic representation for unbounded reasoning *)
  | FiniteStepCounter  (** Global iteration bound for all loops *)
  | StepCounterPerLoop  (** Per-loop iteration bounds *)
  | Generic  (** Default interpretation strategy *)

(** Parse output mode string from command line.

    @param s String representation (case-insensitive)
    @return The corresponding output_mode
    @raise Exit with error message if invalid *)
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

(** Analysis configuration options.

    These options control various aspects of the verification process:
    - Memory model selection
    - Analysis depth and exhaustiveness
    - Loop handling
    - Undefined behavior detection *)
type options = {
  mutable model : string;
      (** Memory consistency model name (e.g., "rc11", "imm", "power") *)
  mutable dependencies : bool;  (** Whether to compute dependency relations *)
  mutable exhaustive : bool;
      (** Whether to explore all possible executions exhaustively *)
  mutable forcerc11 : bool;  (** Force RC11 memory model constraints *)
  mutable forceimm : bool;
      (** Force IMM (Intermediate Memory Model) constraints *)
  mutable forcenocoh : bool;  (** Disable coherence checking *)
  mutable coherent : string;
      (** Coherence model to use (e.g., "imm", "rc11", "rc11c") *)
  mutable ubopt : bool;  (** Enable undefined behavior optimizations *)
  mutable loop_semantics : loop_semantics;  (** Loop interpretation mode *)
  mutable step_counter : int;
      (** Number of loop iterations for bounded analysis *)
}

(** Default configuration options.

    Provides sensible defaults:
    - Step counter per loop with 2 iterations
    - Dependencies enabled
    - No exhaustive exploration
    - No undefined behavior optimizations *)
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

(** Reason for use-after-free undefined behavior.

    A set of (write_event, read_event) pairs where reads access freed memory. *)
type uaf_ub_reason = (int * int) uset

(** Reason for unsequenced data race undefined behavior.

    A set of (event1, event2) pairs that race on the same location. *)
type upd_ub_reason = (int * int) uset

(** Unified undefined behavior reason. *)
type ub_reason =
  | UAF of uaf_ub_reason  (** Use-after-free *)
  | UPD of upd_ub_reason  (** Unsequenced data race *)

(** List of undefined behavior reasons per event. *)
type ub_reasons = (int * ub_reason) list

(** {1 Assertion Instance Tracking} *)

(** Information about a set membership test in an assertion.

    For expressions like [(w,r) in .rf], tracks:
    - The relation name (.rf, .co, etc.)
    - The event pair being tested
    - Whether the pair was found in the relation *)
type set_membership_info = {
  relation_name : string;  (** Name of the relation (e.g., "rf", "co") *)
  event_pair : int * int;  (** Pair of event IDs tested *)
  member : bool;  (** Whether the pair is in the relation *)
}

(** Detailed information about an assertion instance.

    Tracks what was evaluated and the result for a specific assertion check:
    - The instantiated expression after substitution
    - Set membership tests performed
    - The evaluation result *)
type assertion_instance_detail = {
  instantiated_expr : expr option;  (** Expression after substitution *)
  set_memberships : set_membership_info list;  (** Set operations evaluated *)
  result : bool;  (** Whether the assertion held *)
}

(** Result of checking an assertion against a single execution.

    An assertion can be:
    - {b Witnessed}: For allow assertions, an execution satisfies the condition
    - {b Contradicted}: For forbid assertions, an execution violates the condition
    - {b Confirmed}: For allow assertions, all executions satisfy the condition
    - {b Refuted}: For forbid assertions, all executions avoid the condition *)
type assertion_instance =
  | Witnessed of {
      exec_id : int;  (** Execution that witnessed the assertion *)
      detail : assertion_instance_detail;  (** Details of what was witnessed *)
    }  (** Allow assertion satisfied by this execution *)
  | Contradicted of {
      exec_id : int;  (** Execution that contradicted the assertion *)
      detail : assertion_instance_detail;  (** Details of the contradiction *)
    }  (** Forbid assertion violated by this execution *)
  | Confirmed  (** Assertion holds for all executions (for allow) *)
  | Refuted  (** Assertion avoided by all executions (for forbid) *)

(** Information about a checked execution.

    Records whether an execution satisfies assertions and any undefined behavior
    detected. *)
type execution_info = {
  exec_id : int;  (** Unique execution identifier *)
  satisfied : bool;  (** Whether assertions are satisfied *)
  ub_reasons : ub_reason list;  (** List of undefined behaviors found *)
}

(** {1 Types for Episodicity Tests} *)

(** Violation of Condition 1: Register access restriction.

    Occurs when a register is read before being written in the same iteration.
*)
type register_condition_violation =
  | RegisterReadBeforeWrite of string (* register name *) * source_span option
[@@deriving show, yojson]

(** Violation of Condition 2: Memory read sources.

    Occurs when a read accesses a write from a previous iteration that is not
    properly ordered. *)
type write_condition_violation =
  | WriteFromPreviousIteration of
      string (* location expression as string *)
      * source_span option (* read source span *)
      * source_span option (* write source span *)
[@@deriving show, yojson]

(** Violation of Condition 3: Branch condition symbols.

    Occurs when a branch condition constrains symbols read before the loop. *)
type branch_condition_violation =
  | BranchConstraintsSymbol of
      string (* symbol name *)
      * int (* symbol origin event *)
      * source_span option
[@@deriving show, yojson]

(** Violation of Condition 4: Inter-iteration ordering.

    Occurs when events from iteration i are not properly ordered before events
    from iteration i+1 by (ppo ∪ dp)*. *)
type loop_condition_violation =
  | LoopIterationOrderingViolation of
      int (* iteration *)
      * source_span option (* from source span *)
      * source_span option (* to source span *)
[@@deriving show, yojson]

(** Unified episodicity violation type.

    Represents any of the four episodicity conditions that can be violated. *)
type episodicity_violation =
  | RegisterConditionViolation of register_condition_violation
  | WriteConditionViolation of write_condition_violation
  | BranchConditionViolation of branch_condition_violation
  | LoopConditionViolation of loop_condition_violation
[@@deriving show, yojson]

(** Result of checking a single episodicity condition.

    Contains whether the condition is satisfied and details of any violations.
*)
type condition_result = {
  satisfied : bool;  (** Whether the condition holds *)
  violations : episodicity_violation list;  (** List of violations found *)
}
[@@deriving show, yojson]

(** Complete episodicity analysis result for a single loop.

    Contains results for all four conditions and overall episodicity
    determination. *)
type loop_episodicity_result = {
  loop_id : int;  (** Loop identifier *)
  condition1 : condition_result;  (** Register access restriction *)
  condition2 : condition_result;  (** Memory read sources *)
  condition3 : condition_result;  (** Branch conditions *)
  condition4 : condition_result;  (** Inter-iteration ordering *)
  is_episodic : bool;  (** Whether loop is episodic (all conditions satisfied) *)
}
[@@deriving show, yojson]

(** Summary of episodicity results for all loops in a program. *)
type loop_episodicity_result_summary = {
  type_ : string; [@key "type"]  (** Result type identifier *)
  loop_episodicity_results : loop_episodicity_result list;
      (** Results for each loop *)
}
[@@deriving show, yojson]

(** {1 Pipeline Context} *)

(** Main context that flows through the verification pipeline.

    This record accumulates results from each stage of analysis:
    + {b Parsing}: Converts litmus test to IR
    + {b Interpretation}: Generates symbolic event structure
    + {b Dependencies}: Computes dependency relations
    + {b Verification}: Checks assertions and undefined behavior
    + {b Episodicity}: Analyzes loop properties (optional)

    Each stage reads from and writes to this context, creating a pipeline of
    transformations. *)
type mordor_ctx = {
  (* Pipeline configuration *)
  options : options;  (** Analysis configuration *)
  (* Inputs *)
  mutable litmus_name : string;  (** Name of the litmus test *)
  mutable litmus_file : string option;  (** Source file path *)
  mutable litmus : string option;  (** Raw litmus test source *)
  (* Parser outputs *)
  mutable litmus_constraints : expr list option;
      (** Constraints from the litmus test *)
  mutable litmus_defacto : expr list option;
      (** De facto constraints (implementation-specific) *)
  mutable program_stmts : ir_node list option;  (** Parsed IR statements *)
  mutable assertions : ir_assertion option;  (** Assertions to verify *)
  (* Event structures *)
  step_counter : int;  (** Loop iteration bound *)
  mutable events : (int, event) Hashtbl.t option;
      (** Event table mapping labels to events *)
  mutable structure : symbolic_event_structure option;
      (** Symbolic event structure *)
  mutable source_spans : event_source_code_span option;
      (** Source code locations for events *)
  (* Justifications *)
  mutable justifications : justification USet.t option;
      (** Justification relations (for RC11/promising semantics) *)
  (* Executions *)
  mutable executions : symbolic_execution USet.t option;
      (** Set of possible executions *)
  (* Futures *)
  mutable futures : future USet.t option;
      (** Future states in symbolic execution *)
  (* Visualization *)
  mutable output : string option;  (** Generated output *)
  output_mode : output_mode;  (** Output format *)
  output_file : string;  (** Output file path *)
  (* Verification results *)
  mutable valid : bool option;
      (** Whether the program is valid (assertions satisfied) *)
  mutable undefined_behaviour : bool option;
      (** Whether undefined behavior was detected *)
  mutable checked_executions : execution_info list option;
      (** Detailed execution checking results *)
  mutable assertion_instances : assertion_instance list option;
      (** Detailed assertion instance tracking *)
  (* Episodicity results *)
  mutable is_episodic : (int, bool) Hashtbl.t option;
      (** Per-loop episodicity determination *)
  mutable episodicity_results : loop_episodicity_result_summary option;
      (** Detailed episodicity analysis results *)
}

(** Create a new pipeline context with given configuration.

    @param options Analysis configuration options
    @param output_mode Output format (default: Json)
    @param output_file Output file path (default: "stdout")
    @param step_counter Loop iteration bound (default: 2)
    @return A fresh context with no analysis results *)
let make_context options ?(output_mode = Json) ?(output_file = "stdout")
    ?(step_counter = 2) () =
  {
    options;
    litmus_name = "";
    litmus_file = None;
    litmus = None;
    litmus_constraints = None;
    litmus_defacto = None;
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
    assertion_instances = None;
    is_episodic = None;
    episodicity_results = None;
  }

(** {1 Memory Model Options} *)

(** Configuration specific to a memory model.

    Different models may require different coherence models and have different
    undefined behavior semantics. *)
type model_options = {
  coherent : string option;  (** Coherence model to use (e.g., "imm", "rc11") *)
  ubopt : bool;  (** Whether this model uses undefined behavior optimizations *)
}

(** Predefined configurations for known memory models.

    This table maps model names to their appropriate settings:
    - {b Power}: IBM POWER architecture with IMM coherence
    - {b RC11}: Repaired C11 memory model
    - {b IMM}: Intermediate Memory Model
    - {b Promising}: Promising semantics with IMM coherence
    - etc.

    Models with "UB" suffix enable undefined behavior optimizations. *)
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

(** Look up model options by name.

    @param name Model name (case-insensitive)
    @return Model options if found *)
let get_model_options name =
  Hashtbl.find_opt model_options_table (String.lowercase_ascii name)

(** List of all supported memory model names. *)
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

(** Apply model-specific options to a context.

    Sets the memory model and adjusts coherence settings based on the model's
    requirements.

    @param ctx The context to update
    @param model Model name to apply *)
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
