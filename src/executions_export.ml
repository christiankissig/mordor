(** {1 Executions Export Module}

    Serialises all symbolic executions of a litmus test into a structured
    document that includes per-event details and the program-order (po),
    data-dependency (dp), preserved-program-order (ppo), reads-from (rf), and
    read-modify-write (rmw) relations.

    The default output format is JSON, but the document is also emitted as a
    pretty-printed string for textual inspection. *)

open Context
open Expr
open Types
open Uset
open Lwt.Syntax

(** JSON representation of a single event in an execution. *)
type json_event = {
  id : int;  (** Event identifier *)
  type_ : string; [@key "type"]  (** Event type (Read, Write, Fence, ...) *)
  label : int;  (** Source label number *)
  thread : int option; [@default None]  (** Owning thread index, if known *)
  location : string option; [@default None]
      (** Memory location expression (for memory events) *)
  rval : string option; [@default None]  (** Read value symbol/number *)
  wval : string option; [@default None]  (** Write value expression *)
  cond : string option; [@default None]  (** Branch condition expression *)
  rmod : string;  (** Read memory ordering mode *)
  wmod : string;  (** Write memory ordering mode *)
  fmod : string;  (** Fence memory ordering mode *)
  volatile : bool;  (** Whether the event is volatile *)
  is_rmw : bool;  (** Whether the event is part of an RMW *)
  constraints : string list; [@default []]
      (** Path constraints restricting this event *)
}
[@@deriving yojson]

(** JSON representation of a single execution. *)
type json_execution = {
  id : int;  (** Execution identifier *)
  predicates : string list; [@default []]
      (** Path predicates that must hold for this execution *)
  events : json_event list;  (** Events participating in this execution *)
  po : (int * int) list;  (** Program-order edges restricted to events *)
  dp : (int * int) list;  (** Data dependencies *)
  ppo : (int * int) list;  (** Preserved program order *)
  rf : (int * int) list;  (** Reads-from *)
  rmw : (int * int) list;  (** Read-modify-write pairs *)
}
[@@deriving yojson]

(** Top-level document: program name and an array of executions. *)
type json_executions = { program : string; executions : json_execution list }
[@@deriving yojson]

let mode_to_string (m : mode) : string =
  match m with
  | Relaxed -> "Relaxed"
  | Acquire -> "Acquire"
  | Release -> "Release"
  | ReleaseAcquire -> "ReleaseAcquire"
  | SC -> "SC"
  | Normal -> "Normal"
  | Strong -> "Strong"
  | Nonatomic -> "Nonatomic"
  | Consume -> "Consume"

let event_to_json (structure : symbolic_event_structure) (event_id : int) :
    json_event =
  let evt = Hashtbl.find structure.events event_id in
  let constraints =
    try Hashtbl.find structure.restrict event_id with Not_found -> []
  in
  let thread = Hashtbl.find_opt structure.thread_index event_id in
    {
      id = event_id;
      type_ = show_event_type evt.typ;
      label = evt.label;
      thread;
      location = Option.map Expr.to_string evt.loc;
      rval = Option.map Value.to_string evt.rval;
      wval = Option.map Expr.to_string evt.wval;
      cond = Option.map Expr.to_string evt.cond;
      rmod = mode_to_string evt.rmod;
      wmod = mode_to_string evt.wmod;
      fmod = mode_to_string evt.fmod;
      volatile = evt.volatile;
      is_rmw = evt.is_rdmw;
      constraints = List.map Expr.to_string constraints;
    }

let execution_to_json (structure : symbolic_event_structure)
    (exec : symbolic_execution) : json_execution =
  let events =
    USet.values exec.e |> List.sort compare |> List.map (event_to_json structure)
  in
  let po =
    USet.filter
      (fun (s, d) -> USet.mem exec.e s && USet.mem exec.e d)
      structure.po
    |> USet.values
  in
    {
      id = exec.id;
      predicates = List.map Expr.to_string exec.ex_p;
      events;
      po;
      dp = USet.values exec.dp;
      ppo = USet.values exec.ppo;
      rf = USet.values exec.rf;
      rmw = USet.values exec.rmw;
    }

(** Build the structured executions document from a Mordor context.

    Returns [None] if the structure or executions have not yet been computed. *)
let build_executions_document (ctx : mordor_ctx) : json_executions option =
  match (ctx.structure, ctx.executions) with
  | Some structure, Some executions ->
      let exec_list = USet.values executions in
      let exec_jsons = List.map (execution_to_json structure) exec_list in
        Some { program = ctx.litmus_name; executions = exec_jsons }
  | _ -> None

(** Serialise the executions document to a JSON string.

    Returns [None] if the structure or executions are missing. *)
let to_json_string (ctx : mordor_ctx) : string option =
  Option.map
    (fun doc -> Yojson.Safe.to_string (json_executions_to_yojson doc))
    (build_executions_document ctx)

(** Pipeline step: write the executions document to the configured output.

    Honours [ctx.output_mode] (only [Json] is supported) and [ctx.output_file]
    ("stdout" prints to standard output, anything else opens a file). The
    serialised content is also stored in [ctx.output]. *)
let step_export_executions (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match ctx.output_mode with
    | Json -> (
        match to_json_string ctx with
        | None ->
            Logs_safe.err (fun m ->
                m
                  "Executions or event structure not available for export. \
                   Pipeline must run through dependency calculation first."
            );
            Lwt.return ctx
        | Some content -> (
            ctx.output <- Some content;
            match ctx.output_file with
            | "stdout" ->
                print_string content;
                print_newline ();
                flush stdout;
                Lwt.return ctx
            | path ->
                let oc = open_out path in
                  output_string oc content;
                  close_out oc;
                  Logs_safe.info (fun m ->
                      m "Executions JSON written to %s" path
                  );
                  Lwt.return ctx
          )
      )
    | _ ->
        Logs_safe.err (fun m ->
            m
              "Unsupported output mode for executions export (use \
               --output-mode json)."
        );
        Lwt.return ctx
