(** {1 Streaming Pipelines}

    The analyses the web UI asks for. Each sends its results through
    [send_data], one JSON message at a time, as it goes: over SSE from
    [web/server.ml], and as Web Worker messages from the browser build (W3,
    #179). Moved from [web/server.ml], so that both send the same messages. *)

open Context
open Lwt.Syntax
open Source_info
open Uset

(** Completion message sent at the end. *)

type complete_message = {
  type_ : string; [@key "type"]
      (** type_ Message type (should be "complete") *)
  total_executions : int;  (** Optional total number of executions *)
}
[@@deriving yojson]

let send_complete ~send_data total_executions =
  let complete_message = { type_ = "complete"; total_executions } in
  let complete_json =
    Yojson.Safe.to_string (complete_message_to_yojson complete_message)
  in
    send_data complete_json

(** The models the settings dialog offers to compare, by the names the model
    table uses, and ["ps1"] and ["ps2"]: promising semantics, which computes
    executions of its own and is compared by outcome (see [Semantics]). *)
let comparable_models =
  ("smrd" :: "rc11" :: "imm" :: Context.implemented_zoo_models)
  @ [ "ps1"; "ps2" ]

(** The primary models it offers: those, or ["default"], the model the litmus
    test states or sMRD, which can be one not offered here. *)
let selectable_models = "default" :: comparable_models

(** [step_executions ~send_data] computes the executions under the semantics the
    model selection chose. sMRD's justifications are sent as they are found;
    promising semantics has none, and tracks each execution's events and
    relations so that its graph has something to show. *)
let step_executions ~send_data =
  Semantics.step_calculate_executions ~track:true
    ~after_justifications:
      (Eventstructureviz.step_send_justification_set ~send_data)

(** A request's choice of models: the primary executions are enumerated under,
    and the others each is checked against. *)
type model_selection = { primary : string; others : string list }

(** [model_selection_of_json json] reads [memory_model] and [compare_models].

    No [memory_model] is ["default"], the model the litmus test states or sMRD.
    A model the server does not offer is an error naming it, primary or
    compared: running under another model and labelling the results with the one
    asked for would answer a different question. [Failure] carries the message.
*)
let model_selection_of_json json =
  let field key =
    match json with
    | `Assoc fields -> List.assoc_opt key fields
    | _ -> None
  in
  let unknown = ref [] in
  let known offered m =
    let m = String.lowercase_ascii m in
      if List.mem m offered then Some m
      else (
        unknown := m :: !unknown;
        None
      )
  in
  let primary =
    match field "memory_model" with
    | None | Some `Null -> "default"
    | Some (`String m) -> known selectable_models m |> Option.value ~default:""
    | Some other ->
        unknown := Yojson.Basic.to_string other :: !unknown;
        ""
  in
  let others =
    match field "compare_models" with
    | Some (`List ms) ->
        List.filter_map
          (function
            | `String m -> known comparable_models m
            | other ->
                unknown := Yojson.Basic.to_string other :: !unknown;
                None
            )
          ms
    | _ -> []
  in
    match List.rev !unknown with
    | [] -> { primary; others }
    | names ->
        failwith
          (Printf.sprintf "Unknown memory model%s %s. The server offers %s."
             (if List.length names > 1 then "s" else "")
             (String.concat ", " (List.map (Printf.sprintf "%S") names))
             (String.concat ", " selectable_models)
          )

(** [select_models selection] is {!Context.step_select_models} for a request. It
    follows parsing, which is what resolves ["default"]. *)
let select_models { primary; others } =
  Context.step_select_models ~primary ~others

(** {2 Visualization Functions} *)

(** [visualize_to_stream program options step_counter ~send_data] processes a
    litmus test program through the analysis pipeline and sends results as JSON
    messages.

    @param program The litmus test program source code as a string
    @param options Configuration options for the analysis
    @param step_counter The maximum number of loop iterations to execute
    @param send_data Sends one JSON message, as the transport has it
    @return
      A promise that resolves to the final context after all analysis steps

    The function performs the following pipeline:
    - Parses the litmus test program
    - Sends loop information
    - Interprets the program
    - Generates and sends event structure graphs
    - Tests episodicity properties
    - Calculates dependencies
    - Checks assertions
    - Sends execution graphs *)
let visualize_to_stream program options step_counter ~models ~send_data =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    Logs.info (fun m ->
        m "Visualize single program with options\n%s" (show_options options)
    );

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> select_models models
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
           ~on_loop_result:(Episodicity.send_loop_episodicity_result send_data)
      |> step_executions ~send_data
      |> Eventstructureviz.step_send_model_counts ~send_data
      |> Assertion.step_check_assertions
      |> Assertion.step_send_assertion_results ~send_data
      |> Eventstructureviz.step_send_execution_graphs ~send_data
    in

    let total_executions =
      match ctx.executions with
      | Some exs -> USet.size exs
      | None ->
          Logs.info (fun m -> m "no executions");
          0
    in
      let* () = send_complete ~send_data total_executions in

      Lwt.return ctx

let visualize_parse_to_stream program options step_counter ~models ~send_data =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> select_models models
      |> LoopInformation.send_loop_information send_data
    in

    let* () = send_complete ~send_data 0 in

    Lwt.return ctx

let visualize_interpret_to_stream program options step_counter ~models
    ~send_data =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> select_models models
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
    in

    let* () = send_complete ~send_data 0 in

    Lwt.return ctx

let visualize_test_episodicity_to_stream program options step_counter ~models
    ~send_data =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> select_models models
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
           ~on_loop_result:(Episodicity.send_loop_episodicity_result send_data)
    in

    let* () = send_complete ~send_data 0 in

    Lwt.return ctx

let visualize_test_assertions_to_stream program options step_counter ~models
    ~send_data =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> select_models models
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
           ~on_loop_result:(Episodicity.send_loop_episodicity_result send_data)
      |> step_executions ~send_data
      |> Eventstructureviz.step_send_model_counts ~send_data
      |> Assertion.step_check_assertions
      |> Assertion.step_send_assertion_results ~send_data
      |> Eventstructureviz.step_send_execution_graphs ~send_data
    in

    let total_executions =
      match ctx.executions with
      | Some exs -> USet.size exs
      | None -> 0
    in
      let* () = send_complete ~send_data total_executions in

      Lwt.return ctx

(** [error_message exn] is the text to show for [exn]: a [Failure]'s own
    message, which is how the pipeline reports what went wrong, rather than
    [Failure("...")] around it. *)
let error_message = function
  | Failure msg -> msg
  | exn -> Printexc.to_string exn

(** {2 Requests} *)

(** A request: the program, the options it is analysed under, and the models
    chosen, or why they could not be. *)
type request = {
  program : string;
  options : options;
  step_counter : int;
  models : (model_selection, string) result;
}

(** [request_of_json json] reads a request as the [/api/*/stream] bodies have
    it: [program], [loop_semantics], [steps], [memory_model] and
    [compare_models]. An unknown model is not an error here: it is reported on
    the stream, as any other error is. *)
let request_of_json json =
  let get_field key =
    match json with
    | `Assoc fields -> (
        match List.assoc_opt key fields with
        | Some (`String s) -> s
        | _ -> ""
      )
    | _ -> ""
  in

  let program = get_field "program" in

  let loop_semantics =
    match String.lowercase_ascii (get_field "loop_semantics") with
    | "symbolic" -> Symbolic
    | "step-counter" -> StepCounterPerLoop
    | _ -> StepCounterPerLoop
  in

  let step_counter =
    match loop_semantics with
    | Generic | Symbolic -> 0
    | StepCounterPerLoop | FiniteStepCounter -> (
        let s = get_field "steps" in
          try int_of_string s with Failure _ -> 2
      )
  in

  let models =
    try Ok (model_selection_of_json json) with Failure msg -> Error msg
  in

  (* No model is applied before parsing: [select_models] needs to see what the
     test itself states. *)
  let options = { default_options with loop_semantics; step_counter } in
    { program; options; step_counter; models }

let status_message status =
  Yojson.Basic.to_string (`Assoc [ ("status", `String status) ])

let error_json message =
  Yojson.Basic.to_string
    (`Assoc [ ("type", `String "error"); ("message", `String message) ])

(** [run ?on_error pipeline request ~send_data] runs [pipeline] on [request],
    sending the status messages [parsing], [interpreting] and [visualizing]
    first, then what [pipeline] sends. A failure, an unknown model among them,
    is sent as an [error] message, after [on_error] is told it. *)
let run ?(on_error = fun _ -> ()) pipeline request ~send_data =
  Lwt.catch
    (fun () ->
      let models =
        match request.models with
        | Ok models -> models
        | Error msg -> failwith msg
      in
        let* () = send_data (status_message "parsing") in
          Logs.info (fun m ->
              m "Running single program with options\n%s"
                (show_options request.options)
          );
          let* () = send_data (status_message "interpreting") in
            let* () = send_data (status_message "visualizing") in
              let* _ctx =
                pipeline request.program request.options request.step_counter
                  ~models ~send_data
              in
                Lwt.return_unit
    )
    (fun exn ->
      let error_msg = error_message exn in
        on_error error_msg;
        send_data (error_json error_msg)
    )
