(** {1 Mordor Web Server}

    A web server for visualizing program execution graphs and running litmus
    tests. Provides Server-Sent Events (SSE) streaming for real-time
    visualization and a REST API for test execution. *)

open Context
open Episodicity_runner_api
open Lwt.Syntax
open Source_info
open Test_runner_api
open Types
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

(** {2 Visualization Functions} *)

(** [visualize_to_stream program options step_counter stream] processes a litmus
    test program through the analysis pipeline and streams results as JSON via
    SSE.

    @param program The litmus test program source code as a string
    @param options Configuration options for the analysis
    @param step_counter The maximum number of loop iterations to execute
    @param stream The Dream SSE stream to write results to
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
let visualize_to_stream program options step_counter stream =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    Logs.info (fun m ->
        m "Visualize single program with options\n%s" (show_options options)
    );

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
      |> Episodicity.send_episodicity_results send_data
      |> Elaborations.step_generate_justifications
      |> Executions.step_calculate_dependencies
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

let visualize_parse_to_stream program options step_counter stream =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> LoopInformation.send_loop_information send_data
    in

    let* () = send_complete ~send_data 0 in

    Lwt.return ctx

let visualize_interpret_to_stream program options step_counter stream =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
    in

    let* () = send_complete ~send_data 0 in

    Lwt.return ctx

let visualize_test_episodicity_to_stream program options step_counter stream =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
      |> Episodicity.send_episodicity_results send_data
    in

    let* () = send_complete ~send_data 0 in

    Lwt.return ctx

let visualize_test_assertions_to_stream program options step_counter stream =
  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
      |> Episodicity.send_episodicity_results send_data
      |> Elaborations.step_generate_justifications
      |> Executions.step_calculate_dependencies
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

(** [sse_data json_obj] formats a JSON object as an SSE data message.

    @param json_obj The JSON object to format
    @return A string in SSE format: "data: <json>\n\n" *)
let sse_data json_obj =
  let json_str = Yojson.Basic.to_string json_obj in
    Printf.sprintf "data: %s\n\n" json_str

(** {2 HTTP Request Handlers} *)

(** [make_sse_handler pipeline_fn] creates an SSE handler for a specific
    pipeline.

    @param pipeline_fn
      The pipeline function to execute, with signature:
      [string -> options -> int -> Dream.stream -> context Lwt.t]
    @return An HTTP request handler that sets up SSE streaming for the pipeline
*)
let make_sse_handler pipeline_fn request =
  let* body = Dream.body request in

  let json = try Yojson.Basic.from_string body with _ -> `Assoc [] in

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

  let memory_model =
    let m = String.lowercase_ascii (get_field "memory_model") in
      match m with
      | "rc11" | "rc11c" | "rc11ub" | "smrd" | "ub11" | "undefined" -> m
      | _ -> "smrd"
  in

  Printf.printf "📥 SSE request: %d chars, %d steps, model: %s\n%!"
    (String.length program) step_counter memory_model;

  Dream.stream
    ~headers:
      [
        ("Content-Type", "text/event-stream");
        ("Cache-Control", "no-cache");
        ("Connection", "keep-alive");
        ("X-Accel-Buffering", "no");
      ]
    (fun stream ->
      Lwt.catch
        (fun () ->
          let* () =
            Dream.write stream
              (sse_data (`Assoc [ ("status", `String "parsing") ]))
          in
            let* () = Dream.flush stream in

            let options =
              {
                default_options with
                loop_semantics;
                step_counter;
                model = memory_model;
              }
            in

            Logs.info (fun m ->
                m "Running single program with options\n%s"
                  (show_options options)
            );

            let* () =
              Dream.write stream
                (sse_data (`Assoc [ ("status", `String "interpreting") ]))
            in
              let* () = Dream.flush stream in

              let* () =
                Dream.write stream
                  (sse_data (`Assoc [ ("status", `String "visualizing") ]))
              in
                let* () = Dream.flush stream in

                let* _ctx = pipeline_fn program options step_counter stream in

                Lwt.return_unit
        )
        (fun exn ->
          let error_msg = Printexc.to_string exn in
            Printf.printf "❌ Pipeline error: %s\n%!" error_msg;
            let* () =
              Dream.write stream
                (sse_data
                   (`Assoc
                      [
                        ("type", `String "error"); ("message", `String error_msg);
                      ]
                   )
                )
            in
              Dream.flush stream
        )
    )

(** [visualize_sse_handler request] handles SSE requests for full program
    visualization using the complete pipeline. *)
let visualize_sse_handler = make_sse_handler visualize_to_stream

(** [parse_sse_handler request] handles SSE requests for parsing only. *)
let parse_sse_handler = make_sse_handler visualize_parse_to_stream

(** [interpret_sse_handler request] handles SSE requests for parsing and
    interpretation. *)
let interpret_sse_handler = make_sse_handler visualize_interpret_to_stream

(** [episodicity_sse_handler request] handles SSE requests for parsing,
    interpretation, and episodicity testing. *)
let episodicity_sse_handler =
  make_sse_handler visualize_test_episodicity_to_stream

(** [assertions_sse_handler request] handles SSE requests for parsing,
    interpretation, episodicity testing, and assertion checking. *)
let assertions_sse_handler =
  make_sse_handler visualize_test_assertions_to_stream

(** [health_handler request] provides a simple health check endpoint.

    @param request The HTTP request (unused)
    @return A JSON response with status "ok" *)
let health_handler _request = Dream.json "{\"status\": \"ok\"}"

(** {2 Server Setup and Configuration} *)

(** [setup_logs ()] configures the logging system with timestamps.

    Sets up a custom log reporter that includes microsecond-precision timestamps
    in the format [HH:MM:SS.mmm]. Sets the log level to Debug. *)
let setup_logs () =
  let pp_header ppf (l, h) =
    let timestamp = Unix.gettimeofday () in
    let tm = Unix.localtime timestamp in
      Format.fprintf ppf "[%02d:%02d:%02d.%03d] %a: " tm.Unix.tm_hour
        tm.Unix.tm_min tm.Unix.tm_sec
        (int_of_float ((timestamp -. floor timestamp) *. 1000.))
        Logs_fmt.pp_header (l, h)
  in
  let reporter = Logs_fmt.reporter ~pp_header () in
    Logs.set_reporter reporter;
    Logs.set_level (Some Logs.Debug)

(** {2 Main Server Entry Point}

    Starts the Mordor web server with the following endpoints:

    {b Static Content:}
    - [GET /] - Main application page (index.html)
    - [GET /help/] - Help documentation (help.html)
    - [GET /static/**] - Static assets (CSS, JS, images)

    {b Health Check:}
    - [GET /health] - Returns [{"status": "ok"}]

    {b Visualization API:}
    - [GET /api/visualize/stream] - SSE endpoint for full visualization pipeline
    - [GET /api/visualize/parse/stream] - SSE endpoint for parse stage only
    - [GET /api/visualize/interpret/stream] - SSE endpoint for parse + interpret
      stages
    - [GET /api/visualize/episodicity/stream] - SSE endpoint for parse +
      interpret + episodicity stages
    - [GET /api/visualize/assertions/stream] - SSE endpoint for parse +
      interpret + episodicity + assertions stages

    {b Test Runner API:}
    - [GET /api/tests/list] - List all available litmus tests
    - [POST /api/tests/run] - Run a specific test
    - [GET /api/tests/source] - Get source code of a test

    The server listens on port 8080 on all interfaces (0.0.0.0). *)
let () =
  setup_logs ();
  Printexc.record_backtrace true;
  Printf.printf "Mordor Web - Graph Visualization & Test Runner\n";
  Printf.printf "🌐 http://localhost:8080\n\n";

  Dream.run ~interface:"0.0.0.0" ~port:8080
  @@ Dream.logger
  @@ Dream.router
       ([
          Dream.get "/" (Dream.from_filesystem "web/frontend" "index.html");
          Dream.get "/help/" (Dream.from_filesystem "web/frontend" "help.html");
          Dream.get "/static/**" (Dream.static "web/frontend/static");
          Dream.get "/health" health_handler;
          (* Visualization API - Pipeline stages *)
          Dream.post "/api/visualize/stream" visualize_sse_handler;
          Dream.post "/api/parse/stream" parse_sse_handler;
          Dream.post "/api/interpret/stream" interpret_sse_handler;
          Dream.post "/api/episodicity/stream" episodicity_sse_handler;
          Dream.post "/api/assertions/stream" assertions_sse_handler;
        ]
       @ Test_runner_api.routes
       @ Episodicity_runner_api.routes
       )
