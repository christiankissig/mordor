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

(** {2 Example Library} *)

(** The examples the editor's dropdown offers, served from the corpus.

    Embedding a second copy of SB, MP and LB in the frontend meant the tool
    shipped three programs while [litmus-tests/] held nearly three hundred, and
    the copies were free to drift from the corpus (github #76). These are paths
    into the tree the integration suite scans, so an example is a test that is
    known to run.

    Grouped by what the example is for, not by where it lives. *)
let example_library =
  [
    ("Classics", "MP", "litmus-tests/test6/MP.lit");
    ("Classics", "LB", "litmus-tests/test6/LB.lit");
    ("Classics", "SB (3 threads)", "litmus-tests/test6/3.SB.lit");
    ("Classics", "IRIW", "litmus-tests/test6/IRIW.lit");
    ("Classics", "2+2W", "litmus-tests/test6/2+2W.lit");
    ("Classics", "RWC", "litmus-tests/test6/RWC.lit");
    ("Classics", "W+RWC", "litmus-tests/test6/W+RWC.lit");
    ("Coherence", "CoRR", "litmus-tests/test6/CoRR1.lit");
    ("Coherence", "CoRW", "litmus-tests/test6/CoRW.lit");
    ("Coherence", "CoWR", "litmus-tests/test6/CoWR.lit");
    ("Coherence", "CoWW", "litmus-tests/test6/CoWW.lit");
    ( "Fences and access modes",
      "IRIW+acq+sc",
      "litmus-tests/pldi_repairing/IRIW+acq+sc.lit"
    );
    ( "Fences and access modes",
      "IRIW+Fsc+Fsc",
      "litmus-tests/popl_bridging/IRIW+Fsc+Fsc.lit"
    );
    ( "Fences and access modes",
      "IRIW+rlx",
      "litmus-tests/rmm-zoo/properties/atomicity-mca/IRIW+rlx.lit"
    );
    ( "Fences and access modes",
      "RWC+syncs",
      "litmus-tests/pldi_repairing/RWC+syncs.lit"
    );
    ( "Dependencies and thin air",
      "LB+deps",
      "litmus-tests/popl_bubbly/LB+deps.lit"
    );
    ( "Dependencies and thin air",
      "LB+ctrldata",
      "litmus-tests/esop_problem/lb+ctrldat+ctrl-single.lit"
    );
    ( "Dependencies and thin air",
      "Out-of-thin-air (listing12)",
      "litmus-tests/avoidoota/listing12.lit"
    );
    ( "Dependencies and thin air",
      "Volatile store is not elided",
      "litmus-tests/own/volatile-store-not-elided.lit"
    );
    (* The ones cppMem cannot express at all, and which had no one-click route
       into the editor before. *)
    ("MoRDor only", "Use after free", "programs/uaf-bug.lit");
    ("MoRDor only", "Use after free (fixed)", "programs/uaf-bug-fixed.lit");
    ("MoRDor only", "Refinement chain", "litmus-tests/avoidoota/listing7.lit");
    ( "MoRDor only",
      "Episodicity: a register condition",
      "programs/episodicity/register_condition/fail.lit"
    );
  ]

(** [read_example path] is the file's contents, or [None] if it is not there. *)
let read_example path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
      close_in ic;
      Some s
  with Sys_error _ -> None

(** [examples_handler _] serves the library as JSON.

    An entry whose file is missing is dropped with a warning rather than
    breaking the dropdown, so a corpus rename degrades to one fewer example. *)
let examples_handler _request =
  let entries =
    List.filter_map
      (fun (group, label, path) ->
        match read_example path with
        | Some source ->
            Some
              (`Assoc
                 [
                   ("group", `String group);
                   ("label", `String label);
                   ("path", `String path);
                   ("source", `String source);
                 ]
              )
        | None ->
            Logs.warn (fun m -> m "example not found, skipping: %s" path);
            None
      )
      example_library
  in
    Dream.json (Yojson.Safe.to_string (`List entries))

(** {2 Model Selection} *)

(** {2 HTTP Request Handlers} *)

(** [make_sse_handler pipeline_fn] creates an SSE handler for a specific
    pipeline of {!Streaming}: each message the pipeline sends becomes an SSE
    [data:] message.

    @param pipeline_fn The pipeline to run, as {!Streaming.run} takes it
    @return An HTTP request handler that sets up SSE streaming for the pipeline
*)
let make_sse_handler pipeline_fn request =
  let* body = Dream.body request in

  let json = try Yojson.Basic.from_string body with _ -> `Assoc [] in
  let request = Streaming.request_of_json json in

  ( match request.models with
  | Ok models ->
      Printf.printf
        "📥 SSE request: %d chars, %d steps, model: %s, compared: [%s]\n%!"
        (String.length request.program)
        request.step_counter models.primary
        (String.concat ", " models.others)
  | Error msg -> Printf.printf "📥 SSE request refused: %s\n%!" msg
  );

  Dream.stream
    ~headers:
      [
        ("Content-Type", "text/event-stream");
        ("Cache-Control", "no-cache");
        ("Connection", "keep-alive");
        ("X-Accel-Buffering", "no");
      ]
    (fun stream ->
      let send_data json_str =
        let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
          Dream.flush stream
      in
        Streaming.run
          ~on_error:(fun msg -> Printf.printf "❌ Pipeline error: %s\n%!" msg)
          pipeline_fn request ~send_data
    )

(** [visualize_sse_handler request] handles SSE requests for full program
    visualization using the complete pipeline. *)
let visualize_sse_handler = make_sse_handler Streaming.visualize_to_stream

(** [parse_sse_handler request] handles SSE requests for parsing only. *)
let parse_sse_handler = make_sse_handler Streaming.visualize_parse_to_stream

(** [interpret_sse_handler request] handles SSE requests for parsing and
    interpretation. *)
let interpret_sse_handler =
  make_sse_handler Streaming.visualize_interpret_to_stream

(** [episodicity_sse_handler request] handles SSE requests for parsing,
    interpretation, and episodicity testing. *)
let episodicity_sse_handler =
  make_sse_handler Streaming.visualize_test_episodicity_to_stream

(** [assertions_sse_handler request] handles SSE requests for parsing,
    interpretation, episodicity testing, and assertion checking. *)
let assertions_sse_handler =
  make_sse_handler Streaming.visualize_test_assertions_to_stream

(** [executions_export_handler request] returns all executions of the supplied
    program — with event details and the po, dp, ppo, rf, rmw relations — as a
    single JSON document.

    Expects a JSON body with [program], [loop_semantics], [steps], and
    [memory_model] fields (same shape as the SSE endpoints). The response is
    [application/json]. *)
let executions_export_handler request =
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

  let options = { default_options with loop_semantics; step_counter } in

  let context =
    make_context_with_model options ~output_mode:Json ~step_counter ()
  in
    context.litmus <- Some program;

    Lwt.catch
      (fun () ->
        let models =
          { (Streaming.model_selection_of_json json) with others = [] }
        in
          let* ctx =
            Lwt.return context
            |> Parse.step_parse_litmus
            |> Streaming.select_models models
            |> Lwt.map (fun (ctx : mordor_ctx) ->
                (* The export is of sMRD's executions, with their dependencies. *)
                Semantics.require_smrd ~command:"executions export" ctx.options;
                ctx
            )
            |> Interpret.step_interpret
            |> Elaborations.step_generate_justifications
            |> Executions.step_calculate_dependencies
          in
            match Executions_export.to_json_string ctx with
            | Some content ->
                Dream.respond
                  ~headers:[ ("Content-Type", "application/json") ]
                  content
            | None ->
                Dream.respond ~status:`Internal_Server_Error
                  ~headers:[ ("Content-Type", "application/json") ]
                  {|{"error": "executions or event structure not available"}|}
      )
      (fun exn ->
        let error_msg = Streaming.error_message exn in
          Printf.printf "❌ Executions export error: %s\n%!" error_msg;
          let body =
            Yojson.Basic.to_string
              (`Assoc
                 [ ("type", `String "error"); ("message", `String error_msg) ]
              )
          in
            Dream.respond ~status:`Internal_Server_Error
              ~headers:[ ("Content-Type", "application/json") ]
              body
      )

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

(** The port to listen on: [MORDOR_WEB_PORT], or 8080. *)
let port =
  Option.bind (Sys.getenv_opt "MORDOR_WEB_PORT") int_of_string_opt
  |> Option.value ~default:8080

(** {2 Main Server Entry Point}

    Starts the Mordor web server with the following endpoints:

    {b Static Content:}
    - [GET /] - Main application page (index.html)
    - [GET /manual/] - The manual (manual.html), which [GET /help/] also serves
      for links to the page it replaced
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

    The server listens on all interfaces (0.0.0.0), on {!port}. *)
let () =
  setup_logs ();
  Printexc.record_backtrace true;
  Printf.printf "Mordor Web - Graph Visualization & Test Runner\n";
  Printf.printf "🌐 http://localhost:%d\n\n" port;

  Dream.run ~interface:"0.0.0.0" ~port
  @@ Dream.logger
  @@ Dream.router
       ([
          Dream.get "/" (Dream.from_filesystem "web/frontend" "index.html");
          Dream.get "/manual/"
            (Dream.from_filesystem "web/frontend" "manual.html");
          Dream.get "/help/" (Dream.from_filesystem "web/frontend" "manual.html");
          Dream.get "/static/**" (Dream.static "web/frontend/static");
          Dream.get "/health" health_handler;
          (* Visualization API - Pipeline stages *)
          Dream.post "/api/visualize/stream" visualize_sse_handler;
          Dream.post "/api/parse/stream" parse_sse_handler;
          Dream.post "/api/interpret/stream" interpret_sse_handler;
          Dream.post "/api/episodicity/stream" episodicity_sse_handler;
          Dream.post "/api/assertions/stream" assertions_sse_handler;
          (* Executions export (non-streaming JSON) *)
          Dream.post "/api/executions" executions_export_handler;
          Dream.get "/api/examples" examples_handler;
        ]
       @ Test_runner_api.routes
       @ Episodicity_runner_api.routes
       )
