(** {1 Mordor Web Server}

    A web server for visualizing program execution graphs and running litmus
    tests. Provides Server-Sent Events (SSE) streaming for real-time
    visualization and a REST API for test execution. *)

open Lwt.Syntax
open Context
open Types
open Source_info
open Test_runner_api
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
  let context = make_context options ~output_mode:Json ~step_counter () in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    Logs.info(fun m ->
        m "Visualize single program with options\n%s"
          (show_options options)
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
      | None -> (Logs.info (fun m -> m "no executions"); 0)
    in
      let* () = send_complete ~send_data total_executions in

      Lwt.return ctx

let visualize_parse_to_stream program options step_counter stream =
  let context = make_context options ~output_mode:Json ~step_counter () in
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
  let context = make_context options ~output_mode:Json ~step_counter () in
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
  let context = make_context options ~output_mode:Json ~step_counter () in
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
  let context = make_context options ~output_mode:Json ~step_counter () in
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

  Printf.printf "📥 SSE request: %d chars, %d steps\n%!" (String.length program)
    step_counter;

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

            let options = { default_options with loop_semantics; step_counter; } in

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

(** {2 Test Runner API}

    Module providing test discovery, execution, and source retrieval for litmus
    tests. *)
module TestRunner = struct
  (** Directory containing litmus test files *)
  let litmus_dir = "litmus-tests"

  (** Path to the CLI executable used for running tests *)
  let cli_executable = "_build/default/cli/main.exe"

  (** [read_litmus_files dir] recursively discovers all .lit files in a
      directory.

      @param dir The root directory to search
      @return A list of file paths to litmus test files *)
  let read_litmus_files dir =
    let rec read_dir_recursive path =
      try
        let files = Sys.readdir path in
          List.concat
            (Array.to_list files
            |> List.map (fun f ->
                let full_path = Filename.concat path f in
                  if Sys.is_directory full_path then
                    read_dir_recursive full_path
                  else if Filename.check_suffix f ".lit" then [ full_path ]
                  else []
            )
            )
      with Sys_error _ -> []
    in
      read_dir_recursive dir

  (** Results from parsing the CLI verification output *)
  type verification_result = {
    valid : bool option;  (** Whether the test passed validation *)
    undefined_behaviour : bool option;
        (** Whether undefined behavior was detected *)
    executions : int option;  (** Number of executions found *)
    events : int option;  (** Number of events in the execution *)
  }

  (** [parse_verification_output output_lines] extracts verification results
      from the CLI output.

      Recognizes lines in the format:
      - "Valid: true" or "Valid: false"
      - "Undefined Behavior: true" or "Undefined Behavior: false"
      - "Executions: <number>"
      - "Events: <number>"

      @param output_lines The output from the CLI as a list of strings
      @return A [verification_result] record with parsed values *)
  let parse_verification_output output_lines =
    let result =
      {
        valid = None;
        undefined_behaviour = None;
        executions = None;
        events = None;
      }
    in
    let parse_bool_line prefix line =
      if
        String.length line > String.length prefix
        && String.sub line 0 (String.length prefix) = prefix
      then
        let value_str =
          String.sub line (String.length prefix)
            (String.length line - String.length prefix)
        in
        let trimmed = String.trim value_str in
          match trimmed with
          | "true" -> Some true
          | "false" -> Some false
          | _ -> None
      else None
    in
    let parse_int_line prefix line =
      if
        String.length line > String.length prefix
        && String.sub line 0 (String.length prefix) = prefix
      then
        let value_str =
          String.sub line (String.length prefix)
            (String.length line - String.length prefix)
        in
          try Some (int_of_string (String.trim value_str))
          with Failure _ -> None
      else None
    in
    let rec process_lines result = function
      | [] -> result
      | line :: rest ->
          let updated_result =
            match parse_bool_line "Valid: " line with
            | Some v -> { result with valid = Some v }
            | None -> (
                match parse_bool_line "Undefined Behavior: " line with
                | Some ub -> { result with undefined_behaviour = Some ub }
                | None -> (
                    match parse_int_line "Executions: " line with
                    | Some n -> { result with executions = Some n }
                    | None -> (
                        match parse_int_line "Events: " line with
                        | Some n -> { result with events = Some n }
                        | None -> result
                      )
                  )
              )
          in
            process_lines updated_result rest
    in
      process_lines result output_lines

  (** [run_cli_on_file filepath] executes the CLI tool on a single test file.

      @param filepath Path to the litmus test file
      @return
        A tuple [(exit_code, output_lines)] where exit_code is 0 for success and
        output_lines is the command output as a string list *)
  let run_cli_on_file filepath =
    let cmd =
      Printf.sprintf "%s run --single \"%s\" 2>&1" cli_executable filepath
    in
    let ic = Unix.open_process_in cmd in
    let output = ref [] in
      try
        while true do
          output := input_line ic :: !output
        done;
        (0, [])
      with End_of_file ->
        let exit_code = Unix.close_process_in ic in
        let status =
          match exit_code with
          | Unix.WEXITED code -> code
          | Unix.WSIGNALED _ -> -1
          | Unix.WSTOPPED _ -> -1
        in
          (status, List.rev !output)

  (** [list_tests_handler request] handles GET requests to list all available
      tests.

      @param request The HTTP request (unused)
      @return A JSON response with format: [{"tests": ["path1", "path2", ...]}]

      Returns HTTP 500 on error with: [{"error": "<message>"}] *)
  let list_tests_handler _request =
    try
      let tests = read_litmus_files litmus_dir in
      let json =
        `Assoc [ ("tests", `List (List.map (fun t -> `String t) tests)) ]
      in
        Dream.json (Yojson.Basic.to_string json)
    with exn ->
      let error = Printexc.to_string exn in
        Dream.json ~status:`Internal_Server_Error
          (Yojson.Basic.to_string (`Assoc [ ("error", `String error) ]))

  (** [run_test_handler request] handles POST requests to run a specific test.

      Expects JSON body: [{"test": "path/to/test.lit"}]

      @param request The HTTP request containing the test path in JSON body
      @return
        A JSON response with test results including:
        - [success]: Overall test success (exit code 0 and valid result)
        - [exit_code]: The CLI exit code
        - [output]: Raw CLI output
        - [parsed]: Whether output was successfully parsed
        - [valid], [undefined_behaviour], [executions], [events]: Parsed results

      Returns HTTP 500 on error with:
      [{"success": false, "error": "<message>", "output": "<message>"}] *)
  let run_test_handler request =
    let* body = Dream.body request in
      try
        let json = Yojson.Basic.from_string body in
        let test_path =
          match json with
          | `Assoc fields -> (
              match List.assoc_opt "test" fields with
              | Some (`String path) -> path
              | _ -> raise (Failure "Missing 'test' field")
            )
          | _ -> raise (Failure "Invalid JSON")
        in

        Printf.printf "🧪 Running test: %s\n%!" test_path;

        let exit_code, output = run_cli_on_file test_path in
        let output_str = String.concat "\n" output in
        let results = parse_verification_output output in

        let success = exit_code = 0 && results.valid <> Some false in

        let response =
          `Assoc
            [
              ("success", `Bool success);
              ("exit_code", `Int exit_code);
              ("output", `String output_str);
              ("parsed", `Bool (results.valid <> None));
              ( "valid",
                match results.valid with
                | Some v -> `Bool v
                | None -> `Null
              );
              ( "undefined_behaviour",
                match results.undefined_behaviour with
                | Some v -> `Bool v
                | None -> `Null
              );
              ( "executions",
                match results.executions with
                | Some n -> `Int n
                | None -> `Null
              );
              ( "events",
                match results.events with
                | Some n -> `Int n
                | None -> `Null
              );
            ]
        in

        Dream.json (Yojson.Basic.to_string response)
      with exn ->
        let error = Printexc.to_string exn in
          Printf.printf "❌ Error running test: %s\n%!" error;
          Dream.json ~status:`Internal_Server_Error
            (Yojson.Basic.to_string
               (`Assoc
                  [
                    ("success", `Bool false);
                    ("error", `String error);
                    ("output", `String error);
                  ]
               )
            )

  (** [get_test_source_handler request] handles GET requests to retrieve test
      source code.

      Expects query parameter: [test=path/to/test.lit]

      @param request The HTTP request with [test] query parameter
      @return A JSON response with format: [{"source": "<file contents>"}]

      Returns:
      - HTTP 400 if [test] parameter is missing:
        [{"error": "Missing 'test' parameter"}]
      - HTTP 404 if file not found: [{"error": "<system error>"}]
      - HTTP 500 on other errors: [{"error": "<message>"}] *)
  let get_test_source_handler request =
    try
      let test_path = Dream.query request "test" |> Option.value ~default:"" in

      if test_path = "" then
        Dream.json ~status:`Bad_Request
          (Yojson.Basic.to_string
             (`Assoc [ ("error", `String "Missing 'test' parameter") ])
          )
      else
        let ic = open_in test_path in
        let source = ref [] in
          ( try
              while true do
                source := input_line ic :: !source
              done
            with End_of_file -> close_in ic
          );

          let source_str = String.concat "\n" (List.rev !source) in
          let response = `Assoc [ ("source", `String source_str) ] in

          Dream.json (Yojson.Basic.to_string response)
    with
    | Sys_error msg ->
        Dream.json ~status:`Not_Found
          (Yojson.Basic.to_string (`Assoc [ ("error", `String msg) ]))
    | exn ->
        let error = Printexc.to_string exn in
          Dream.json ~status:`Internal_Server_Error
            (Yojson.Basic.to_string (`Assoc [ ("error", `String error) ]))
end

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
       [
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
         (* Test Runner API *)
         Dream.get "/api/tests/list" TestRunner.list_tests_handler;
         Dream.post "/api/tests/run" TestRunner.run_test_handler;
         Dream.get "/api/tests/source" TestRunner.get_test_source_handler;
       ]
