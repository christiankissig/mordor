(** Mordor Web Server *)

open Lwt.Syntax
open Context
open Types
open Source_info
open Test_runner_api

let visualize_to_stream program options step_counter stream =
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
      |> Symmrd.step_calculate_dependencies
      |> Assertion.step_check_assertions
      |> Eventstructureviz.step_send_execution_graphs ~send_data
    in

    Lwt.return ctx

let sse_data json_obj =
  let json_str = Yojson.Basic.to_string json_obj in
    Printf.sprintf "data: %s\n\n" json_str

let visualize_sse_handler request =
  let program = Dream.query request "program" |> Option.value ~default:"" in

  let loop_semantics =
    Dream.query request "loop_semantics"
    |> Option.value ~default:"finite-step-counter"
  in

  let loop_semantics =
    match String.lowercase_ascii loop_semantics with
    | "symbolic" -> Symbolic
    | "step-counter" -> StepCounterPerLoop
    | _ -> StepCounterPerLoop
  in

  let step_counter =
    match loop_semantics with
    | Generic | Symbolic -> 0
    | StepCounterPerLoop | FiniteStepCounter ->
        Dream.query request "steps"
        |> Option.map int_of_string
        |> Option.value ~default:2
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

            let options = { default_options with loop_semantics } in

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

                let* _ctx =
                  Lwt.catch
                    (fun () ->
                      visualize_to_stream program options step_counter stream
                    )
                    (fun exn ->
                      let error = Printexc.to_string exn in
                        Printf.printf "❌ Error: %s\n%!" error;
                        let* () =
                          Dream.write stream
                            (sse_data (`Assoc [ ("error", `String error) ]))
                        in
                          let* () = Dream.flush stream in
                            Lwt.fail exn
                    )
                in

                Printf.printf "🎉 Complete!\n%!";
                Dream.close stream
        )
        (fun exn ->
          Printf.printf "❌ SSE error: %s\n%!" (Printexc.to_string exn);
          let* () =
            Dream.write stream
              (sse_data (`Assoc [ ("error", `String (Printexc.to_string exn)) ]))
          in
            Dream.close stream
        )
    )

let health_handler _request = Dream.json "{\"status\": \"ok\"}"

(* Test Runner API *)
module TestRunner = struct
  let litmus_dir = "litmus-tests"
  let cli_executable = "_build/default/cli/main.exe"

  let read_litmus_files dir =
    let rec read_dir_recursive path =
      try
        let files = Sys.readdir path in
        List.concat
          (Array.to_list files
          |> List.map (fun f ->
              let full_path = Filename.concat path f in
              if Sys.is_directory full_path then read_dir_recursive full_path
              else if Filename.check_suffix f ".lit" then [ full_path ]
              else []
            )
          )
      with Sys_error _ -> []
    in
    read_dir_recursive dir

  type verification_result = {
    valid : bool option;
    undefined_behaviour : bool option;
    executions : int option;
    events : int option;
  }

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

  let run_cli_on_file filepath =
    let cmd = Printf.sprintf "%s run --single \"%s\" 2>&1" cli_executable filepath in
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

  let list_tests_handler _request =
    try
      let tests = read_litmus_files litmus_dir in
      let json =
        `Assoc [ ("tests", `List (List.map (fun t -> `String t) tests)) ]
      in
      Dream.json (Yojson.Basic.to_string json)
    with exn ->
      let error = Printexc.to_string exn in
      Dream.json
        ~status:`Internal_Server_Error
        (Yojson.Basic.to_string
           (`Assoc [ ("error", `String error) ])
        )

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
      Dream.json
        ~status:`Internal_Server_Error
        (Yojson.Basic.to_string
           (`Assoc
             [
               ("success", `Bool false);
               ("error", `String error);
               ("output", `String error);
             ]
           )
        )

  let get_test_source_handler request =
    try
      let test_path = Dream.query request "test" |> Option.value ~default:"" in

      if test_path = "" then
        Dream.json
          ~status:`Bad_Request
          (Yojson.Basic.to_string
             (`Assoc [ ("error", `String "Missing 'test' parameter") ])
          )
      else
        let ic = open_in test_path in
        let source = ref [] in
        (try
           while true do
             source := input_line ic :: !source
           done
         with End_of_file -> close_in ic);

        let source_str = String.concat "\n" (List.rev !source) in
        let response = `Assoc [ ("source", `String source_str) ] in

        Dream.json (Yojson.Basic.to_string response)
    with
    | Sys_error msg ->
        Dream.json
          ~status:`Not_Found
          (Yojson.Basic.to_string (`Assoc [ ("error", `String msg) ]))
    | exn ->
        let error = Printexc.to_string exn in
        Dream.json
          ~status:`Internal_Server_Error
          (Yojson.Basic.to_string (`Assoc [ ("error", `String error) ]))
end

(* Setup logging *)
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

let () =
  setup_logs ();
  Printexc.record_backtrace true;
  Printf.printf "🔮 Mordor Web - Graph Visualization & Test Runner\n";
  Printf.printf "🌐 http://localhost:8080\n\n";

  Dream.run ~interface:"0.0.0.0" ~port:8080
  @@ Dream.logger
  @@ Dream.router
       [
         Dream.get "/" (Dream.from_filesystem "web/frontend" "index.html");
         Dream.get "/static/**" (Dream.static "web/frontend/static");
         Dream.get "/health" health_handler;
         Dream.get "/api/visualize/stream" visualize_sse_handler;
         (* Test Runner API *)
         Dream.get "/api/tests/list" TestRunner.list_tests_handler;
         Dream.post "/api/tests/run" TestRunner.run_test_handler;
         Dream.get "/api/tests/source" TestRunner.get_test_source_handler;
       ]
