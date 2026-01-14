(** Test Runner API - Server-side handlers for running litmus tests *)

open Lwt.Syntax

(* Configuration *)
let litmus_dir = "litmus-tests"
let cli_executable = "_build/default/cli/main.exe"

(* Read all .lit files from directory recursively *)
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

(* Parse verification results from CLI output *)
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

(* Execute CLI command and capture result *)
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

(* API Handlers *)

(* GET /api/tests/list - List all available litmus tests *)
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

(* POST /api/tests/run - Run a specific litmus test *)
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

    Printf.printf "Running test: %s\n%!" test_path;

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
    Printf.printf "Error running test: %s\n%!" error;
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

(* GET /api/tests/source?test=<path> - Get source code of a test file *)
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

(* Routes to add to main server *)
let routes =
  [
    Dream.get "/api/tests/list" list_tests_handler;
    Dream.post "/api/tests/run" run_test_handler;
    Dream.get "/api/tests/source" get_test_source_handler;
  ]
