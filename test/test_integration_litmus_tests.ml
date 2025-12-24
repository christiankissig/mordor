(** Integration tests for litmus test files *)

open Lwt.Syntax

(* Configuration *)
let litmus_dir = "litmus-tests"
let cli_executable = "_build/default/cli/main.exe"

(* Read all .lit files from directory *)
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
    with Sys_error msg ->
      Printf.eprintf "Error reading directory %s: %s\n" path msg;
      []
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
  let cmd = Printf.sprintf "%s run --single \"%s\"" cli_executable filepath in
  let ic = Unix.open_process_in cmd in
  let output = ref [] in
    try
      while true do
        output := input_line ic :: !output
      done;
      (0, []) (* Never reached *)
    with End_of_file ->
      let exit_code = Unix.close_process_in ic in
      let status =
        match exit_code with
        | Unix.WEXITED code -> code
        | Unix.WSIGNALED _ -> -1
        | Unix.WSTOPPED _ -> -1
      in
        (status, List.rev !output)

(* Test that CLI runs successfully on a litmus file *)
let test_litmus_file filepath () =
  let exit_code, output = run_cli_on_file filepath in
  let output_str = String.concat "\n" output in

  (* Check that CLI exited successfully *)
  Alcotest.(check int)
    (Printf.sprintf "CLI should exit successfully for %s" filepath)
    0 exit_code;

  (* Check that we got some output *)
  Alcotest.(check bool)
    (Printf.sprintf "Output should contain results for %s" filepath)
    true
    (String.length output_str > 0);

  (* Parse the verification results *)
  let results = parse_verification_output output in

  (* Check that we got a validity result *)
  Alcotest.(check bool)
    (Printf.sprintf "Should have validity result for %s" filepath)
    true (results.valid <> None);

  (* Check that the assertion was valid (no assertion failures) *)
  ( match results.valid with
  | Some true ->
      Printf.printf "✓ %s: Assertion VALID\n" (Filename.basename filepath)
  | Some false ->
      Printf.printf "✗ %s: Assertion INVALID\n" (Filename.basename filepath);
      (* Optionally fail the test if assertion is invalid *)
      Alcotest.(check bool)
        (Printf.sprintf "Assertion should be valid for %s" filepath)
        true false
  | None ->
      Alcotest.fail (Printf.sprintf "No validity result found for %s" filepath)
  );

  (* Report undefined behavior if detected *)
  match results.undefined_behaviour with
  | Some true ->
      Printf.printf "⚠ %s: Undefined Behavior detected\n"
        (Filename.basename filepath)
  | Some false ->
      Printf.printf "✓ %s: No Undefined Behavior\n" (Filename.basename filepath)
  | None -> ()

(* Alternative test that only checks for successful execution without failing on invalid assertions *)
let test_litmus_file_permissive filepath () =
  let exit_code, output = run_cli_on_file filepath in
  let output_str = String.concat "\n" output in

  (* Check that CLI exited successfully *)
  Alcotest.(check int)
    (Printf.sprintf "CLI should exit successfully for %s" filepath)
    0 exit_code;

  (* Check that we got some output *)
  Alcotest.(check bool)
    (Printf.sprintf "Output should contain results for %s" filepath)
    true
    (String.length output_str > 0);

  (* Parse and report the verification results *)
  let results = parse_verification_output output in

  (* Report validity status *)
  match results.valid with
  | Some true ->
      Printf.printf "✓ %s: Assertion VALID\n" (Filename.basename filepath)
  | Some false ->
      Printf.printf "✗ %s: Assertion INVALID (but test passes)\n"
        (Filename.basename filepath)
  | None -> (
      Printf.printf "? %s: No validity result found\n"
        (Filename.basename filepath);

      (* Report undefined behavior if detected *)
      match results.undefined_behaviour with
      | Some true ->
          Printf.printf "⚠ %s: Undefined Behavior detected\n"
            (Filename.basename filepath)
      | Some false ->
          Printf.printf "✓ %s: No Undefined Behavior\n"
            (Filename.basename filepath)
      | None -> (
          ();

          (* Report execution count if available *)
          match results.executions with
          | Some n -> Printf.printf "  Executions: %d\n" n
          | None -> (
              ();

              (* Report event count if available *)
              match results.events with
              | Some n -> Printf.printf "  Events: %d\n" n
              | None -> ()
            )
        )
    )

(* Generate test cases from litmus files *)
let litmus_test_cases ~strict =
  let files = read_litmus_files litmus_dir in
  let test_fn =
    if strict then test_litmus_file else test_litmus_file_permissive
  in
    List.map
      (fun filepath ->
        let test_name = filepath in
          Alcotest.test_case test_name `Quick (test_fn filepath)
      )
      files

(* Test suites *)
let suite_strict =
  ("Integration Tests - Litmus Tests Strict", litmus_test_cases ~strict:true)

let suite_permissive =
  ( "Integration Tests - Litmus Tests Permissive",
    litmus_test_cases ~strict:false
  )

(* Default suite is permissive to allow reporting without failing *)
let suite = suite_permissive
