(** Integration tests for litmus test files *)

open Lwt.Syntax

(* Configuration *)
let litmus_dir = "litmus-tests"
let cli_executable = "_build/default/src/main.exe"

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
    Alcotest.(check int)
      (Printf.sprintf "CLI should exit successfully for %s" filepath)
      0 exit_code;

    (* Optional: Check that we got some verification results *)
    Alcotest.(check bool)
      (Printf.sprintf "Output should contain results for %s" filepath)
      true
      (String.length output_str > 0)

(* Generate test cases from litmus files *)
let litmus_test_cases () =
  let files = read_litmus_files litmus_dir in
    List.map
      (fun filepath ->
        let test_name = Filename.basename filepath in
          Alcotest.test_case test_name `Quick (test_litmus_file filepath)
      )
      files

(* Test suite *)
let suite = ("Integration Tests - Litmus Tests", litmus_test_cases ())
