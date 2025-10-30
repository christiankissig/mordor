(** Main entry point for sMRD *)
open Lwt.Syntax

open Types
open Symmrd

(** Run verification *)
let verify_program program options =
  let* result = create_symbolic_event_structure program options in
    Lwt.return result

(** Pretty print results *)
let print_results (result : result) =
  Printf.printf "=== Verification Results ===\n";
  Printf.printf "Valid: %b\n" result.valid;
  Printf.printf "Undefined Behavior: %b\n" result.ub;
  Printf.printf "Executions: %d\n" (List.length result.executions);
  Printf.printf "Events: %d\n" (Uset.size result.structure.e);
  Printf.printf "===========================\n";
  flush stdout

(** Example programs *)
let example_programs =
  [
    ( "Store Buffering",
      {|
name = SB
%%
{ x := 1 } ||| { y := 1 }
%% allow (x = 0 && y = 0) [rc11]
  |}
    );
    ( "Message Passing",
      {|
name = MP
%%
{ x := 1; y := 1 } ||| { r1 := y; r2 := x }
%% forbid (r1 = 1 && r2 = 0) [rc11]
  |}
    );
    ( "Load Buffering",
      {|
name = LB
%%
{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }
%% forbid (r1 = 1 && r2 = 1) [rc11]
  |}
    );
  ]

(** Run example *)
let run_example name program =
  Printf.printf "\n=== Running: %s ===\n" name;
  Printf.printf "Program:\n%s\n\n" program;
  flush stdout;

  let* result = verify_program program default_options in
    print_results result;
    Lwt.return_unit

(** Read all .lit files from a directory *)
let read_litmus_files dir =
  try
    let files = Sys.readdir dir in
    let lit_files =
      Array.to_list files
      |> List.filter (fun f -> Filename.check_suffix f ".lit")
      |> List.map (fun f -> Filename.concat dir f)
    in
      List.map
        (fun path ->
          let name = Filename.basename path in
          let ic = open_in path in
          let content = really_input_string ic (in_channel_length ic) in
            close_in ic;
            (name, content)
        )
        lit_files
  with Sys_error msg ->
    Printf.eprintf "Error reading directory: %s\n" msg;
    []

(** Run tests from a list of (name, program) pairs *)
let run_tests tests =
  Printf.printf "MoRDor - Symbolic Modular Relaxed Dependencies\n";
  flush stdout;

  let* () =
    Lwt_list.iter_s
      (fun (name, prog) ->
        Printf.printf "Running program %s.\n" name;
        Printf.printf "===================\n";
        run_example name prog
      )
      tests
  in
    flush stdout;
    Lwt.return_unit

(** Command line options *)
type run_mode = Samples | AllLitmusTests

let run_mode = ref Samples
let litmus_dir = ref "litmus_tests"
let usage_msg = "Usage: main [--samples | --all-litmus-tests [dir]]"

let specs =
  [
    ( "--samples",
      Arg.Unit (fun () -> run_mode := Samples),
      " Run built-in sample programs (default)"
    );
    ( "--all-litmus-tests",
      Arg.String
        (fun dir ->
          run_mode := AllLitmusTests;
          litmus_dir := dir
        ),
      " Process all .lit files in the specified directory (default: \
       litmus_tests)"
    );
  ]

(** Main entry point *)
let main () =
  (* Parse command line arguments *)
  Arg.parse specs (fun _ -> ()) usage_msg;

  (* Determine which tests to run *)
  let tests =
    match !run_mode with
    | Samples -> example_programs
    | AllLitmusTests ->
        let litmus_tests = read_litmus_files !litmus_dir in
          if List.length litmus_tests = 0 then (
            Printf.eprintf "Warning: No .lit files found in %s\n" !litmus_dir;
            []
          )
          else litmus_tests
  in

  run_tests tests

let () = Lwt_main.run (main ())
