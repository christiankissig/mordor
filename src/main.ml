(* Main entry point for sMRD *)
open Lwt.Syntax
open Types
open Symmrd

(* Run verification *)
let verify_program program options =
  let* result = create_symbolic_event_structure program options in
    Lwt.return result

(* Pretty print results *)
let print_results (result : result) =
  Printf.printf "=== Verification Results ===\n";
  Printf.printf "Valid: %b\n" result.valid;
  Printf.printf "Undefined Behavior: %b\n" result.ub;
  Printf.printf "Executions: %d\n" (List.length result.executions);
  Printf.printf "Events: %d\n" (Uset.size result.structure.e);
  Printf.printf "===========================\n";
  flush stdout

(* Example programs *)
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

(* Run example *)
let run_example name program =
  Printf.printf "\n=== Running: %s ===\n" name;
  Printf.printf "Program:\n%s\n\n" program;
  flush stdout;
  let* result = verify_program program default_options in
    print_results result;
    Lwt.return_unit

(* Read all .lit files from a directory *)
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

(* Run tests from a list of (name, program) pairs *)
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

(* Command line options *)
type run_mode = Samples | AllLitmusTests
type output_mode = Json | Html | Dot
type command = Parse | Interpret | VisualEs | Futures

let command = ref None
let output_mode = ref None
let run_mode = ref Samples
let litmus_dir = ref "litmus_tests"

let usage_msg =
  "Usage: main COMMAND [OPTIONS]\n\n\
   Commands:\n\
  \  parse         Parse the input program\n\
  \  interpret     Run verification\n\
  \  visual-es     Visualize event structure\n\
  \  futures       Compute futures\n\n\
   Options:"

let parse_output_mode s =
  match String.lowercase_ascii s with
  | "json" -> Json
  | "html" -> Html
  | "dot" -> Dot
  | _ ->
      Printf.eprintf
        "Error: Invalid output mode '%s' (must be json, html, or dot)\n" s;
      exit 1

let specs =
  [
    ( "--output-mode",
      Arg.String (fun s -> output_mode := Some (parse_output_mode s)),
      " Output mode for visual-es command: json, html, or dot"
    );
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

let anon_fun arg =
  match !command with
  | None -> (
      match String.lowercase_ascii arg with
      | "parse" -> command := Some Parse
      | "interpret" -> command := Some Interpret
      | "visual-es" -> command := Some VisualEs
      | "futures" -> command := Some Futures
      | _ ->
          Printf.eprintf "Error: Unknown command '%s'\n" arg;
          Printf.eprintf
            "Valid commands: parse, interpret, visual-es, futures\n";
          exit 1
    )
  | Some _ ->
      Printf.eprintf "Error: Multiple commands specified\n";
      exit 1

(* Main entry point *)
let main () =
  (* Parse command line arguments *)
  Arg.parse specs anon_fun usage_msg;

  (* Check that a command was specified *)
  let cmd =
    match !command with
    | None ->
        Printf.eprintf "Error: No command specified\n\n";
        Arg.usage specs usage_msg;
        exit 1
    | Some c -> c
  in

  (* Handle the command *)
  match cmd with
  | Parse ->
      Printf.printf "TODO: Implement parse command\n";
      Lwt.return_unit
  | Interpret ->
      (* Determine which tests to run *)
      let tests =
        match !run_mode with
        | Samples -> example_programs
        | AllLitmusTests ->
            let litmus_tests = read_litmus_files !litmus_dir in
              if List.length litmus_tests = 0 then (
                Printf.eprintf "Warning: No .lit files found in %s\n"
                  !litmus_dir;
                []
              )
              else litmus_tests
      in
        run_tests tests
  | VisualEs ->
      let mode =
        match !output_mode with
        | None ->
            Printf.eprintf
              "Error: --output-mode is required for visual-es command\n";
            Printf.eprintf "Valid modes: json, html, dot\n";
            exit 1
        | Some m -> m
      in
        ( match mode with
        | Json -> Printf.printf "TODO: Implement visual-es with JSON output\n"
        | Html -> Printf.printf "TODO: Implement visual-es with HTML output\n"
        | Dot -> Printf.printf "TODO: Implement visual-es with DOT output\n"
        );
        Lwt.return_unit
  | Futures ->
      Printf.printf "TODO: Implement futures command\n";
      Lwt.return_unit

let () = Lwt_main.run (main ())
