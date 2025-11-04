(** Mordor - Main Loop *)

open Lwt.Syntax
open Types
open Symmrd
open Eventstructureviz
open Uset

(* Command line options *)
type run_mode = Samples | AllLitmusTests | Single
type output_mode = Json | Html | Dot
type command = Run | Parse | Interpret | VisualEs | Dependencies | Futures

let command = ref None
let output_mode = ref None
let run_mode = ref Samples
let litmus_dir = ref "litmus_tests"
let single_file = ref None
let output_file = ref None

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
  Printf.printf "Events: %d\n" (USet.size result.structure.e);
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

let run_single name program =
  Printf.printf "Running program %s.\n" name;
  Printf.printf "===================\n";
  Printf.printf "\n=== Running: %s ===\n" name;
  Printf.printf "Program:\n%s\n\n" program;
  flush stdout;
  let* result = verify_program program default_options in
    print_results result;
    Lwt.return_unit

let run_tests tests =
  Logs.info (fun m -> m "Running %d tests." (List.length tests));
  let* () = Lwt_list.iter_s (fun (name, prog) -> run_single name prog) tests in
    flush stdout;
    Lwt.return_unit

let parse_single name program =
  Logs.info (fun m -> m "Parsing program %s." name);
  let _ast, _program_stmts = Symmrd.parse_program program in
    Logs.info (fun m -> m "Parsed program %s successfully." name);
    Lwt.return_unit

let parse_tests tests =
  let* () =
    Lwt_list.iter_s (fun (name, prog) -> parse_single name prog) tests
  in
    flush stdout;
    Lwt.return_unit

let interpret_single name program =
  Logs.info (fun m -> m "Interpreting program %s." name);
  let _, program_stmts = Symmrd.parse_program program in
    let* _result =
      Interpret.interpret program_stmts [] (Hashtbl.create 16) []
    in
      Printf.printf "Interpreted program %s successfully.\n" name;
      flush stdout;
      Lwt.return_unit

let interpret_tests tests =
  let* () =
    Lwt_list.iter_s (fun (name, prog) -> interpret_single name prog) tests
  in
    flush stdout;
    Lwt.return_unit

let visualize_event_structure (mode : output_mode) output_file (name, program) =
  Printf.printf "Visualizing event structure for program %s.\n" name;
  flush stdout;
  let opts = { default_options with just_structure = true } in
    let* result = create_symbolic_event_structure program opts in
      match mode with
      | Json ->
          let json =
            EventStructureViz.visualize EventStructureViz.JSON result.structure
              result.events
          in
            ( if output_file = "stdout" then Printf.printf "%s\n" json
              else
                let oc = open_out output_file in
                  output_string oc json;
                  close_out oc
            );
            Lwt.return_unit
      | Dot ->
          let dot =
            EventStructureViz.visualize EventStructureViz.DOT result.structure
              result.events
          in
            ( if output_file = "stdout" then Printf.printf "%s\n" dot
              else
                let oc = open_out output_file in
                  output_string oc dot;
                  close_out oc
            );
            Lwt.return_unit
      | Html ->
          Printf.eprintf "HTML output not implemented yet.\n";
          Lwt.return_unit

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
    ( "--output-file",
      Arg.String (fun s -> output_file := Some s),
      " Output file for visual-es command (default: stdout)"
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
    ( "--single",
      Arg.String
        (fun filename ->
          run_mode := Single;
          single_file := Some filename
        ),
      " Process a single .lit file specified by filename"
    );
  ]

let anon_fun arg =
  match !command with
  | None -> (
      match String.lowercase_ascii arg with
      | "run" -> command := Some Run
      | "parse" -> command := Some Parse
      | "interpret" -> command := Some Interpret
      | "visual-es" -> command := Some VisualEs
      | "futures" -> command := Some Futures
      | "dependencies" -> command := Some Dependencies
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
  Printf.printf "MoRDor - Symbolic Modular Relaxed Dependencies\n";
  flush stdout;

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
    | Single -> (
        match !single_file with
        | None ->
            Printf.eprintf "Error: --single option requires a filename\n";
            exit 1
        | Some filename ->
            let ic = open_in filename in
            let content = really_input_string ic (in_channel_length ic) in
              close_in ic;
              [ (Filename.basename filename, content) ]
      )
  in

  (* Handle the command *)
  match cmd with
  | Run -> run_tests tests
  | Parse -> parse_tests tests
  | Interpret -> interpret_tests tests
  | VisualEs ->
      if List.length tests <> 1 then (
        Printf.eprintf
          "Error: visual-es command requires exactly one input program\n";
        exit 1
      );
      let output_file =
        match !output_file with
        | None -> "stdout"
        | Some f -> f
      in
        Printf.printf "Generating visualization to %s\n" output_file;
        let mode =
          match !output_mode with
          | None ->
              Printf.eprintf
                "Error: --output-mode is required for visual-es command\n";
              Printf.eprintf "Valid modes: json, html, dot\n";
              exit 1
          | Some m -> m
        in
          visualize_event_structure mode output_file (List.hd tests)
  | _ ->
      Printf.printf "TODO: not implemented yet\n";
      Lwt.return_unit

let () =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  Lwt_main.run (main ())
