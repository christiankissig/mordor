(** Mordor - Main Loop *)

open Context
open Lwt.Syntax
open Types
open Uset

(* Command line options *)
type run_mode = Samples | AllLitmusTests | Single
type command = Run | Parse | Interpret | VisualEs | Dependencies | Futures

let command = ref None
let output_mode = ref None
let run_mode = ref Samples
let litmus_dir = ref "litmus_tests"
let single_file = ref None
let output_file = ref None
let recursive = ref false
let step_counter = ref None
let use_finite_step_counter_semantics = ref false
let use_step_counter_per_loop = ref true

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

(* Pretty print results *)
let print_results (lwt_ctx : mordor_ctx Lwt.t) =
  let* ctx = lwt_ctx in
    Printf.printf "=== Verification Results ===\n";
    ( match ctx.valid with
    | None -> Printf.printf "Valid: Unknown\n"
    | Some valid -> Printf.printf "Valid: %b\n" valid
    );
    ( match ctx.undefined_behaviour with
    | None -> Printf.printf "Undefined Behavior: Unknown\n"
    | Some ub -> Printf.printf "Undefined Behavior: %b\n" ub
    );
    ( match ctx.executions with
    | None -> Printf.printf "Executions: Unknown\n"
    | Some executions -> Printf.printf "Executions: %d\n" (USet.size executions)
    );
    ( match ctx.structure with
    | None -> Printf.printf "Events: Unknown\n"
    | Some structure -> Printf.printf "Events: %d\n" (USet.size structure.e)
    );
    Printf.printf "===========================\n";
    flush stdout;
    Lwt.return_unit

(* Read all .lit files from a directory *)
let read_litmus_files dir =
  let rec read_dir_recursive path =
    try
      let files = Sys.readdir path in
        List.concat
          (Array.to_list files
          |> List.map (fun f ->
              let full_path = Filename.concat path f in
                if Sys.is_directory full_path && !recursive then
                  read_dir_recursive full_path
                else if Filename.check_suffix f ".lit" then [ full_path ]
                else []
          )
          )
    with Sys_error msg ->
      Printf.eprintf "Error reading directory %s: %s\n" path msg;
      []
  in
  let lit_files = read_dir_recursive dir in
    List.map
      (fun path ->
        let name = Filename.basename path in
        let ic = open_in path in
        let content = really_input_string ic (in_channel_length ic) in
          close_in ic;
          (name, content)
      )
      lit_files

(* Run verification *)
let verify_program program options =
  let context = make_context options () in
    context.litmus <- Some program;
    Lwt.return context
    |> Parse.step_parse_litmus
    |> Interpret.step_interpret
    |> Symmrd.step_calculate_dependencies

let run_single name program =
  Printf.printf "Running program %s.\n" name;
  Printf.printf "===================\n";
  Printf.printf "\n=== Running: %s ===\n" name;
  Printf.printf "Program:\n%s\n\n" program;
  flush stdout;
  verify_program program default_options |> print_results

let run_tests tests =
  Logs.info (fun m -> m "Running %d tests." (List.length tests));
  let* () = Lwt_list.iter_s (fun (name, prog) -> run_single name prog) tests in
    flush stdout;
    Lwt.return_unit

let parse_single name program options =
  let context = make_context options () in
    context.litmus_name <- Some name;
    context.litmus <- Some program;
    Lwt.return context |> Parse.step_parse_litmus |> print_results

let parse_tests tests options =
  let* () =
    Lwt_list.iter_s (fun (name, prog) -> parse_single name prog options) tests
  in
    Lwt.return_unit

let interpret_single name program options step_counter =
  Logs.info (fun m -> m "Interpreting program %s." name);
  let context = make_context options ~step_counter () in
    context.litmus <- Some program;
    Lwt.return context
    |> Parse.step_parse_litmus
    |> Interpret.step_interpret
    |> print_results

let interpret_tests tests options step_counter =
  let* () =
    Lwt_list.iter_s
      (fun (name, prog) -> interpret_single name prog options step_counter)
      tests
  in
    flush stdout;
    Lwt.return_unit

let futures_single (name, program) options output_mode output_file step_counter
    =
  let context =
    make_context options ~output_mode ~output_file ~step_counter ()
  in
    context.litmus_name <- Some name;
    context.litmus <- Some program;
    Lwt.return context
    |> Parse.step_parse_litmus
    |> Interpret.step_interpret
    |> Symmrd.step_calculate_dependencies
    |> Futures.step_futures
    |> Futures.print_futures
    |> print_results

let visualize_es_single (name, program) options output_mode output_file
    step_counter =
  let context =
    make_context options ~output_mode ~output_file ~step_counter ()
  in
    context.litmus_name <- Some name;
    context.litmus <- Some program;
    Lwt.return context
    |> Parse.step_parse_litmus
    |> Interpret.step_interpret
    |> Eventstructureviz.step_visualize_event_structure
    |> print_results

let usage_msg =
  "Usage: main COMMAND [OPTIONS]\n\n\
   Commands:\n\
  \  run           Run verification on input programs\n\
  \  parse         Parse the input program\n\
  \  interpret     Run verification\n\
  \  visual-es     Visualize event structure (single file only)\n\
  \  futures       Compute futures (single file only)\n\
   Options:"

let specs =
  [
    (* inputs *)
    ( "--all-litmus-tests",
      Arg.String
        (fun dir ->
          run_mode := AllLitmusTests;
          litmus_dir := dir
        ),
      " Process all .lit files in the specified directory (default: \
       litmus_tests)"
    );
    ( "-r",
      Arg.Set recursive,
      " Scan directories recursively (use with --all-litmus-tests)"
    );
    ( "--single",
      Arg.String
        (fun filename ->
          run_mode := Single;
          single_file := Some filename
        ),
      " Process a single .lit file specified by filename"
    );
    ( "--samples",
      Arg.Unit (fun () -> run_mode := Samples),
      " Run built-in sample programs (default)"
    );
    (* outputs *)
    ( "--output-mode",
      Arg.String (fun s -> output_mode := Some (parse_output_mode s)),
      " Output mode: json/dot/html (for visual-es), or isa/json (for \
       parse/futures)"
    );
    ( "--output-file",
      Arg.String (fun s -> output_file := Some s),
      " Output file for visual-es, parse, or futures command (default: stdout \
       or auto-generated)"
    );
    (* loop semantics *)
    ( "--step-counter",
      Arg.Int
        (fun n ->
          use_finite_step_counter_semantics := true;
          use_step_counter_per_loop := false;
          step_counter := Some n
        ),
      " Number of steps for interpretation (default: 5)"
    );
    ( "--step-counter-per-loop",
      Arg.Int
        (fun n ->
          use_finite_step_counter_semantics := true;
          use_step_counter_per_loop := true;
          step_counter := Some n
        ),
      " Number of steps for interpretation (default: 5)"
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
            "Valid commands: run, parse, interpret, visual-es, futures\n";
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

  let options =
    {
      default_options with
      use_finite_step_counter_semantics = !use_finite_step_counter_semantics;
      use_step_counter_per_loop = !use_step_counter_per_loop;
    }
  in

  let assert_single_test =
    if List.length tests <> 1 then (
      Printf.eprintf
        "Error: command requires exactly one input program (use --single)\n";
      exit 1
    )
  in

  (* Handle the command *)
  match cmd with
  | Run -> run_tests tests
  | Parse -> parse_tests tests options
  | Interpret ->
      interpret_tests tests options (Option.value !step_counter ~default:5)
  | Futures ->
      assert_single_test;
      futures_single (List.hd tests) options
        (Option.value !output_mode ~default:Json)
        (Option.value !output_file ~default:"stdout")
        (Option.value !step_counter ~default:5)
  | VisualEs ->
      assert_single_test;
      visualize_es_single (List.hd tests) options
        (Option.value !output_mode ~default:Dot)
        (Option.value !output_file ~default:"stdout")
        (Option.value !step_counter ~default:5)
  | _ ->
      Printf.printf "TODO: not implemented yet\n";
      Lwt.return_unit

(* Add this function before the main function *)
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
  Lwt_main.run (main ())
