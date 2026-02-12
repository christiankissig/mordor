(** {1 Mordor - Main Loop}

    This module provides the main entry point and command-line interface for the
    Mordor (Symbolic Modular Relaxed Dependencies) verification tool.

    The module is organized into several logical sections:
    - Configuration and command types
    - Example programs for testing
    - File I/O operations
    - Verification pipelines for each command
    - Command-line interface

    @author Mordor Team *)

open Context
open Lwt.Syntax
open Types
open Uset

(** {1 Configuration Types} *)

module Config = struct
  (** Mode for selecting which programs to run. *)
  type run_mode =
    | Samples  (** Run built-in sample programs *)
    | AllLitmusTests of { dir : string; recursive : bool }
        (** Run all .lit files in a directory *)
    | Single of string  (** Run a single specified file *)
  [@@deriving show]

  (** Available commands for the Mordor tool.

      Each command represents a different stage or aspect of the verification
      pipeline that can be run independently. *)
  type command =
    | Run
        (** Run full verification: parse → interpret → dependencies → assertions
        *)
    | Parse  (** Parse only: convert litmus test to IR *)
    | Interpret  (** Parse and interpret: generate event structure *)
    | Episodicity
        (** Check episodicity: analyze loop properties (requires single file) *)
    | VisualEs
        (** Visualize event structure: generate graphical representation
            (requires single file) *)
    | Dependencies  (** Compute dependencies: calculate dependency relations *)
    | Futures
        (** Compute futures: calculate possible future states (requires single
            file) *)
  [@@deriving show]

  (** Complete configuration for a Mordor run.

      This encapsulates all command-line options and settings needed to execute
      an analysis. *)
  type t = {
    command : command;  (** Which analysis to perform *)
    run_mode : run_mode;  (** Which programs to analyze *)
    output_mode : output_mode option;  (** Output format (if applicable) *)
    output_file : string option;  (** Output file path (if applicable) *)
    step_counter : int option;  (** Loop iteration bound (if applicable) *)
    options : Context.options;  (** Detailed analysis options *)
  }
  [@@deriving show]
end

(** {1 Example Programs} *)

module Examples = struct
  (** Built-in example programs for testing and demonstration.

      These are classic concurrent program patterns used in memory model
      research:

      - {b Store Buffering (SB)}: Tests whether independent stores can be
        reordered, potentially allowing both threads to read initial values.
      - {b Message Passing (MP)}: Tests release-acquire synchronization where
        one thread sends a message through a shared variable.
      - {b Load Buffering (LB)}: Tests cyclic dependencies where each thread's
        read depends on the other thread's write. *)

  (** Store Buffering test.

      Tests if two independent stores can be reordered such that both reads
      observe initial values (0). This is allowed under relaxed memory models
      but forbidden under sequential consistency. *)
  let store_buffering =
    ( "Store Buffering",
      {|
name = SB
%%
{ x := 1 } ||| { y := 1 }
%% allow (x = 0 && y = 0) []
  |}
    )

  (** Message Passing test.

      Tests release-acquire synchronization. Thread 1 writes data then sets a
      flag; thread 2 reads the flag then reads data. The outcome where the flag
      is observed but not the data should be forbidden. *)
  let message_passing =
    ( "Message Passing",
      {|
name = MP
%%
{ x := 1; y := 1 } ||| { r1 := y; r2 := x }
%% forbid (r1 = 1 && r2 = 0) []
  |}
    )

  (** Load Buffering test.

      Tests cyclic dependencies between loads and stores. Both threads read a
      variable then write to another, creating a cycle that should be forbidden.
  *)
  let load_buffering =
    ( "Load Buffering",
      {|
name = LB
%%
{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }
%% forbid (r1 = 1 && r2 = 1) []
  |}
    )

  (** All example programs as a list. *)
  let all = [ store_buffering; message_passing; load_buffering ]
end

(** {1 File I/O} *)

module FileIO = struct
  (** Read a single litmus test file.

      @param filename Path to the .lit file
      @return A (name, content) pair where name is the basename
      @raise Sys_error if the file cannot be read *)
  let read_single_file filename =
    let name = Filename.basename filename in
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
      close_in ic;
      (name, content)

  (** Read all .lit files from a directory, optionally recursively.

      Scans the directory for files with .lit extension. If recursive is true,
      also scans all subdirectories. Errors reading individual files are logged
      but don't halt the scan.

      @param dir The directory path to scan
      @param recursive Whether to scan subdirectories
      @return A list of (filename, content) pairs for all found litmus tests *)
  let read_litmus_files ~dir ~recursive =
    (* Recursively scan a directory for .lit files.

       @param path Current directory path
       @return List of full paths to .lit files *)
    let rec read_dir_recursive path =
      try
        let files = Sys.readdir path in
          List.concat
            (Array.to_list files
            |> List.map (fun f ->
                let full_path = Filename.concat path f in
                  if Sys.is_directory full_path && recursive then
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
      List.map read_single_file lit_files

  (** Load test programs based on run mode.

      Dispatches to the appropriate loading mechanism based on the run mode:
      - Samples: Returns built-in examples
      - AllLitmusTests: Scans directory for .lit files
      - Single: Loads one specified file

      @param run_mode The mode specifying which programs to load
      @return A list of (name, program) pairs *)
  let load_tests = function
    | Config.Samples -> Examples.all
    | Config.AllLitmusTests { dir; recursive } ->
        let tests = read_litmus_files ~dir ~recursive in
          if List.length tests = 0 then
            Printf.eprintf "Warning: No .lit files found in %s\n" dir;
          tests
    | Config.Single filename -> [ read_single_file filename ]
end

(** {1 Output and Display} *)

module Display = struct
  (** Pretty print verification results to stdout.

      Displays a summary of the analysis results including:
      - Validity (whether assertions were satisfied)
      - Undefined behavior detection
      - Number of possible executions
      - Number of events in the event structure

      @param lwt_ctx The Mordor context containing analysis results
      @return Unit wrapped in Lwt *)
  let print_results (lwt_ctx : mordor_ctx Lwt.t) =
    let* ctx = lwt_ctx in
      Printf.printf "=== Verification Results ===\n";
      ( match ctx.structure with
      | None -> ()
      | Some structure -> Printf.printf "Events: %d\n" (USet.size structure.e)
      );
      ( match ctx.is_episodic with
      | None -> ()
      | Some is_episodic ->
          Printf.printf "Episodic: %s\n"
            (Hashtbl.fold
               (fun loop_index res acc ->
                 acc ^ Printf.sprintf "%d: %b; " loop_index res
               )
               is_episodic ""
            )
      );
      ( match ctx.episodicity_results with
      | None -> ()
      | Some results ->
          Printf.printf "Episodicity Results: %s\n"
            (show_loop_episodicity_result_summary results)
      );
      ( match ctx.executions with
      | None -> ()
      | Some executions ->
          Printf.printf "Executions: %d\n" (USet.size executions)
      );
      ( match ctx.valid with
      | None -> ()
      | Some valid -> Printf.printf "Valid: %b\n" valid
      );
      ( match ctx.assertion_instances with
      | None -> ()
      | Some instances ->
          Printf.printf "Assertion Instances: %s\n"
            (String.concat "\n\t" (List.map show_assertion_instance instances))
      );
      ( match ctx.undefined_behaviour with
      | None -> ()
      | Some ub -> Printf.printf "Undefined Behavior: %b\n" ub
      );
      Printf.printf "===========================\n";
      flush stdout;
      Lwt.return_unit

  (** Print a formatted header for a test run.

      @param name The program name
      @param program The program source code *)
  let print_program_header name program =
    Printf.printf "Running program %s.\n" name;
    Printf.printf "===================\n";
    Printf.printf "\n=== Running: %s ===\n" name;
    Printf.printf "Program:\n%s\n\n" program;
    flush stdout
end

(** {1 Verification Pipelines} *)

module Pipeline = struct
  (** Create a basic context with program loaded.

      Initializes a Mordor context with the program and configuration settings.
      The context is ready to be passed through the analysis pipeline.

      @param name Program name for identification
      @param program Program source code
      @param config Complete configuration
      @return A fresh Mordor context *)
  let make_program_context name program config =
    let context =
      make_context config.Config.options ?output_mode:config.output_mode
        ?output_file:config.output_file ?step_counter:config.step_counter ()
    in
      context.litmus_name <- name;
      context.litmus <- Some program;
      context

  (** {2 Run Command} *)

  (** Run full verification pipeline on a single program.

      Executes the complete pipeline:
      + Parse litmus test to IR
      + Interpret to generate event structure
      + Calculate dependencies
      + Check assertions

      @param name Program name
      @param program Program source
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let run_single name program config =
    Logs.info (fun m ->
        m "Running single program %s with options\n%s" name
          (show_options config.Config.options)
    );
    Display.print_program_header name program;
    let context = make_program_context name program config in
      Lwt.return context
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Elaborations.step_generate_justifications
      |> Executions.step_calculate_dependencies
      |> Assertion.step_check_assertions
      |> Display.print_results

  (** Run verification on multiple programs sequentially.

      @param tests List of (name, program) pairs
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let run_tests tests config =
    Logs.info (fun m -> m "Running %d tests." (List.length tests));
    let* () =
      Lwt_list.iter_s (fun (name, prog) -> run_single name prog config) tests
    in
      flush stdout;
      Lwt.return_unit

  (** {2 Parse Command} *)

  (** Parse a single program without further analysis.

      Only executes the parsing stage, converting the litmus test to IR. Useful
      for debugging parser issues or inspecting the IR.

      @param name Program name
      @param program Program source
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let parse_single name program config =
    let context = make_program_context name program config in
      Lwt.return context |> Parse.step_parse_litmus |> Display.print_results

  (** Parse multiple programs.

      @param tests List of (name, program) pairs
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let parse_tests tests config =
    let* () =
      Lwt_list.iter_s (fun (name, prog) -> parse_single name prog config) tests
    in
      Lwt.return_unit

  (** {2 Interpret Command} *)

  (** Interpret a single program to generate event structure.

      Executes parsing and interpretation stages. The interpretation stage uses
      the configured loop semantics (symbolic, bounded, etc.) to generate a
      symbolic event structure.

      @param name Program name
      @param program Program source
      @param config Configuration (including loop semantics and step counter)
      @return Unit wrapped in Lwt *)
  let interpret_single name program config =
    Logs.info (fun m -> m "Interpreting program %s." name);
    let context = make_program_context name program config in
      Lwt.return context
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Display.print_results

  (** Interpret multiple programs.

      @param tests List of (name, program) pairs
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let interpret_tests tests config =
    let* () =
      Lwt_list.iter_s
        (fun (name, prog) -> interpret_single name prog config)
        tests
    in
      flush stdout;
      Lwt.return_unit

  (** {2 Episodicity Command} *)

  (** Check episodicity of loops in a single program.

      Analyzes whether loops satisfy the four episodicity conditions:
      + Register access restriction
      + Memory read sources
      + Branch condition symbols
      + Inter-iteration ordering

      This command requires symbolic loop semantics and will generate both
      symbolic and bounded (3-iteration) event structures for analysis.

      @param name Program name
      @param program Program source
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let check_episodicity name program config =
    let context = make_program_context name program config in
      Lwt.return context
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Episodicity.step_test_episodicity
      |> Display.print_results

  (** {2 Visual ES Command} *)

  (** Visualize event structure for a single program.

      Generates a visual representation of the symbolic event structure. Output
      format is controlled by the config (DOT, JSON, or HTML).

      The visualization includes:
      - Events with their types and labels
      - Program order relations
      - Dependency relations
      - Read-from relations

      @param name Program name
      @param program Program source
      @param config Configuration (including output_mode)
      @return Unit wrapped in Lwt *)
  let visualize_es name program config =
    let context = make_program_context name program config in
      Lwt.return context
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Elaborations.step_generate_justifications
      |> Executions.step_calculate_dependencies
      |> Eventstructureviz.step_visualize_event_structure
      |> Display.print_results

  (** {2 Futures Command} *)

  (** Compute futures for a single program.

      Calculates possible future states in the symbolic execution. Futures
      represent states that could be reached through valid execution paths.

      @param name Program name
      @param program Program source
      @param config Configuration
      @return Unit wrapped in Lwt *)
  let compute_futures name program config =
    let context = make_program_context name program config in
      Lwt.return context
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Elaborations.step_generate_justifications
      |> Executions.step_calculate_dependencies
      |> Futures.step_futures
      |> Futures.print_futures
      |> Display.print_results

  (** Execute a command on the loaded tests.

      Dispatches to the appropriate pipeline function based on the command.
      Commands that require a single input file will fail if multiple files are
      provided.

      @param config The complete configuration
      @param tests List of (name, program) pairs to analyze
      @return Unit wrapped in Lwt
      @raise Failure if a single-file command is given multiple files *)
  let execute config tests =
    match config.Config.command with
    | Config.Run -> run_tests tests config
    | Config.Parse -> parse_tests tests config
    | Config.Interpret -> interpret_tests tests config
    | Config.Episodicity ->
        if List.length tests <> 1 then
          failwith
            "Episodicity command requires exactly one input program (use \
             --single)";
        let name, program = List.hd tests in
          check_episodicity name program config
    | Config.VisualEs ->
        if List.length tests <> 1 then
          failwith
            "VisualEs command requires exactly one input program (use --single)";
        let name, program = List.hd tests in
          visualize_es name program config
    | Config.Futures ->
        if List.length tests <> 1 then
          failwith
            "Futures command requires exactly one input program (use --single)";
        let name, program = List.hd tests in
          compute_futures name program config
    | Config.Dependencies ->
        Printf.printf "TODO: Dependencies command not implemented yet\n";
        Lwt.return_unit
end

(** {1 Command Line Interface} *)

module CLI = struct
  (** Mutable state for command-line parsing.

      This state accumulates options as they're parsed from the command line,
      then is converted to an immutable {!Config.t} once parsing is complete. *)
  type parse_state = {
    mutable command : Config.command option;  (** Command to execute *)
    mutable run_mode : Config.run_mode;  (** Which programs to run *)
    mutable output_mode : output_mode option;  (** Output format *)
    mutable output_file : string option;  (** Output file path *)
    mutable step_counter : int option;  (** Loop iteration bound *)
    mutable loop_semantics : loop_semantics;  (** Loop interpretation mode *)
    mutable recursive : bool;  (** Recursive directory scanning *)
    mutable litmus_dir : string;  (** Directory for litmus tests *)
    mutable log_level : Logs.level option;  (** Logging level *)
  }

  (** Create initial parse state with defaults. *)
  let initial_state () =
    {
      command = None;
      run_mode = Config.Samples;
      output_mode = None;
      output_file = None;
      step_counter = Some 2;
      loop_semantics = FiniteStepCounter;
      recursive = false;
      litmus_dir = "litmus_tests";
      log_level = None;
    }

  (** Convert parse state to immutable configuration.

      Applies the loop semantics from parse state to the options.

      @param state The mutable parse state
      @return An immutable configuration
      @raise Failure if no command was specified *)
  let to_config state =
    match state.command with
    | None -> failwith "No command specified"
    | Some command ->
        let run_mode =
          match state.run_mode with
          | Config.Samples -> Config.Samples
          | Config.AllLitmusTests _ ->
              Config.AllLitmusTests
                { dir = state.litmus_dir; recursive = state.recursive }
          | Config.Single _ as s -> s
        in
        let options =
          {
            default_options with
            loop_semantics = state.loop_semantics;
            step_counter = Option.value state.step_counter ~default:2;
          }
        in
          {
            Config.command;
            run_mode;
            output_mode = state.output_mode;
            output_file = state.output_file;
            step_counter = state.step_counter;
            options;
          }

  (** Usage message displayed on error or with --help. *)
  let usage_msg =
    "Usage: main COMMAND [OPTIONS]\n\n\
     Commands:\n\
    \  run           Run full verification pipeline\n\
    \  parse         Parse litmus test to IR only\n\
    \  interpret     Parse and interpret to generate event structure\n\
    \  episodicity   Check loop episodicity (requires --single)\n\
    \  visual-es     Visualize event structure (requires --single)\n\
    \  futures       Compute futures (requires --single)\n\
    \  dependencies  Compute dependencies (not yet implemented)\n\n\
     Options:"

  (** Command-line argument specifications.

      Defines all available flags and options with their handlers. Each option
      updates the mutable parse state.

      @param state The mutable parse state to update
      @return List of Arg specifications *)
  let specs state =
    [
      (* Input sources *)
      ( "--all-litmus-tests",
        Arg.String
          (fun dir ->
            state.run_mode <- Config.AllLitmusTests { dir; recursive = false };
            state.litmus_dir <- dir
          ),
        " Process all .lit files in the specified directory (default: \
         litmus_tests)"
      );
      ( "-r",
        Arg.Unit (fun () -> state.recursive <- true),
        " Scan directories recursively (use with --all-litmus-tests)"
      );
      ( "--single",
        Arg.String (fun filename -> state.run_mode <- Config.Single filename),
        " Process a single .lit file"
      );
      ( "--samples",
        Arg.Unit (fun () -> state.run_mode <- Config.Samples),
        " Run built-in sample programs (default)"
      );
      (* Output configuration *)
      ( "--output-mode",
        Arg.String (fun s -> state.output_mode <- Some (parse_output_mode s)),
        " Output format: json/dot/html (visual-es) or isa/json (parse/futures)"
      );
      ( "--output-file",
        Arg.String (fun s -> state.output_file <- Some s),
        " Output file path (default: stdout)"
      );
      (* Logging levels *)
      ( "--debug",
        Arg.Unit (fun () -> state.log_level <- Some Logs.Debug),
        " Set log level to Debug (most verbose)"
      );
      ( "--info",
        Arg.Unit (fun () -> state.log_level <- Some Logs.Info),
        " Set log level to Info"
      );
      ( "--warning",
        Arg.Unit (fun () -> state.log_level <- Some Logs.Warning),
        " Set log level to Warning"
      );
      ( "--error",
        Arg.Unit (fun () -> state.log_level <- Some Logs.Error),
        " Set log level to Error (least verbose)"
      );
      (* Loop semantics - these are mutually exclusive *)
      ( "--symbolic-loop-semantics",
        Arg.Unit (fun () -> state.loop_semantics <- Symbolic),
        " Use symbolic loop representation (for episodicity checking)"
      );
      ( "--step-counter",
        Arg.Int
          (fun n ->
            state.loop_semantics <- FiniteStepCounter;
            state.step_counter <- Some n
          ),
        " Global loop iteration bound (default: 2)"
      );
      ( "--step-counter-per-loop",
        Arg.Int
          (fun n ->
            state.loop_semantics <- StepCounterPerLoop;
            state.step_counter <- Some n
          ),
        " Per-loop iteration bound (default: 2)"
      );
    ]

  (** Parse command name from anonymous argument.

      The first non-flag argument is interpreted as the command name. Only one
      command can be specified.

      @param state The parse state to update
      @param arg The command name string
      @raise Failure if command is unknown or multiple commands specified *)
  let parse_command state arg =
    match state.command with
    | Some _ -> failwith "Multiple commands specified"
    | None -> (
        match String.lowercase_ascii arg with
        | "run" -> state.command <- Some Config.Run
        | "parse" -> state.command <- Some Config.Parse
        | "interpret" -> state.command <- Some Config.Interpret
        | "episodicity" -> state.command <- Some Config.Episodicity
        | "visual-es" -> state.command <- Some Config.VisualEs
        | "futures" -> state.command <- Some Config.Futures
        | "dependencies" -> state.command <- Some Config.Dependencies
        | cmd ->
            Printf.eprintf "Error: Unknown command '%s'\n" cmd;
            Printf.eprintf
              "Valid commands: run, parse, interpret, episodicity, visual-es, \
               futures, dependencies\n";
            exit 1
      )

  (** Parse command-line arguments and return configuration.

      Uses the Arg module to parse command-line flags and options, then converts
      the mutable parse state to an immutable config.

      @return A tuple of (configuration, log_level option)
      @raise Exit on parse errors or invalid arguments *)
  let parse_args () =
    let state = initial_state () in
    let anon_fun arg = parse_command state arg in
      try
        Arg.parse (specs state) anon_fun usage_msg;
        (to_config state, state.log_level)
      with Failure msg ->
        Printf.eprintf "Error: %s\n\n" msg;
        Arg.usage (specs state) usage_msg;
        exit 1
end

(** {1 Logging Setup} *)

module Logging = struct
  (** Setup logging with timestamps and formatted headers.

      Configures the Logs library to output with timestamps in the format:
      [HH:MM:SS.mmm] LEVEL: message

      @param level Optional log level; defaults to Debug if not specified *)
  let setup ?(level = Logs.Debug) () =
    (* Custom header formatter with millisecond timestamps.

       @param ppf Format printer
       @param l Log level and optional header *)
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
      Logs.set_level (Some level)
end

(** {1 Main Entry Point} *)

(** Main function that orchestrates the entire program execution.

    Execution flow:
    + Parse command-line arguments into configuration
    + Setup logging with the specified log level
    + Print banner
    + Load test programs based on run mode
    + Execute the requested command
    + Display results

    @return Unit wrapped in Lwt *)
let main () =
  (* Parse command-line arguments *)
  let config, log_level = CLI.parse_args () in

  (* Setup logging with the specified level *)
  let level = Option.value log_level ~default:Logs.Debug in
    Logging.setup ~level ();

    Printf.printf "MoRDor - Symbolic Modular Relaxed Dependencies\n";
    flush stdout;

    (* Load test programs based on run mode *)
    let tests = FileIO.load_tests config.Config.run_mode in

    (* Execute the command *)
    Pipeline.execute config tests

(** Program entry point.

    Runs the main function in the Lwt runtime. All async operations are handled
    by Lwt's cooperative threading. *)
let () = Lwt_main.run (main ())
