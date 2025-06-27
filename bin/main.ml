open Mordor.Smrd_parser

type command = 
  | Parse
  | Dependencies  
  | Futures

let command_of_string = function
  | "parse" -> Some Parse
  | "dependencies" -> Some Dependencies
  | "futures" -> Some Futures
  | _ -> None

let usage_msg = "mordor COMMAND -f source.smrd"

let print_usage () =
  Printf.eprintf "Usage: %s\n" usage_msg;
  Printf.eprintf "Commands:\n";
  Printf.eprintf "  parse         Parse the SMRD source file\n";
  Printf.eprintf "  dependencies  Analyze dependencies (not implemented)\n";
  Printf.eprintf "  futures       Analyze futures (not implemented)\n";
  Printf.eprintf "Options:\n";
  Printf.eprintf "  -f FILE       Specify source file\n";
  exit 1

let read_file filename =
  try
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    content
  with
  | Sys_error msg ->
      Printf.eprintf "Error reading file '%s': %s\n" filename msg;
      exit 1

let execute_parse filename =
  let content = read_file filename in
  Printf.printf "Parsing file: %s\n\n" filename;
  try
    let parsed = parse content in
    Printf.printf "Parse successful!\n";
    Printf.printf "Result: %s\n" (string_of_program parsed)
  with
  | ParseError msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      exit 1

let execute_dependencies filename =
  Printf.eprintf "Error: 'dependencies' command not implemented yet\n";
  Printf.eprintf "File: %s\n" filename;
  exit 1

let execute_futures filename =
  Printf.eprintf "Error: 'futures' command not implemented yet\n";
  Printf.eprintf "File: %s\n" filename;
  exit 1

let execute_command command filename =
  match command with
  | Parse -> execute_parse filename
  | Dependencies -> execute_dependencies filename
  | Futures -> execute_futures filename

let parse_args () =
  let command_ref = ref None in
  let filename_ref = ref None in
  let expecting_filename = ref false in
  
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  
  let rec process_args = function
    | [] -> ()
    | "-f" :: filename :: rest ->
        filename_ref := Some filename;
        expecting_filename := false;
        process_args rest
    | "-f" :: [] ->
        Printf.eprintf "Error: -f option requires a filename\n";
        print_usage ()
    | arg :: rest when !command_ref = None ->
        (match command_of_string arg with
         | Some cmd -> 
             command_ref := Some cmd;
             process_args rest
         | None ->
             Printf.eprintf "Error: Unknown command '%s'\n" arg;
             print_usage ())
    | arg :: _ ->
        Printf.eprintf "Error: Unexpected argument '%s'\n" arg;
        print_usage ()
  in
  
  process_args args;
  
  match (!command_ref, !filename_ref) with
  | (Some command, Some filename) -> (command, filename)
  | (None, _) ->
      Printf.eprintf "Error: No command specified\n";
      print_usage ()
  | (Some _, None) ->
      Printf.eprintf "Error: No source file specified (use -f option)\n";
      print_usage ()

let () =
  if Array.length Sys.argv < 2 then (
    print_usage ()
  ) else (
    let (command, filename) = parse_args () in
    execute_command command filename
  )
