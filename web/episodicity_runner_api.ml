(** Episodicity Runner API - Server-side handlers for running episodicity
    analysis *)

open Lwt.Syntax

(* Configuration *)
let episodicity_dir = "programs/episodicity"
let step_counter = 2

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

(* Types mirroring test_integration_episodicity.ml *)
type condition_result = {
  condition_num : int;
  satisfied : bool;
  violation_count : int;
}

type episodicity_result = {
  loop_id : int;
  is_episodic : bool;
  conditions : condition_result list;
}

(* Parse episodicity results from CLI output.
   Logic mirrors parse_episodicity_output in test_integration_episodicity.ml. *)
let parse_episodicity_output output_lines =
  let results = ref [] in
  let current_loop_id = ref None in
  let current_is_episodic = ref false in
  let current_conditions = ref [] in

  let parse_episodic_line line =
    try
      let regexp = Str.regexp "Episodic: \\([0-9]+\\): \\(true\\|false\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
          let loop_id = int_of_string (Str.matched_group 1 line) in
          let is_episodic = Str.matched_group 2 line = "true" in
            Some (loop_id, is_episodic)
        with Not_found -> None
    with _ -> None
  in

  let parse_loop_id_line line =
    try
      let regexp = Str.regexp "loop_id = \\([0-9]+\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
            Some (int_of_string (Str.matched_group 1 line))
        with Not_found -> None
    with _ -> None
  in

  let parse_condition_num line =
    try
      let regexp = Str.regexp "condition\\([0-9]+\\) =" in
        try
          let _ = Str.search_forward regexp line 0 in
            Some (int_of_string (Str.matched_group 1 line))
        with Not_found -> None
    with _ -> None
  in

  let parse_satisfied_value line =
    try
      let regexp = Str.regexp "satisfied = \\(true\\|false\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
            Some (Str.matched_group 1 line = "true")
        with Not_found -> None
    with _ -> None
  in

  let parse_is_episodic_value line =
    try
      let regexp = Str.regexp "is_episodic = \\(true\\|false\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
            Some (Str.matched_group 1 line = "true")
        with Not_found -> None
    with _ -> None
  in

  let parse_violations_section line =
    try
      if Str.string_match (Str.regexp ".*violations =") line 0 then Some ()
      else None
    with _ -> None
  in

  let in_condition = ref None in
  let condition_satisfied = ref true in
  let has_violations = ref false in

  let finalize_current_condition () =
    match !in_condition with
    | Some cond_num ->
        let violation_count =
          if !has_violations && not !condition_satisfied then 1 else 0
        in
          current_conditions :=
            {
              condition_num = cond_num;
              satisfied = !condition_satisfied;
              violation_count;
            }
            :: !current_conditions;
          in_condition := None;
          condition_satisfied := true;
          has_violations := false
    | None -> ()
  in

  let finalize_current_loop () =
    match !current_loop_id with
    | Some loop_id ->
        let result =
          {
            loop_id;
            is_episodic = !current_is_episodic;
            conditions = List.rev !current_conditions;
          }
        in
          results := result :: !results;
          current_loop_id := None;
          current_is_episodic := false;
          current_conditions := [];
          in_condition := None;
          condition_satisfied := true;
          has_violations := false
    | None -> ()
  in

  let switch_loop new_id =
    match !current_loop_id with
    | Some current_id when current_id <> new_id ->
        finalize_current_condition ();
        finalize_current_loop ()
    | _ -> ()
  in

  let rec process_lines = function
    | [] ->
        finalize_current_condition ();
        finalize_current_loop ();
        List.rev !results
    | line :: rest -> (
        match parse_episodic_line line with
        | Some (loop_id, is_episodic) ->
            switch_loop loop_id;
            current_loop_id := Some loop_id;
            current_is_episodic := is_episodic;
            process_lines rest
        | None -> (
            match parse_loop_id_line line with
            | Some loop_id ->
                switch_loop loop_id;
                current_loop_id := Some loop_id;
                process_lines rest
            | None -> (
                match parse_condition_num line with
                | Some cond_num ->
                    finalize_current_condition ();
                    in_condition := Some cond_num;
                    condition_satisfied := true;
                    has_violations := false;
                    process_lines rest
                | None -> (
                    match parse_satisfied_value line with
                    | Some satisfied ->
                        condition_satisfied := satisfied;
                        process_lines rest
                    | None -> (
                        match parse_is_episodic_value line with
                        | Some is_episodic ->
                            current_is_episodic := is_episodic;
                            process_lines rest
                        | None -> (
                            match parse_violations_section line with
                            | Some () ->
                                has_violations := true;
                                process_lines rest
                            | None -> process_lines rest
                          )
                      )
                  )
              )
          )
      )
  in
    process_lines output_lines

(* Serialise a single condition_result to JSON *)
let condition_result_to_json (c : condition_result) =
  `Assoc
    [
      ("condition_num", `Int c.condition_num);
      ("satisfied", `Bool c.satisfied);
      ("violation_count", `Int c.violation_count);
    ]

(* Serialise a single episodicity_result to JSON *)
let episodicity_result_to_json (r : episodicity_result) =
  `Assoc
    [
      ("loop_id", `Int r.loop_id);
      ("is_episodic", `Bool r.is_episodic);
      ("conditions", `List (List.map condition_result_to_json r.conditions));
    ]

(* Execute the episodicity CLI command and capture output.
   Mirrors run_cli_episodicity in test_integration_episodicity.ml. *)
let run_cli_episodicity filepath =
  let cmd =
    Printf.sprintf
      "dune exec mordor -- episodicity --step-counter %d --single \"%s\" 2>&1"
      step_counter filepath
  in
  let ic = Unix.open_process_in cmd in
  let output = ref [] in
    ( try
        while true do
          output := input_line ic :: !output
        done
      with End_of_file -> ()
    );
    let exit_code = Unix.close_process_in ic in
    let status =
      match exit_code with
      | Unix.WEXITED code -> code
      | Unix.WSIGNALED _ -> -1
      | Unix.WSTOPPED _ -> -1
    in
      (status, List.rev !output)

(* API Handlers *)

(* GET /api/episodicity/list - List all available episodicity test files *)
let list_episodicity_handler _request =
  try
    let tests = read_litmus_files episodicity_dir in
    let json =
      `Assoc [ ("tests", `List (List.map (fun t -> `String t) tests)) ]
    in
      Dream.json (Yojson.Basic.to_string json)
  with exn ->
    let error = Printexc.to_string exn in
      Dream.json ~status:`Internal_Server_Error
        (Yojson.Basic.to_string (`Assoc [ ("error", `String error) ]))

(* POST /api/episodicity/run - Run episodicity analysis on a specific file.
   Request body: {"test": "path/to/file.lit"}
   Response:
     { "success": bool,
       "exit_code": int,
       "output": string,
       "loops_analyzed": int,
       "all_episodic": bool,
       "results": [ { "loop_id": int, "is_episodic": bool,
                      "conditions": [ { "condition_num": int,
                                        "satisfied": bool,
                                        "violation_count": int } ] } ] } *)
let run_episodicity_handler request =
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

      Printf.printf "Running episodicity analysis: %s\n%!" test_path;

      let exit_code, output = run_cli_episodicity test_path in
      let output_str = String.concat "\n" output in
      let results = parse_episodicity_output output in

      let all_episodic =
        results <> [] && List.for_all (fun r -> r.is_episodic) results
      in
      let success = exit_code = 0 && List.length results > 0 in

      let response =
        `Assoc
          [
            ("success", `Bool success);
            ("exit_code", `Int exit_code);
            ("output", `String output_str);
            ("loops_analyzed", `Int (List.length results));
            ("all_episodic", `Bool all_episodic);
            ("results", `List (List.map episodicity_result_to_json results));
          ]
      in

      Dream.json (Yojson.Basic.to_string response)
    with exn ->
      let error = Printexc.to_string exn in
        Printf.printf "Error running episodicity analysis: %s\n%!" error;
        Dream.json ~status:`Internal_Server_Error
          (Yojson.Basic.to_string
             (`Assoc
                [
                  ("success", `Bool false);
                  ("error", `String error);
                  ("output", `String error);
                ]
             )
          )

(* GET /api/episodicity/source?test=<path> - Get source of an episodicity test file *)
let get_episodicity_source_handler request =
  try
    let test_path = Dream.query request "test" |> Option.value ~default:"" in

    if test_path = "" then
      Dream.json ~status:`Bad_Request
        (Yojson.Basic.to_string
           (`Assoc [ ("error", `String "Missing 'test' parameter") ])
        )
    else
      let ic = open_in test_path in
      let source = ref [] in
        ( try
            while true do
              source := input_line ic :: !source
            done
          with End_of_file -> close_in ic
        );

        let source_str = String.concat "\n" (List.rev !source) in
        let response = `Assoc [ ("source", `String source_str) ] in

        Dream.json (Yojson.Basic.to_string response)
  with
  | Sys_error msg ->
      Dream.json ~status:`Not_Found
        (Yojson.Basic.to_string (`Assoc [ ("error", `String msg) ]))
  | exn ->
      let error = Printexc.to_string exn in
        Dream.json ~status:`Internal_Server_Error
          (Yojson.Basic.to_string (`Assoc [ ("error", `String error) ]))

(* Routes to add to main server *)
let routes =
  [
    Dream.get "/api/episodicity/list" list_episodicity_handler;
    Dream.post "/api/episodicity/run" run_episodicity_handler;
    Dream.get "/api/episodicity/source" get_episodicity_source_handler;
  ]
