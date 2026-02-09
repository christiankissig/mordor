(** Integration tests for episodicity analysis on litmus test files *)

open Lwt.Syntax

(* Configuration *)
let episodicity_dir = "programs/episodicity"
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

(* Parse episodicity results from CLI output *)
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

let parse_episodicity_output output_lines =
  let results = ref [] in
  let current_loop_id = ref None in
  let current_is_episodic = ref false in
  let current_conditions = ref [] in

  let parse_episodic_line line =
    (* Match: "Episodic: 1: false;" or "Episodic: 0: true;" *)
    try
      let regexp = Str.regexp "Episodic: \\([0-9]+\\): \\(true\\|false\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
          let loop_id = int_of_string (Str.matched_group 1 line) in
          let is_episodic = Str.matched_group 2 line = "true" in
            Printf.printf "[DEBUG] Parsed episodic line: Loop %d = %b\n" loop_id
              is_episodic;
            Some (loop_id, is_episodic)
        with Not_found -> None
    with _ -> None
  in

  let parse_loop_id_line line =
    (* Match: "loop_id = 1;" *)
    try
      let regexp = Str.regexp "loop_id = \\([0-9]+\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
          let loop_id = int_of_string (Str.matched_group 1 line) in
            Printf.printf "[DEBUG] Parsed loop_id: %d\n" loop_id;
            Some loop_id
        with Not_found -> None
    with _ -> None
  in

  let parse_condition_satisfied line =
    (* Match: "condition1 =" followed by "{ Context.satisfied = false;" *)
    (* This is a multi-line structure, we'll just track condition numbers *)
    try
      let regexp = Str.regexp "condition\\([0-9]+\\) =" in
        try
          let _ = Str.search_forward regexp line 0 in
          let cond_num = int_of_string (Str.matched_group 1 line) in
            Printf.printf "[DEBUG] Found condition%d declaration\n" cond_num;
            Some cond_num
        with Not_found -> None
    with _ -> None
  in

  let parse_satisfied_value line =
    (* Match: "satisfied = false;" or "satisfied = true;" *)
    try
      let regexp = Str.regexp "satisfied = \\(true\\|false\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
          let satisfied = Str.matched_group 1 line = "true" in
            Printf.printf "[DEBUG] Parsed satisfied: %b\n" satisfied;
            Some satisfied
        with Not_found -> None
    with _ -> None
  in

  let parse_is_episodic_value line =
    (* Match: "is_episodic = true" or "is_episodic = false" *)
    try
      let regexp = Str.regexp "is_episodic = \\(true\\|false\\)" in
        try
          let _ = Str.search_forward regexp line 0 in
          let is_episodic = Str.matched_group 1 line = "true" in
            Printf.printf "[DEBUG] Parsed is_episodic: %b\n" is_episodic;
            Some is_episodic
        with Not_found -> None
    with _ -> None
  in

  let parse_violations_count line =
    (* Match: "violations =" and count the violations in subsequent lines *)
    (* For now, just detect if there are violations *)
    try
      let has_violations =
        Str.string_match (Str.regexp ".*violations =") line 0
      in
        if has_violations then (
          Printf.printf "[DEBUG] Found violations section\n";
          Some ()
        )
        else None
    with _ -> None
  in

  (* State machine for parsing *)
  let in_condition = ref None in
  let condition_satisfied = ref true in
  let has_violations = ref false in

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

  let rec process_lines = function
    | [] ->
        finalize_current_condition ();
        finalize_current_loop ();
        let final_results = List.rev !results in
          Printf.printf "[DEBUG] Total results parsed: %d\n"
            (List.length final_results);
          List.iter
            (fun r ->
              Printf.printf "[DEBUG]   Loop %d: episodic=%b, conditions=%d\n"
                r.loop_id r.is_episodic (List.length r.conditions);
              List.iter
                (fun c ->
                  Printf.printf
                    "[DEBUG]     Condition %d: satisfied=%b, violations=%d\n"
                    c.condition_num c.satisfied c.violation_count
                )
                r.conditions
            )
            final_results;
          final_results
    | line :: rest -> (
        (* Try parsing episodic line (simple format) *)
        match parse_episodic_line line with
        | Some (loop_id, is_episodic) ->
            (* Only finalize if we have a different loop_id *)
            ( match !current_loop_id with
            | Some current_id when current_id <> loop_id ->
                finalize_current_condition ();
                finalize_current_loop ()
            | None -> ()
            | _ -> ()
            );
            current_loop_id := Some loop_id;
            current_is_episodic := is_episodic;
            process_lines rest
        | None -> (
            (* Try parsing loop_id line (structured format) *)
            match parse_loop_id_line line with
            | Some loop_id ->
                (* Only finalize if we have a different loop_id *)
                ( match !current_loop_id with
                | Some current_id when current_id <> loop_id ->
                    finalize_current_condition ();
                    finalize_current_loop ()
                | None -> ()
                | _ -> ()
                );
                current_loop_id := Some loop_id;
                process_lines rest
            | None -> (
                (* Try parsing condition declaration *)
                match parse_condition_satisfied line with
                | Some cond_num ->
                    finalize_current_condition ();
                    in_condition := Some cond_num;
                    (* Reset state for new condition *)
                    condition_satisfied := true;
                    has_violations := false;
                    process_lines rest
                | None -> (
                    (* Try parsing satisfied value *)
                    match parse_satisfied_value line with
                    | Some satisfied ->
                        condition_satisfied := satisfied;
                        process_lines rest
                    | None -> (
                        (* Try parsing is_episodic value *)
                        match parse_is_episodic_value line with
                        | Some is_episodic ->
                            current_is_episodic := is_episodic;
                            process_lines rest
                        | None -> (
                            (* Try parsing violations *)
                            match parse_violations_count line with
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

(* Execute CLI command and capture result *)
let run_cli_episodicity filepath =
  let cmd =
    Printf.sprintf "%s episodicity --step-counter 2 --single \"%s\""
      cli_executable filepath
  in
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

(* Test specification type *)
type episodicity_test_spec = {
  filepath : string;
  expected_episodic : bool option; (* None means don't check *)
  expected_failing_conditions : int list;
      (* List of condition numbers expected to fail *)
  description : string;
}

(* Predefined test specifications *)
let test_specifications =
  [
    {
      filepath =
        "programs/episodicity/register_violations/episodic_register_cond_fail.lit";
      expected_episodic = Some false;
      expected_failing_conditions = [ 1 ];
      description = "Register condition failure - ri read before write";
    };
    {
      filepath =
        "programs/episodicity/write_violations/episodic_write_cond_fail.lit";
      expected_episodic = Some false;
      expected_failing_conditions = [ 2 ];
      description = "Write condition failure - modifying write after read";
    };
    {
      filepath =
        "programs/episodicity/branch_violations/episodic_branch_cond_fail.lit";
      expected_episodic = Some false;
      expected_failing_conditions = [ 3 ];
      description = "Branch condition failure - constrains pre-loop symbol";
    };
    (* TODO event ordering condition
    {
      filepath = "programs/episodicity/ordering_violations/episodic_events_cond_fail.lit";
      expected_episodic = Some false;
      expected_failing_conditions = [ 4 ];
      description = "Event ordering failure - iterations not properly ordered";
    };
       *)
    {
      filepath = "programs/episodicity/episodic_branch_nested_fail.lit";
      expected_episodic = Some false;
      expected_failing_conditions = [ 3 ];
      description =
        "Branch condition failure - nested loop constrains pre-loop symbol";
    };
    {
      filepath = "programs/episodicity/episodic_register_multi_fail.lit";
      expected_episodic = Some false;
      expected_failing_conditions = [ 1; 2 ];
      description =
        "Multiple condition failures - register and write conditions fail";
    };
    {
      filepath = "programs/episodicity/valid/episodic_valid_read.lit";
      expected_episodic = Some true;
      expected_failing_conditions = [];
      description =
        "Valid episodic loop - should be episodic with no failing conditions";
    };
    {
      filepath = "programs/episodicity/valid/episodic_valid_write_only.lit";
      expected_episodic = Some true;
      expected_failing_conditions = [];
      description =
        "Valid episodic loop with only writes - should be episodic with no \
         failing conditions";
    };
  ]

(* Test that checks episodicity analysis with expected results *)
let test_episodicity_spec spec () =
  let exit_code, output = run_cli_episodicity spec.filepath in
  let output_str = String.concat "\n" output in

  Printf.printf "\n[DEBUG] Parsing output for %s\n"
    (Filename.basename spec.filepath);
  Printf.printf "[DEBUG] First 10 lines of output:\n";
  List.iteri
    (fun i line -> if i < 10 then Printf.printf "[DEBUG]   %d: %s\n" i line)
    output;
  Printf.printf "[DEBUG] Lines containing 'Loop':\n";
  List.iter
    (fun line ->
      if Str.string_match (Str.regexp ".*Loop.*") line 0 then
        Printf.printf "[DEBUG]   > %s\n" line
    )
    output;

  (* Check that CLI exited successfully *)
  Alcotest.(check int)
    (Printf.sprintf "CLI should exit successfully for %s" spec.filepath)
    0 exit_code;

  (* Check that we got some output *)
  Alcotest.(check bool)
    (Printf.sprintf "Output should contain results for %s" spec.filepath)
    true
    (String.length output_str > 0);

  (* Parse the episodicity results *)
  let results = parse_episodicity_output output in

  (* Debug: print parsing results *)
  if List.length results = 0 then
    Printf.printf "\n⚠ Warning: No results parsed from output for %s\n"
      (Filename.basename spec.filepath);

  (* Check that we got at least one loop analyzed *)
  Alcotest.(check bool)
    (Printf.sprintf "Should have analyzed at least one loop in %s" spec.filepath)
    true
    (List.length results > 0);

  (* Check episodicity status if expected *)
  ( match (spec.expected_episodic, results) with
  | Some expected, _ :: _ ->
      (* Use the last result (most complete from structured output) *)
      let result = List.hd (List.rev results) in
        Alcotest.(check bool)
          (Printf.sprintf "Loop should %sbe episodic in %s"
             (if expected then "" else "not ")
             (Filename.basename spec.filepath)
          )
          expected result.is_episodic;

        (* Report result *)
        if result.is_episodic then
          Printf.printf "✓ %s: Loop %d is EPISODIC\n"
            (Filename.basename spec.filepath)
            result.loop_id
        else
          Printf.printf "✗ %s: Loop %d is NOT EPISODIC (expected)\n"
            (Filename.basename spec.filepath)
            result.loop_id
  | None, _ -> ()
  | Some _, [] ->
      Alcotest.fail
        (Printf.sprintf "No loop analysis results found for %s" spec.filepath)
  );

  (* Check failing conditions if specified *)
  if List.length spec.expected_failing_conditions > 0 then
    match results with
    | _ :: _ ->
        (* Use the last result (most complete from structured output) *)
        let result = List.hd (List.rev results) in
        let failing_conditions =
          List.filter (fun c -> not c.satisfied) result.conditions
          |> List.map (fun c -> c.condition_num)
        in
        let expected_set = List.sort compare spec.expected_failing_conditions in
        let actual_set = List.sort compare failing_conditions in
          Alcotest.(check (list int))
            (Printf.sprintf "Should have expected failing conditions in %s"
               (Filename.basename spec.filepath)
            )
            expected_set actual_set;

          (* Report violations *)
          List.iter
            (fun c ->
              if not c.satisfied then
                Printf.printf "  Condition %d: %d violation(s)\n"
                  c.condition_num c.violation_count
            )
            result.conditions
    | [] ->
        Alcotest.fail
          (Printf.sprintf "No loop analysis results found for %s" spec.filepath)

(* Test that only checks for successful execution without specific expectations *)
let test_episodicity_file filepath () =
  let exit_code, output = run_cli_episodicity filepath in
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

  (* Parse and report the episodicity results *)
  let results = parse_episodicity_output output in

  (* Report results *)
  List.iter
    (fun result ->
      if result.is_episodic then
        Printf.printf "✓ %s: Loop %d is EPISODIC\n"
          (Filename.basename filepath)
          result.loop_id
      else (
        Printf.printf "✗ %s: Loop %d is NOT EPISODIC\n"
          (Filename.basename filepath)
          result.loop_id;

        (* Report which conditions failed *)
        List.iter
          (fun c ->
            if not c.satisfied then
              Printf.printf "  Condition %d failed: %d violation(s)\n"
                c.condition_num c.violation_count
          )
          result.conditions
      )
    )
    results

(* Generate test cases from specifications *)
let spec_test_cases =
  List.map
    (fun spec ->
      let test_name = Printf.sprintf "%s - %s" spec.filepath spec.description in
        Alcotest.test_case test_name `Quick (test_episodicity_spec spec)
    )
    test_specifications

(* Generate test cases from litmus files in directory *)
let litmus_test_cases =
  let files = read_litmus_files episodicity_dir in
  (* Filter out files already covered by specifications *)
  let spec_files =
    List.map (fun spec -> spec.filepath) test_specifications
    |> List.sort compare
  in
  let additional_files =
    List.filter (fun filepath -> not (List.mem filepath spec_files)) files
    |> List.sort compare
  in
    List.map
      (fun filepath ->
        let test_name = filepath in
          Alcotest.test_case test_name `Quick (test_episodicity_file filepath)
      )
      additional_files

(* Test suites *)
let suite_spec =
  ("Integration Tests - Episodicity (With Expectations)", spec_test_cases)

let suite_discovery =
  ("Integration Tests - Episodicity (Discovery)", litmus_test_cases)

(* Combined suite *)
let suite =
  ("Integration Tests - Episodicity", spec_test_cases @ litmus_test_cases)

(* Utility function to create episodicity directory structure if it doesn't exist *)
let ensure_episodicity_dir () =
  try
    if not (Sys.file_exists episodicity_dir) then
      Unix.mkdir episodicity_dir 0o755;

    (* Create subdirectories for organizing tests *)
    let subdirs =
      [
        "valid";
        (* Episodic loops *)
        "register_violations";
        (* Condition 1 failures *)
        "write_violations";
        (* Condition 2 failures *)
        "branch_violations";
        (* Condition 3 failures *)
        "ordering_violations";
        (* Condition 4 failures *)
      ]
    in
      List.iter
        (fun subdir ->
          let path = Filename.concat episodicity_dir subdir in
            if not (Sys.file_exists path) then Unix.mkdir path 0o755
        )
        subdirs
  with Unix.Unix_error (err, fn, param) ->
    Printf.eprintf "Warning: Could not create episodicity directory: %s %s %s\n"
      (Unix.error_message err) fn param

(* Initialize directory structure on module load *)
let () = ensure_episodicity_dir ()
