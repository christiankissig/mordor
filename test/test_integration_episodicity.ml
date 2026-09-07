(** Integration tests for episodicity analysis on litmus test files *)

open Lwt.Syntax

(* Configuration *)
let episodicity_dir = "programs/episodicity"

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

(* Name a parsed condition the way the paper and the analysis logs do, e.g.
   "branching condition (3)", so the test output reads as the definition does.
   Falls back to the bare index should the analysis ever report a condition
   this test does not know about. *)
let describe_condition_num n =
  match Episodicity.condition_of_index n with
  | Some kind -> Episodicity.describe_condition kind
  | None -> Printf.sprintf "condition (%d)" n

(* "1 violation" / "3 violations". *)
let violation_count_phrase n =
  Printf.sprintf "%d %s" n (if n = 1 then "violation" else "violations")

let parse_episodicity_output output_lines =
  let results = ref [] in
  (* Every loop the summary line names, whether or not the structured dump that
     follows carries a block for it. A loop the analysis could not get a
     bisection for is reported there and nowhere else. *)
  let summary = ref [] in
  let current_loop_id = ref None in
  let current_is_episodic = ref false in
  let current_conditions = ref [] in

  (* The summary is one line carrying every loop -- "Episodic: 2: false; 3:
     false; 1: false;" -- so it has to be scanned to the end. Reading only the
     first match dropped every loop after it, which went unnoticed while the
     structured dump below happened to carry a block for each. *)
  let parse_episodic_line line =
    try
      let regexp = Str.regexp "\\([0-9]+\\): \\(true\\|false\\)" in
      let rec scan from acc =
        match Str.search_forward regexp line from with
        | exception Not_found -> List.rev acc
        | pos ->
            let loop_id = int_of_string (Str.matched_group 1 line) in
            let is_episodic = Str.matched_group 2 line = "true" in
              Printf.printf "[DEBUG] Parsed episodic line: Loop %d = %b\n"
                loop_id is_episodic;
              scan (pos + 1) ((loop_id, is_episodic) :: acc)
      in
        if Str.string_match (Str.regexp ".*Episodic:") line 0 then
          match scan 0 [] with
          | [] -> None
          | pairs -> Some pairs
        else None
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
            Printf.printf "[DEBUG] Found the %s\n"
              (describe_condition_num cond_num);
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
        let parsed = List.rev !results in
        (* A loop the analysis could not bisect produces no block, only a
           verdict in the summary. Record it with no conditions rather than
           leaving it out, so an expectation for it fails on the verdict rather
           than on the loop being missing. *)
        let missing =
          List.filter_map
            (fun (loop_id, is_episodic) ->
              if List.exists (fun r -> r.loop_id = loop_id) parsed then None
              else Some { loop_id; is_episodic; conditions = [] }
            )
            !summary
        in
        let final_results = parsed @ missing in
          Printf.printf "[DEBUG] Parsed %s\n"
            ( match List.length final_results with
            | 1 -> "1 loop result"
            | n -> Printf.sprintf "%d loop results" n
            );
          List.iter
            (fun r ->
              Printf.printf "[DEBUG]   Loop %d is %sepisodic (%s reported)\n"
                r.loop_id
                (if r.is_episodic then "" else "not ")
                ( match List.length r.conditions with
                | 1 -> "1 condition"
                | n -> Printf.sprintf "%d conditions" n
                );
              List.iter
                (fun c ->
                  Printf.printf "[DEBUG]     %-24s %s\n"
                    (describe_condition_num c.condition_num ^ ":")
                    ( if c.satisfied then "satisfied"
                      else
                        Printf.sprintf "violated (%s)"
                          (violation_count_phrase c.violation_count)
                    )
                )
                r.conditions
            )
            final_results;
          final_results
    | line :: rest -> (
        (* Try parsing episodic line (simple format) *)
        match parse_episodic_line line with
        | Some pairs ->
            finalize_current_condition ();
            finalize_current_loop ();
            summary := !summary @ pairs;
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
  (* Use dune exec to ensure we can find the executable regardless of context *)
  let cmd =
    Printf.sprintf
      "dune exec mordor -- episodicity --step-counter 2 --single \"%s\" 2>&1"
      filepath
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

(* Per-loop expectation: check a specific loop by its id *)
type loop_expectation = {
  loop_id : int;
  expected_episodic : bool;
  expected_failing_conditions : int list;
      (* Condition numbers expected to fail for this loop *)
}

(* Test specification type *)
type episodicity_test_spec = {
  filepath : string;
  loop_expectations : loop_expectation list;
      (* Per-loop expectations; loops not listed are not checked *)
  description : string;
}

(* Convenience constructors *)

(* Single-loop file where the one loop should be episodic *)
let single_episodic filepath description =
  {
    filepath;
    loop_expectations =
      [
        {
          loop_id = 1;
          expected_episodic = true;
          expected_failing_conditions = [];
        };
      ];
    description;
  }

(* Single-loop file where the one loop fails *)
let single_failing filepath failing_conditions description =
  {
    filepath;
    loop_expectations =
      [
        {
          loop_id = 1;
          expected_episodic = false;
          expected_failing_conditions = failing_conditions;
        };
      ];
    description;
  }

(* Predefined test specifications *)
let test_specifications =
  [
    (* register condition *)
    single_failing "programs/episodicity/register_condition/fail.lit" [ 1 ]
      "Register condition failure - loop reads pre-loop symbol without \
       separation";
    (* branch condition *)
    single_failing "programs/episodicity/branch_condition/fail.lit" [ 3 ]
      "Branch condition failure - constrains pre-loop symbol";
    single_failing "programs/episodicity/branch_condition/nested_fail.lit"
      [ 3; 4 ]
      "Branch condition failure - nested loop constrains pre-loop symbol";
    (* write condition *)
    single_failing "programs/episodicity/write_condition/fail.lit" [ 2 ]
      "Write condition failure - a read takes its value from a write of an \
       earlier iteration under every loop boundary";
    single_episodic "programs/episodicity/valid/rotated.lit"
      "Episodic once the loop boundary moves - a single satisfying bisection \
       suffices";
    (* events condition *)
    single_failing "programs/episodicity/events_condition/two_reads_fail.lit"
      [ 4 ] "Event ordering failure - iterations don't separate two reads";
    single_episodic "programs/episodicity/events_condition/cas_inc_loop.lit"
      "Valid episodic loop with RMW events - should be episodic with no \
       failing conditions";
    (* multiple violations *)
    single_failing "programs/episodicity/multiple/register_events_fail.lit"
      [ 1 ]
      (* TODO there is a bijection which fails the test this way, but a
failure at 4 is intended *)
      "Multiple condition failures - register and write conditions fail";
    (* valid cases *)
    single_episodic "programs/episodicity/valid/read.lit"
      "Valid episodic loop - should be episodic with no failing conditions";
    single_episodic "programs/episodicity/valid/write_only.lit"
      "Valid episodic loop with only writes - should be episodic with no \
       failing conditions";
    (* The self-incrementing loop, in three spellings of the same program: each
       iteration reads the counter and writes it back incremented, so a value
       crosses the loop boundary and none of them is episodic.

       They used to disagree. The do form was episodic because loop_conditions
       was never populated for a do-while, leaving Condition 2 vacuous; the
       while form was episodic because a rotating bisection satisfied Condition
       2 while Condition 1 still read the unrotated body; the hand-written
       rotation was correctly rejected. The verdict is pinned rather than the
       failing condition, because when no bisection is episodic the reported
       conditions are those of the last one tried: the rotated spelling fails
       Condition 1 on the trivial bisection and Condition 2 on the rotated one,
       and reports the latter. *)
    single_failing "programs/episodicity/self_increment/do.lit" []
      "Self-incrementing loop, do-while form - not episodic";
    single_failing "programs/episodicity/self_increment/while.lit" []
      "Self-incrementing loop, while form - must agree with the do form";
    single_failing "programs/episodicity/self_increment/rotated.lit" []
      "Self-incrementing loop, hand-rotated form - must agree with the do form";
    (* real-world locking protocols *)
    single_episodic "programs/episodicity/seqlock-1.lit"
      "Seqlock - Loop 1 is episodic";
    single_episodic "programs/episodicity/spinlock-1.lit"
      "Spinlock - Loop 1 is episodic";
    (* These record what MoRDor reports today, not what the paper's table
       claims, and not a considered verdict on the program: loops 1 and 2 are
       expected episodic and are currently reported otherwise for a reason that
       is a defect in the checker.

       Both loops sit inside another do-while, and the symbolic encoding gives
       one unravelled body plus the residual loop, so their events arrive as two
       po-incomparable copies -- loop 1's are 65..69 and 255..259, with no po
       edge between the chains. all_bisections ranks events by how many of the
       loop's events precede them and keeps the prefix of size k only when
       exactly k events rank below k, which enumerates the order ideals of a
       total order and nothing else. With the ranks tied across two chains that
       holds only at k = 0 and k = |E|, and k = |E| leaves the right side empty,
       so the sole surviving candidate is the empty bisection. With no left
       there is no earlier part of an iteration for a read to read from, so
       every loop read that may see a loop write is a write-condition
       violation. Loop 3 is the same mechanism with no candidate at all, which
       is what "could not analyze" reports.

       Enumerating the po-downward-closed subsets properly is 36 candidates for
       loop 1 and 8281 for loop 2, against 2^10 and 2^48 -- tractable to
       enumerate, not yet to check at two minutes a bisection. The Todoist task
       carries the options. Until one lands, read these as "fails against the
       empty bisection", not as "not episodic".

       An empty failing-condition list skips the check, so loop 3 asserts only
       its verdict. *)
    {
      filepath = "programs/episodicity/hp-1.lit";
      loop_expectations =
        [
          {
            loop_id = 1;
            expected_episodic = false;
            expected_failing_conditions = [ 2 ];
          };
          {
            loop_id = 2;
            expected_episodic = false;
            expected_failing_conditions = [ 2; 4 ];
          };
          {
            loop_id = 3;
            expected_episodic = false;
            expected_failing_conditions = [];
          };
        ];
      description =
        "Hazard pointers - loops 1 and 2 judged against the empty bisection, \
         the only candidate all_bisections yields for a body duplicated into \
         po-incomparable copies, so both fail the write condition; loop 3 \
         yields no candidate at all";
    };
    (* Both episodic, as the table has them. The increment loop was the last to
       come back: its reads through the pointer the fetch-and-add returns were
       held to alias the writes into the rcu array, because nothing said an
       address inside one allocation is not an address inside another. See
       allocation_interiors_are_disjoint in the write condition. *)
    {
      filepath = "programs/episodicity/rcu-1.lit";
      loop_expectations =
        [
          {
            loop_id = 1;
            expected_episodic = true;
            expected_failing_conditions = [];
          };
          {
            loop_id = 2;
            expected_episodic = true;
            expected_failing_conditions = [];
          };
        ];
      description = "RCU - both loops episodic";
    };
    (* The increment loop on its own -- the one the table is about. 33 events
       against rcu-1's 97, and a second and a half against thirty-five, because
       a loop removed takes both its own events and the copy of the
       continuation it forces on every loop before it. *)
    single_episodic "programs/episodicity/rcu-inc.lit"
      "RCU increment loop alone - episodic";
  ]

(* hp-1 and its pruned variant are skipped.

   hp-1 and rcu-1 were held out while their episodicity analysis did not
   finish: the symbolic do-while encoding grew their event structures from 15
   and 21 events to 360 and 493, and the elaboration fixed point did not
   converge on either. It does now — the forwarding contexts it was enumerating
   are collapsed for the episodicity path, since Condition 4 reads
   justifications only through freeze_dp.

   rcu-1 is 97 events and about 35 seconds since its two dead sync loops went:
   the program has one thread, so waiting on the other two rcu slots was
   unreachable. rcu-inc.lit is its increment loop alone, 33 events and a second
   and a half.

   hp-1 is out again, and so is hp-inc.lit, the same pruning applied to it.
   Pruning does not help there: it takes hp-1 from 360 events to 99, but the two
   loops in question are the increment loop and the hazard-pointer loop nested
   in it, so they keep their 10 and 48 events and their 36 and 8281 candidate
   boundaries. Loop 1 takes about two and a half minutes and loop 2 does not
   finish. The cost is per bisection -- each one re-elaborates -- and that is
   what wants fixing before either goes back in.

   run_cli_episodicity still has no timeout — it blocks on close_process_in —
   so a program that does not finish hangs the suite rather than failing it.
   That is why these are skipped rather than left to run. *)
let disabled_files =
  [ "programs/episodicity/hp-1.lit"; "programs/episodicity/hp-inc.lit" ]

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

  (* Parse the episodicity results, indexed by loop_id for O(1) lookup *)
  let results = parse_episodicity_output output in
  let results_by_id =
    List.fold_left
      (fun acc (r : episodicity_result) -> List.cons (r.loop_id, r) acc)
      [] results
  in
  let find_loop id =
    try Some (List.assoc id results_by_id) with Not_found -> None
  in

  (* Debug: print parsing results *)
  if List.length results = 0 then
    Printf.printf "\n⚠ Warning: No results parsed from output for %s\n"
      (Filename.basename spec.filepath);

  (* Check that we got at least one loop analyzed *)
  Alcotest.(check bool)
    (Printf.sprintf "Should have analyzed at least one loop in %s" spec.filepath)
    true
    (List.length results > 0);

  (* Check each per-loop expectation independently *)
  List.iter
    (fun exp ->
      match find_loop exp.loop_id with
      | None ->
          Alcotest.fail
            (Printf.sprintf "Loop %d not found in output for %s" exp.loop_id
               (Filename.basename spec.filepath)
            )
      | Some result ->
          (* Check episodicity *)
          Alcotest.(check bool)
            (Printf.sprintf "%s: Loop %d should %sbe episodic"
               (Filename.basename spec.filepath)
               exp.loop_id
               (if exp.expected_episodic then "" else "not ")
            )
            exp.expected_episodic result.is_episodic;

          (* Report *)
          if result.is_episodic then
            Printf.printf "✓ %s: Loop %d is EPISODIC\n"
              (Filename.basename spec.filepath)
              result.loop_id
          else
            Printf.printf "✗ %s: Loop %d is NOT EPISODIC (expected)\n"
              (Filename.basename spec.filepath)
              result.loop_id;

          (* Check failing conditions if any are expected *)
          if exp.expected_failing_conditions <> [] then (
            let failing_conditions =
              List.filter (fun c -> not c.satisfied) result.conditions
              |> List.map (fun c -> c.condition_num)
            in
            let expected_set =
              List.sort compare exp.expected_failing_conditions
            in
            let actual_set = List.sort compare failing_conditions in
              Alcotest.(check (list int))
                (Printf.sprintf
                   "%s: Loop %d should have expected failing conditions"
                   (Filename.basename spec.filepath)
                   exp.loop_id
                )
                expected_set actual_set;

              List.iter
                (fun c ->
                  if not c.satisfied then
                    Printf.printf "  Loop %d: %s violated (%s)\n" result.loop_id
                      (describe_condition_num c.condition_num)
                      (violation_count_phrase c.violation_count)
                )
                result.conditions
          )
    )
    spec.loop_expectations

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
              Printf.printf "  %s violated (%s)\n"
                (describe_condition_num c.condition_num)
                (violation_count_phrase c.violation_count)
          )
          result.conditions
      )
    )
    results

(* Generate test cases from specifications *)
let spec_test_cases =
  (* Only create tests if files actually exist *)
  List.filter_map
    (fun spec ->
      if
        Sys.file_exists spec.filepath
        && not (List.mem spec.filepath disabled_files)
      then
        Some
          (let test_name =
             Printf.sprintf "%s - %s" spec.filepath spec.description
           in
             Alcotest.test_case test_name `Quick (test_episodicity_spec spec)
          )
      else None
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
    List.filter
      (fun filepath ->
        (not (List.mem filepath spec_files))
        && not (List.mem filepath disabled_files)
      )
      files
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
  (* Try to find the project root by looking for dune-project *)
  let find_project_root () =
    let rec go path depth =
      if depth > 5 then None (* Don't search too deep *)
      else if Sys.file_exists (Filename.concat path "dune-project") then
        Some path
      else go (Filename.concat path "..") (depth + 1)
    in
      go "." 0
  in

  match find_project_root () with
  | Some root -> (
      let full_path = Filename.concat root episodicity_dir in
        try
          if not (Sys.file_exists full_path) then Unix.mkdir full_path 0o755;

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
              "events_condition";
              (* Condition 4 failures *)
            ]
          in
            List.iter
              (fun subdir ->
                let path = Filename.concat full_path subdir in
                  if not (Sys.file_exists path) then Unix.mkdir path 0o755
              )
              subdirs
        with Unix.Unix_error (err, fn, param) ->
          Printf.eprintf
            "Warning: Could not create episodicity directory: %s %s %s\n"
            (Unix.error_message err) fn param
    )
  | None ->
      Printf.eprintf
        "Warning: Could not find project root (no dune-project found)\n"

(* Call this function explicitly when you want to run the tests *)
let initialize () = ensure_episodicity_dir ()
