(** Integration tests for the domain-parallel path.

    Nothing exercised [--threads] above 1. Every unit test builds its context
    with [~num_threads:1], the web server passes none, and the litmus
    integration tests shell out to the CLI without the flag. So the whole
    domain-parallel path -- the pool, the chunked dispatch, and every cache a
    worker touches -- ran only when somebody ran it by hand.

    What these tests pin down is the property that matters and that a race would
    break: a parallel run must agree with the sequential one, exactly. Analysis
    output is a set of executions and a verdict, and none of it is supposed to
    depend on how the work was divided. A cache mutated without its lock, or an
    entry read while another domain rewrites it, shows up here as output that
    differs from [--threads 1] rather than as a crash.

    They compare stdout, not stderr, because stderr carries timestamped log
    lines that differ between any two runs. *)

(** The project root, found by walking up from wherever the test is run:
    [dune test] runs it in [_build/default/test] and [dune exec] from the
    project root, and the CLI and the programs have to be found from both. *)
let project_root =
  let rec up dir fuel =
    if fuel = 0 then None
    else if Sys.file_exists (Filename.concat dir "dune-project") then Some dir
    else
      let parent = Filename.dirname dir in
        if parent = dir then None else up parent (fuel - 1)
  in
    up (Sys.getcwd ()) 8

(** [run_cli root args] runs the CLI with [args] and returns its exit code and
    stdout. stderr is discarded: it is the log stream, and it is timestamped. *)
let run_cli root args =
  let exe = Filename.concat root "_build/default/cli/main.exe" in
  let cmd =
    String.concat " " (Filename.quote exe :: List.map Filename.quote args)
    ^ " 2>/dev/null"
  in
  let ic = Unix.open_process_in cmd in
  let lines = ref [] in
  let () =
    try
      while true do
        lines := input_line ic :: !lines
      done
    with End_of_file -> ()
  in
  let status =
    match Unix.close_process_in ic with
    | Unix.WEXITED code -> code
    | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1
  in
    (status, String.concat "\n" (List.rev !lines))

(** Programs picked to be quick and to still reach the parallel stages: each has
    justifications to elaborate and executions to freeze and filter. *)
let programs = [ "lb.lit"; "lb-uaf.lit"; "spinlock-1.lit"; "uaf-bug.lit" ]

(** [test_agrees_with_sequential name] checks that [name] analysed on a domain
    pool gives the same answer as analysed on one domain.

    [--threads 4] is capped to what the machine recommends, so on a single-core
    runner this compares a sequential run against a sequential run. That is a
    weaker test rather than a flaky one. *)
let test_agrees_with_sequential name () =
  match project_root with
  | None ->
      Alcotest.fail "could not find dune-project above the working directory"
  | Some root ->
      let program = Filename.concat root (Filename.concat "programs" name) in
      let run threads =
        run_cli root [ "run"; "--single"; program; "--threads"; threads ]
      in
      let sequential_code, sequential_out = run "1" in
      let parallel_code, parallel_out = run "4" in
        Alcotest.(check int)
          (name ^ ": sequential run exits cleanly")
          0 sequential_code;
        Alcotest.(check int)
          (name ^ ": parallel run exits cleanly")
          0 parallel_code;
        Alcotest.(check string)
          (name ^ ": parallel output matches sequential")
          sequential_out parallel_out

(** [test_rejects_bad_thread_count] checks that a thread count below one is
    refused by the argument parser rather than quietly running sequentially. *)
let test_rejects_bad_thread_count () =
  match project_root with
  | None ->
      Alcotest.fail "could not find dune-project above the working directory"
  | Some root ->
      let program =
        Filename.concat root (Filename.concat "programs" "lb.lit")
      in
      let code, _ =
        run_cli root [ "run"; "--single"; program; "--threads"; "0" ]
      in
        Alcotest.(check bool) "--threads 0 is refused" true (code <> 0)

let suite =
  ( "Integration Tests - Parallel",
    Alcotest.test_case "--threads 0 is refused" `Quick
      test_rejects_bad_thread_count
    :: List.map
         (fun name ->
           Alcotest.test_case
             (name ^ ": parallel agrees with sequential")
             `Slow
             (test_agrees_with_sequential name)
         )
         programs
  )
