open Uset

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

(** The full integration suite. The litmus suite runs the CLI on every file
    under [litmus-tests/] and takes minutes, so [dune build @runtest] runs
    [test_integration.exe --quick], which runs only [quick_suites] and names
    what it skips; [dune build @integration] runs all of it (test/dune). *)
let suites () =
  [
    Test_integration_litmus_tests.suite_strict;
    Test_integration_episodicity.suite;
    Test_integration_parallel.suite;
  ]

let quick_suites = [ fst Test_integration_parallel.suite ]

let () =
  setup_logs ();
  (* Initialize episodicity test directories before running *)
  Test_integration_episodicity.initialize ();
  let quick = Array.mem "--quick" Sys.argv in
  let argv =
    Array.of_list (List.filter (( <> ) "--quick") (Array.to_list Sys.argv))
  in
  let run, skipped =
    if quick then
      List.partition (fun (name, _) -> List.mem name quick_suites) (suites ())
    else (suites (), [])
  in
    List.iter
      (fun (name, cases) ->
        Printf.printf "SKIPPED (--quick): %s, %d cases\n" name
          (List.length cases)
      )
      skipped;
    if skipped <> [] then
      print_endline
        "Run them with: dune build @integration (or dune exec \
         test/test_integration.exe)";
    Alcotest.run ~argv "Mordor Integration Test Suite" run
