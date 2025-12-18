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

let () =
  setup_logs ();
  Alcotest.run "Mordor Integration Test Suite"
    [ Test_integration_litmus_tests.suite_strict ]
