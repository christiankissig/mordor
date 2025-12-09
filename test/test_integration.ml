open Uset

let () =
  Alcotest.run "Mordor Integration Test Suite"
    [ Test_integration_litmus_tests.suite ]
