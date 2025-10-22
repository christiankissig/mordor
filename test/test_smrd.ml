(* Main test runner *)

let () =
  Alcotest.run "Mordor Test Suite"
    [
      Test_coherence.suite;
      Test_elaborations.suite;
      Test_events.suite;
      Test_executions.suite;
      Test_expr.suite;
      Test_forwardingcontext.suite;
      Test_interpret.suite;
      Test_parse.suite;
      Test_solver.suite;
      Test_types.suite;
    ]
