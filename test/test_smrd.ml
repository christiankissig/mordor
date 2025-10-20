(* Main test runner *)

let () =
  Alcotest.run "Mordor Test Suite"
    [
      Test_types.suite;
      Test_expr.suite;
      Test_parse.suite;
      Test_interpret.suite;
      Test_solver.suite;
      Test_forwardingcontext.suite;
      Test_elaborations.suite;
    ]
