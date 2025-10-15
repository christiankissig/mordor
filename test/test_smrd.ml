(* Main test runner *)

let () =
  Alcotest.run "SMRD Test Suite"
    [
      Test_types.suite;
      Test_expr.suite;
      Test_parse.suite;
      Test_interpret.suite;
      Test_solver.suite;
    ]
