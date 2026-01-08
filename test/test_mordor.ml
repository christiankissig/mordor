open Uset

let () =
  Alcotest.run "Mordor Test Suite"
    [
      Test_algorithms.suite;
      Test_types.suite;
      Test_expr.suite;
      Test_solver.suite;
      Test_events.suite;
      Test_coherence.suite;
      Test_elaborations.suite;
      Test_executions.suite;
      Test_forwardingcontext.suite;
      Test_interpret.suite;
      Test_parse.suite;
      Test_symbolic_mrd.suite;
      Test_properties_mrd.suite;
      Test_advanced_mrd.suite;
      Test_histories_futures.suite;
      Test_model_and_tuple_features.suite;
      Test_uset.suite;
      Test_episodicity.suite;
    ]
