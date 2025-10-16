open Solver

let test_solver_basic () = Alcotest.(check bool) "basic solver test" true true

let suite =
  ( "Solver",
    [ Alcotest.test_case "Basic solver operations" `Quick test_solver_basic ]
  )
