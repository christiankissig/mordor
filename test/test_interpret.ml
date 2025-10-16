open Interpret

let test_interpret_basic () =
  Alcotest.(check bool) "basic interpretation" true true

let suite =
  ( "Interpreter",
    [ Alcotest.test_case "Basic interpretation" `Quick test_interpret_basic ]
  )
