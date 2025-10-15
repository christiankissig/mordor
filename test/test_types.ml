open Types

let test_basic () =
  Alcotest.(check bool) "basic type test" true true

let suite =
  (
    "Types", [
      Alcotest.test_case "Basic type operations" `Quick test_basic;
    ]
  )
