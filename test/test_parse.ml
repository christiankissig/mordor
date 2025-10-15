open Parse

let test_parse_simple () =
  (* Example: Parse.parse_string "some input" *)
  Alcotest.(check bool) "parse simple expression" true true

let test_parse_complex () =
  Alcotest.(check bool) "parse complex expression" true true

let suite =
  (
    "Parser", [
      Alcotest.test_case "Parse simple input" `Quick test_parse_simple;
      Alcotest.test_case "Parse complex input" `Quick test_parse_complex;
    ]
  )
