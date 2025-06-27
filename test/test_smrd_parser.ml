open Mordor.Smrd_parser

let test_parse_success input expected_contains =
  try
    let parsed = parse input in
    let result = string_of_program parsed in
    Printf.printf "✓ PASS: %s\n" input;
    Printf.printf "  Result: %s\n" result;
    if expected_contains <> "" && not (String.contains_from result 0 expected_contains.[0]) then
      Printf.printf "  Warning: Expected to contain '%s'\n" expected_contains;
    true
  with
  | ParseError msg ->
      Printf.printf "✗ FAIL: %s\n" input;
      Printf.printf "  Parse error: %s\n" msg;
      false

let test_parse_failure input =
  try
    let _ = parse input in
    Printf.printf "✗ FAIL: %s (expected to fail but succeeded)\n" input;
    false
  with
  | ParseError _ ->
      Printf.printf "✓ PASS: %s (correctly failed)\n" input;
      true

let test_basic_parsing () =
  Printf.printf "\n=== Basic Parsing Tests ===\n";
  let test_cases = [
    "skip";
    "x := 5";
    "x := y + z * 2";
    "if (x = 5) { skip } else { y := 1 }";
    "if (x < y) { x := x + 1 }";
    "while (x < 10) { x := x + 1 }";
    "x := *y + 3";
    "fence_o";
  ] in
  
  let results = List.map (fun input -> test_parse_success input "") test_cases in
  let passed = List.fold_left (fun acc result -> if result then acc + 1 else acc) 0 results in
  let total = List.length results in
  
  Printf.printf "\nBasic tests: %d/%d passed\n" passed total;
  passed = total

let test_unicode_expressions () =
  Printf.printf "\n=== Unicode Expression Tests ===\n";
  let test_cases = [
    "if (x = y ∧ z < 5) { skip }";
    "if (¬(x = y)) { skip }";
    "if (x < y ∨ z > 10) { skip }";
  ] in
  
  let results = List.map (fun input -> test_parse_success input "") test_cases in
  let passed = List.fold_left (fun acc result -> if result then acc + 1 else acc) 0 results in
  let total = List.length results in
  
  Printf.printf "\nUnicode tests: %d/%d passed\n" passed total;
  passed = total

let test_error_handling () =
  Printf.printf "\n=== Error Handling Tests ===\n";
  let invalid_cases = [
    "if x { skip }";  (* missing parentheses *)
    "x := ";          (* incomplete assignment *)
    "{ skip";         (* unmatched brace *)
    "skip skip";      (* missing operator *)
  ] in
  
  let results = List.map test_parse_failure invalid_cases in
  let passed = List.fold_left (fun acc result -> if result then acc + 1 else acc) 0 results in
  let total = List.length results in
  
  Printf.printf "\nError tests: %d/%d passed\n" passed total;
  passed = total

let test_complex_programs () =
  Printf.printf "\n=== Complex Program Tests ===\n";
  let complex_cases = [
    "skip; x := 5; while (x > 0) { x := x - 1 }";
    "if (x = 0) { y := 1 } else { y := 2 }; z := y + 3";
    "x := malloc(10); *x := 42; free(x)";
  ] in
  
  let results = List.map (fun input -> test_parse_success input "") complex_cases in
  let passed = List.fold_left (fun acc result -> if result then acc + 1 else acc) 0 results in
  let total = List.length results in
  
  Printf.printf "\nComplex tests: %d/%d passed\n" passed total;
  passed = total

let run_all_tests () =
  Printf.printf "Running SMRD Parser Tests\n";
  Printf.printf "==========================\n";
  
  let basic_ok = test_basic_parsing () in
  let unicode_ok = test_unicode_expressions () in
  let error_ok = test_error_handling () in
  let complex_ok = test_complex_programs () in
  
  let all_passed = basic_ok && unicode_ok && error_ok && complex_ok in
  
  Printf.printf "\n=== Test Summary ===\n";
  Printf.printf "Basic parsing: %s\n" (if basic_ok then "PASS" else "FAIL");
  Printf.printf "Unicode expressions: %s\n" (if unicode_ok then "PASS" else "FAIL");
  Printf.printf "Error handling: %s\n" (if error_ok then "PASS" else "FAIL");
  Printf.printf "Complex programs: %s\n" (if complex_ok then "PASS" else "FAIL");
  Printf.printf "\nOverall: %s\n" (if all_passed then "ALL TESTS PASSED" else "SOME TESTS FAILED");
  
  all_passed

(* You can call this from your test file or use it directly *)
let () =
  let success = run_all_tests () in
  exit (if success then 0 else 1)
