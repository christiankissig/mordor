open Alcotest
open Uset

module TestURelation = struct
  (** Test URelation.compose with empty list *)
  let test_semicolon_empty () =
    let result = URelation.compose [] in
      check int "empty composition" 0 (USet.size result);
      ()

  (** Test URelation.compose with single relation *)
  let test_semicolon_single () =
    let rel = USet.of_list [ (1, 2); (2, 3) ] in
    let result = URelation.compose [ rel ] in
      check int "single relation size" 2 (USet.size result);
      check bool "contains (1,2)" true (USet.mem result (1, 2));
      check bool "contains (2,3)" true (USet.mem result (2, 3));
      ()

  (** Test URelation.compose composition *)
  let test_semicolon_compose () =
    let r1 = USet.of_list [ (1, 2); (3, 4) ] in
    let r2 = USet.of_list [ (2, 5); (4, 6) ] in
    let result = URelation.compose [ r1; r2 ] in
      check bool "contains (1,5)" true (USet.mem result (1, 5));
      check bool "contains (3,6)" true (USet.mem result (3, 6));
      check bool "not contains (1,2)" false (USet.mem result (1, 2));
      ()

  (** Test URelation.compose with three relations *)
  let test_semicolon_triple () =
    let r1 = USet.of_list [ (1, 2) ] in
    let r2 = USet.of_list [ (2, 3) ] in
    let r3 = USet.of_list [ (3, 4) ] in
    let result = URelation.compose [ r1; r2; r3 ] in
      check bool "contains (1,4)" true (USet.mem result (1, 4));
      check int "result size" 1 (USet.size result);
      ()

  let suite =
    [
      test_case "compose with empty list" `Quick test_semicolon_empty;
      test_case "compose with single relation" `Quick test_semicolon_single;
      test_case "compose composition" `Quick test_semicolon_compose;
      test_case "compose with three relations" `Quick test_semicolon_triple;
    ]
end

let suite = ("USet", TestURelation.suite)
