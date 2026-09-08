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

module TestUSet = struct
  (** [filter_map] keeps what [f] answers [Some] for and drops the rest. *)
  let test_filter_map_keeps_and_drops () =
    let s = USet.of_list [ 1; 2; 3; 4; 5 ] in
    let result =
      USet.filter_map (fun x -> if x mod 2 = 0 then Some (x * 10) else None) s
    in
      check int "two evens survive" 2 (USet.size result);
      check bool "contains 20" true (USet.mem result 20);
      check bool "contains 40" true (USet.mem result 40);
      check bool "does not contain 10" false (USet.mem result 10);
      ()

  (** It is a set, so results that collide are one element. *)
  let test_filter_map_collapses_duplicates () =
    let s = USet.of_list [ 1; 2; 3 ] in
    let result = USet.filter_map (fun _ -> Some 0) s in
      check int "all three map to one" 1 (USet.size result);
      ()

  (** All [None] gives the empty set, and the input is not touched. *)
  let test_filter_map_drops_everything () =
    let s = USet.of_list [ 1; 2; 3 ] in
    let result = USet.filter_map (fun _ -> None) s in
      check int "nothing survives" 0 (USet.size result);
      check int "source is unchanged" 3 (USet.size s);
      ()

  let suite =
    [
      test_case "filter_map keeps and drops" `Quick
        test_filter_map_keeps_and_drops;
      test_case "filter_map collapses duplicates" `Quick
        test_filter_map_collapses_duplicates;
      test_case "filter_map drops everything" `Quick
        test_filter_map_drops_everything;
    ]
end

let suite = ("USet", TestURelation.suite @ TestUSet.suite)
