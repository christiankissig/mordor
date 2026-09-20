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

  let rel = USet.of_list

  (** Cycles of every length, and none. *)
  let test_acyclic_cases () =
    check bool "empty" true (URelation.acyclic (rel []));
    check bool "a self-loop" false (URelation.acyclic (rel [ (1, 1) ]));
    check bool "two events" false (URelation.acyclic (rel [ (1, 2); (2, 1) ]));
    check bool "three events" false
      (URelation.acyclic (rel [ (1, 2); (2, 3); (3, 1) ]));
    check bool "a chain" true
      (URelation.acyclic (rel [ (1, 2); (2, 3); (3, 4) ]));
    check bool "a diamond" true
      (URelation.acyclic (rel [ (1, 2); (1, 3); (2, 4); (3, 4) ]));
    check bool "a cycle away from the first event" false
      (URelation.acyclic (rel [ (1, 2); (3, 4); (4, 5); (5, 3) ]))

  (** [acyclic] is what it says it is: no event reaches itself in the transitive
      closure. Random relations over up to 8 events, seeded. *)
  let test_acyclic_is_closure_irreflexive () =
    let rng = Random.State.make [| 17 |] in
      for case = 1 to 500 do
        let n = 1 + Random.State.int rng 8 in
        let edges =
          List.init
            (Random.State.int rng (2 * n))
            (fun _ -> (Random.State.int rng n, Random.State.int rng n))
        in
        let r = rel edges in
        let by_closure =
          USet.for_all (fun (a, b) -> a <> b) (URelation.transitive_closure r)
        in
          check bool
            (Printf.sprintf "case %d" case)
            by_closure (URelation.acyclic r)
      done

  (** [transitive_closure] is the least transitive relation containing the
      relation: what adding [(a, d)] for every [(a, b)], [(b, d)] until nothing
      changes gives. Random relations over up to 8 events, cycles and self-loops
      included, seeded. *)
  let test_transitive_closure_is_fixpoint () =
    let rng = Random.State.make [| 23 |] in
      for case = 1 to 500 do
        let n = 1 + Random.State.int rng 8 in
        let edges =
          List.init
            (Random.State.int rng (2 * n))
            (fun _ -> (Random.State.int rng n, Random.State.int rng n))
        in
        let rec fixpoint pairs =
          let added =
            List.concat_map
              (fun (a, b) ->
                List.filter_map
                  (fun (c, d) ->
                    if b = c && not (List.mem (a, d) pairs) then Some (a, d)
                    else None
                  )
                  pairs
              )
              pairs
            |> List.sort_uniq compare
          in
            if added = [] then pairs else fixpoint (pairs @ added)
        in
          check
            (list (pair int int))
            (Printf.sprintf "case %d" case)
            (fixpoint (List.sort_uniq compare edges) |> List.sort_uniq compare)
            (USet.values (URelation.transitive_closure (rel edges))
            |> List.sort compare
            )
      done

  let suite =
    [
      test_case "transitive_closure is the fixpoint" `Quick
        test_transitive_closure_is_fixpoint;
      test_case "acyclic: cases" `Quick test_acyclic_cases;
      test_case "acyclic is the closure irreflexive" `Quick
        test_acyclic_is_closure_irreflexive;
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

  (** A set is an element by its members: two sets built differently, with the
      same members, are one element of a set of sets. *)
  let test_sets_of_sets_by_content () =
    let a = USet.of_list [ 1; 2; 3 ] in
    let b = USet.create () in
      List.iter (fun x -> ignore (USet.add b x)) [ 3; 2; 1; 4 ];
      ignore (USet.remove b 4);
      let ss = USet.of_list [ a; b; USet.of_list [ 5 ] ] in
        check int "two distinct sets" 2 (USet.size ss);
        check bool "the other is found by content" true
          (USet.mem ss (USet.of_list [ 2; 3; 1 ]))

  (** So is a set inside a record, as an execution's relations are. *)
  let test_records_holding_sets_by_content () =
    let r1 = (1, USet.of_list [ (1, 2); (2, 3) ]) in
    let r2 = (1, USet.of_list [ (2, 3); (1, 2) ]) in
      check bool "value_equality" true (USet.value_equality r1 r2);
      check int "one element" 1 (USet.size (USet.of_list [ r1; r2 ]))

  (** Reading a set writes nothing to it: domains iterating one set at once
      leave it as it was, and it can be added to afterwards. Base's hash sets,
      which this used to be, could be left refusing every [add]. *)
  let test_concurrent_iteration_leaves_set_usable () =
    let s = USet.of_list (List.init 10_000 Fun.id) in
    let domains =
      List.init 4 (fun _ ->
          Domain.spawn (fun () ->
              let n = ref 0 in
                for _ = 1 to 50 do
                  USet.iter (fun _ -> incr n) s
                done;
                !n
          )
      )
    in
      List.iter
        (fun d ->
          check int "each domain saw every member" 500_000 (Domain.join d)
        )
        domains;
      ignore (USet.add s (-1));
      check int "added to afterwards" 10_001 (USet.size s)

  (** Reversing the iteration order changes the order and nothing else. *)
  let test_reversed_iteration () =
    let s = USet.of_list (List.init 100 Fun.id) in
    let forward = USet.values s in
      USet.reversed_iteration := true;
      let reversed =
        Fun.protect
          ~finally:(fun () -> USet.reversed_iteration := false)
          (fun () -> USet.values s)
      in
        check (list int) "same members"
          (List.sort compare forward)
          (List.sort compare reversed);
        check bool "another order" true (forward <> reversed)

  let suite =
    [
      test_case "sets of sets by content" `Quick test_sets_of_sets_by_content;
      test_case "records holding sets by content" `Quick
        test_records_holding_sets_by_content;
      test_case "concurrent iteration leaves a set usable" `Quick
        test_concurrent_iteration_leaves_set_usable;
      test_case "reversed iteration" `Quick test_reversed_iteration;
      test_case "filter_map keeps and drops" `Quick
        test_filter_map_keeps_and_drops;
      test_case "filter_map collapses duplicates" `Quick
        test_filter_map_collapses_duplicates;
      test_case "filter_map drops everything" `Quick
        test_filter_map_drops_everything;
    ]
end

let suite = ("USet", TestURelation.suite @ TestUSet.suite)
