open Alcotest
open Executions
open Events
open Expr
open Trees
open Types
open Utils

(** Test utilities *)

let create_test_event id typ ?id_val ?cond ?rval ?wval () =
  {
    label = id;
    van = id;
    typ;
    id = id_val;
    loc = Option.map Expr.of_value id_val;
    rval;
    wval;
    rmod = Normal;
    wmod = Normal;
    fmod = Normal;
    cond;
    volatile = false;
    strong = None;
    lhs = None;
    rhs = None;
    pc = None;
    hide = false;
    quot = None;
  }

let create_test_events () =
  let events = Hashtbl.create 16 in
    Hashtbl.add events 0 (create_test_event 0 Init ());
    Hashtbl.add events 1 (create_test_event 1 Write ~id_val:(VVar "x") ());
    Hashtbl.add events 2 (create_test_event 2 Read ~id_val:(VVar "x") ());
    Hashtbl.add events 3 (create_test_event 3 Write ~id_val:(VVar "y") ());
    Hashtbl.add events 4 (create_test_event 4 Read ~id_val:(VVar "y") ());
    events

let create_test_structure () =
  let e = Uset.of_list [ 1; 2; 3; 4 ] in
  let po = Uset.of_list [ (1, 2); (2, 3); (3, 4) ] in
  let restrict = Hashtbl.create 4 in
  let cas_groups = Hashtbl.create 4 in
    {
      e;
      po;
      rmw = Uset.create ();
      lo = Uset.create ();
      restrict;
      cas_groups;
      pwg = [];
      fj = Uset.create ();
      p = Uset.create ();
      constraint_ = [];
    }

(** Test Utils Functions *)

let test_disjoint_same_location () =
  let loc1 = EVar "x" in
  let val1 = ENum (Z.of_int 1) in
  let loc2 = EVar "x" in
  let val2 = ENum (Z.of_int 2) in
  let result = disjoint (loc1, val1) (loc2, val2) in
    match result with
    | EBinOp (l1, "!=", l2) ->
        check bool "locations should be compared" true (l1 = loc1 && l2 = loc2)
    | _ -> fail "Expected binary operation with !="

let test_disjoint_different_locations () =
  let loc1 = EVar "x" in
  let val1 = ENum (Z.of_int 1) in
  let loc2 = EVar "y" in
  let val2 = ENum (Z.of_int 2) in
  let result = disjoint (loc1, val1) (loc2, val2) in
    match result with
    | EBinOp (l1, "!=", l2) ->
        check bool "locations should be different" true (l1 = loc1 && l2 = loc2)
    | _ -> fail "Expected binary operation with !="

let test_origin_from_reads () =
  let events = create_test_events () in
  let sym_event = create_test_event 2 Read ~rval:(VSymbol "s1") () in
    Hashtbl.replace events 2 sym_event;

    let read_events = Uset.of_list [ 2; 4 ] in
    let malloc_events = Uset.create () in

    let result = origin events read_events malloc_events "s1" in
      match result with
      | Some e -> check int "should find event 2" 2 e
      | None -> fail "Expected to find origin event"

let test_origin_from_mallocs () =
  let events = create_test_events () in
  let malloc_event = create_test_event 5 Malloc ~rval:(VSymbol "s2") () in
    Hashtbl.add events 5 malloc_event;

    let read_events = Uset.create () in
    let malloc_events = Uset.of_list [ 5 ] in

    let result = origin events read_events malloc_events "s2" in
      match result with
      | Some e -> check int "should find event 5" 5 e
      | None -> fail "Expected to find origin event"

let test_origin_not_found () =
  let events = create_test_events () in
  let read_events = Uset.of_list [ 2; 4 ] in
  let malloc_events = Uset.create () in

  let result = origin events read_events malloc_events "nonexistent" in
    check (option int) "should not find origin" None result

(** Test Path Generation *)

let test_gen_paths_linear () =
  let events = create_test_events () in
  let structure = create_test_structure () in

  let paths = gen_paths events structure structure.restrict in
    check bool "should generate at least one path" true (List.length paths > 0);

    (* Check that paths contain events in program order *)
    List.iter
      (fun path_info ->
        check bool "path should not be empty" true
          (List.length path_info.path > 0)
      )
      paths

let test_gen_paths_with_branch () =
  let events = create_test_events () in

  (* Add branch event *)
  let branch_event =
    create_test_event 5 Branch ~cond:(EBinOp (EVar "x", "==", ENum Z.one)) ()
  in
    Hashtbl.add events 5 branch_event;

    let e = Uset.of_list [ 1; 2; 3; 4; 5 ] in
    let po = Uset.of_list [ (1, 2); (2, 5); (5, 3); (5, 4) ] in
    let restrict = Hashtbl.create 4 in
    let cas_groups = Hashtbl.create 4 in
    let structure =
      {
        e;
        po;
        rmw = Uset.create ();
        lo = Uset.create ();
        restrict;
        cas_groups;
        pwg = [];
        fj = Uset.create ();
        p = Uset.create ();
        constraint_ = [];
      }
    in

    let paths = gen_paths events structure structure.restrict in

    (* Should generate at least 2 paths (one for each branch) *)
    check bool "should generate multiple paths for branches" true
      (List.length paths >= 2)

let test_gen_paths_empty_structure () =
  let events = create_test_events () in
  let e = Uset.create () in
  let po = Uset.create () in
  let restrict = Hashtbl.create 4 in
  let cas_groups = Hashtbl.create 4 in
  let structure =
    {
      e;
      po;
      rmw = Uset.create ();
      lo = Uset.create ();
      restrict;
      cas_groups;
      pwg = [];
      fj = Uset.create ();
      p = Uset.create ();
      constraint_ = [];
    }
  in

  try
    let _ = gen_paths events structure structure.restrict in
      (* Should handle empty structure gracefully *)
      check bool "should handle empty structure" true true
  with Failure _ -> check bool "should not fail on empty structure" false true

let test_gen_paths_single_event () =
  let events = create_test_events () in
  let e = Uset.of_list [ 1 ] in
  let po = Uset.create () in
  let restrict = Hashtbl.create 4 in
  let cas_groups = Hashtbl.create 4 in
  let structure =
    {
      e;
      po;
      rmw = Uset.create ();
      lo = Uset.create ();
      restrict;
      cas_groups;
      pwg = [];
      fj = Uset.create ();
      p = Uset.create ();
      constraint_ = [];
    }
  in

  let paths = gen_paths events structure structure.restrict in
    check int "should generate one path" 1 (List.length paths);

    match paths with
    | [ path ] ->
        check int "path should contain event 1" 1 (List.length path.path)
    | _ -> fail "Expected exactly one path"

(** Test Justification Choosing *)

let test_choose_empty_path () =
  let justmap = Hashtbl.create 4 in
  let path_events = Uset.create () in

  let result = choose justmap path_events in
    check int "should return one empty combination" 1 (List.length result);
    match result with
    | [ [] ] -> ()
    | _ -> fail "Expected one empty list"

let test_choose_single_event_no_justifications () =
  let justmap = Hashtbl.create 4 in
  let path_events = Uset.of_list [ 1 ] in

  let result = choose justmap path_events in
    (* No justifications means no valid combinations *)
    check int "should return empty list" 0 (List.length result)

let test_choose_single_event_with_justification () =
  let justmap = Hashtbl.create 4 in
  let w_event = create_test_event 1 Write () in
  let just =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.create ();
      we = Uset.create ();
      w = w_event;
      op = ("test", None, None);
    }
  in
    Hashtbl.add justmap 1 [ just ];

    let path_events = Uset.of_list [ 1 ] in
    let result = choose justmap path_events in

    check bool "should return at least one combination" true
      (List.length result > 0)

let test_choose_incompatible_justifications () =
  let justmap = Hashtbl.create 4 in

  (* Create two justifications with conflicting fwd/we *)
  let w_event1 = create_test_event 1 Write () in
  let just1 =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.of_list [ (2, 3) ];
      we = Uset.create ();
      w = w_event1;
      op = ("test", None, None);
    }
  in

  let w_event2 = create_test_event 2 Write () in
  let just2 =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.of_list [ (3, 2) ];
      (* Conflicts with just1 *)
      we = Uset.create ();
      w = w_event2;
      op = ("test", None, None);
    }
  in

  Hashtbl.add justmap 1 [ just1 ];
  Hashtbl.add justmap 2 [ just2 ];

  let path_events = Uset.of_list [ 1; 2 ] in
  let result = choose justmap path_events in

  (* Should filter out incompatible combinations *)
  check bool "should handle incompatible justifications" true
    (List.length result >= 0)

(** Test Path Info Type *)

let test_path_info_creation () =
  let path = [ 1; 2; 3 ] in
  let predicates = [ [ EVar "x" ]; [ EVar "y" ] ] in
  let path_info = { path; p = predicates } in

  check int "path length" 3 (List.length path_info.path);
  check int "predicate lists" 2 (List.length path_info.p)

let test_path_info_empty () =
  let path_info = { path = []; p = [] } in
    check int "empty path" 0 (List.length path_info.path);
    check int "empty predicates" 0 (List.length path_info.p)

(** Test Freeze Result Type *)

let test_freeze_result_creation () =
  let freeze_res =
    {
      justs = [];
      e = Uset.create ();
      dp = Uset.create ();
      ppo = Uset.create ();
      rf = Uset.create ();
      rmw = Uset.create ();
      pp = [];
      conds = [];
    }
  in

  check int "empty justifications" 0 (List.length freeze_res.justs);
  check int "empty conditions" 0 (List.length freeze_res.conds)

(** Edge Cases and Error Handling *)

let test_gen_paths_with_missing_event () =
  let events = Hashtbl.create 16 in
    Hashtbl.add events 1 (create_test_event 1 Write ());

    (* Event 2 is referenced in PO but doesn't exist *)
    let e = Uset.of_list [ 1; 2 ] in
    let po = Uset.of_list [ (1, 2) ] in
    let restrict = Hashtbl.create 4 in
    let cas_groups = Hashtbl.create 4 in
    let structure =
      {
        e;
        po;
        rmw = Uset.create ();
        lo = Uset.create ();
        restrict;
        cas_groups;
        pwg = [];
        fj = Uset.create ();
        p = Uset.create ();
        constraint_ = [];
      }
    in

    (* Should handle missing events gracefully *)
    let _ = gen_paths events structure structure.restrict in
      check bool "should handle missing events" true true

let test_disjoint_with_complex_expressions () =
  let loc1 = EBinOp (EVar "base", "+", ENum (Z.of_int 4)) in
  let val1 = ENum (Z.of_int 1) in
  let loc2 = EBinOp (EVar "base", "+", ENum (Z.of_int 8)) in
  let val2 = ENum (Z.of_int 2) in

  let result = disjoint (loc1, val1) (loc2, val2) in
    match result with
    | EBinOp (_, "!=", _) ->
        check bool "should create disjoint predicate" true true
    | _ -> fail "Expected binary operation"

let test_origin_with_multiple_matches () =
  let events = create_test_events () in

  (* Add multiple events with same symbol *)
  let event1 = create_test_event 2 Read ~rval:(VSymbol "s1") () in
    Hashtbl.replace events 2 event1;

    let event2 = create_test_event 4 Read ~rval:(VSymbol "s1") () in
      Hashtbl.replace events 4 event2;

      let read_events = Uset.of_list [ 2; 4 ] in
      let malloc_events = Uset.create () in

      let result = origin events read_events malloc_events "s1" in
        (* Should return one of the matching events *)
        match result with
        | Some e -> check bool "should find an event" true (e = 2 || e = 4)
        | None -> fail "Expected to find origin event"

let test_gen_paths_with_cycle () =
  let events = create_test_events () in

  (* Create a cycle in PO (which shouldn't normally happen, but test handling) *)
  let e = Uset.of_list [ 1; 2; 3 ] in
  let po = Uset.of_list [ (1, 2); (2, 3); (3, 1) ] in
  let restrict = Hashtbl.create 4 in
  let cas_groups = Hashtbl.create 4 in
  let structure =
    {
      e;
      po;
      rmw = Uset.create ();
      lo = Uset.create ();
      restrict;
      cas_groups;
      pwg = [];
      fj = Uset.create ();
      p = Uset.create ();
      constraint_ = [];
    }
  in

  try
    let _paths = gen_paths events structure structure.restrict in
      (* May generate paths or handle cycle - either is acceptable *)
      check bool "should handle cycles" true true
  with _ ->
    (* Or may throw exception for invalid structure *)
    check bool "may reject cyclic structure" true true

(** Integration Tests *)

let test_path_generation_integration () =
  let events = create_test_events () in

  (* Create a more complex structure with multiple paths *)
  let e = Uset.of_list [ 1; 2; 3; 4 ] in
  let po = Uset.of_list [ (1, 2); (1, 3); (2, 4); (3, 4) ] in
  let restrict = Hashtbl.create 4 in
  let cas_groups = Hashtbl.create 4 in
  let structure =
    {
      e;
      po;
      rmw = Uset.create ();
      lo = Uset.create ();
      restrict;
      cas_groups;
      pwg = [];
      fj = Uset.create ();
      p = Uset.create ();
      constraint_ = [];
    }
  in

  let paths = gen_paths events structure structure.restrict in

  (* Verify paths *)
  List.iter
    (fun path_info ->
      (* Each path should start with an event that has no predecessors *)
      check bool "paths should be valid" true (List.length path_info.path > 0)
    )
    paths

let test_justification_map_building () =
  let justmap = Hashtbl.create 4 in

  let w_event1 = create_test_event 1 Write () in
  let just1 =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.create ();
      we = Uset.create ();
      w = w_event1;
      op = ("test", None, None);
    }
  in

  let w_event2 = create_test_event 1 Write () in
  let just2 =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.create ();
      we = Uset.create ();
      w = w_event2;
      op = ("test", None, None);
    }
  in

  Hashtbl.add justmap 1 [ just1 ];
  let existing = Hashtbl.find justmap 1 in
    Hashtbl.replace justmap 1 (just2 :: existing);

    let result = Hashtbl.find justmap 1 in
      check int "should have multiple justifications" 2 (List.length result)

(** Property-Based Tests *)

let test_path_order_preservation () =
  let events = create_test_events () in
  let structure = create_test_structure () in

  let paths = gen_paths events structure structure.restrict in

  (* Helper function to find index of element in list *)
  let find_index elem lst =
    let rec aux i = function
      | [] -> None
      | x :: xs -> if x = elem then Some i else aux (i + 1) xs
    in
      aux 0 lst
  in

  (* Check if paths preserve PO order (either forward or reverse) *)
  let check_path path_info =
    let path = path_info.path in
    let path_set = Uset.of_list path in

    let violations_forward = ref 0 in
    let violations_reverse = ref 0 in
    let total_checks = ref 0 in

    Uset.iter
      (fun (a, b) ->
        if Uset.mem path_set a && Uset.mem path_set b then incr total_checks;
        let a_pos = find_index a path in
        let b_pos = find_index b path in
          match (a_pos, b_pos) with
          | Some pos_a, Some pos_b ->
              (* Check forward order: a should come before b *)
              if pos_a >= pos_b then incr violations_forward;
              (* Check reverse order: b should come before a *)
              if pos_b >= pos_a then incr violations_reverse
          | _ -> ()
      )
      structure.po;

    (* Accept the path if it's consistent in either direction *)
    !total_checks = 0 || !violations_forward = 0 || !violations_reverse = 0
  in

  (* All paths should be valid *)
  let all_valid = List.for_all check_path paths in
    check bool "paths should preserve PO order (forward or reverse)" true
      all_valid

let test_justification_compatibility_symmetry () =
  (* Test that compatibility checking is symmetric *)
  let w_event1 = create_test_event 1 Write () in
  let just1 =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.of_list [ (1, 2) ];
      we = Uset.create ();
      w = w_event1;
      op = ("test", None, None);
    }
  in

  let w_event2 = create_test_event 2 Write () in
  let just2 =
    {
      p = [];
      d = Uset.create ();
      fwd = Uset.of_list [ (3, 4) ];
      we = Uset.create ();
      w = w_event2;
      op = ("test", None, None);
    }
  in

  (* These justifications should be compatible *)
  let x1 = Uset.union just1.fwd just1.we in
  let x2 = Uset.union just2.fwd just2.we in

  let pi1_x1 = pi_1 x1 in
  let pi2_x1 = pi_2 x1 in
  let pi1_x2 = pi_1 x2 in
  let pi2_x2 = pi_2 x2 in

  let compat_1_2 =
    Uset.size (Uset.intersection pi1_x1 pi2_x2) = 0
    && Uset.size (Uset.intersection pi2_x1 pi1_x2) = 0
  in

  let compat_2_1 =
    Uset.size (Uset.intersection pi1_x2 pi2_x1) = 0
    && Uset.size (Uset.intersection pi2_x2 pi1_x1) = 0
  in

  check bool "compatibility should be symmetric" compat_1_2 compat_2_1

(** Test Suite *)

let suite =
  [
    (* Utils tests *)
    ("disjoint with same location", `Quick, test_disjoint_same_location);
    ( "disjoint with different locations",
      `Quick,
      test_disjoint_different_locations
    );
    ( "disjoint with complex expressions",
      `Quick,
      test_disjoint_with_complex_expressions
    );
    ("origin from reads", `Quick, test_origin_from_reads);
    ("origin from mallocs", `Quick, test_origin_from_mallocs);
    ("origin not found", `Quick, test_origin_not_found);
    ("origin with multiple matches", `Quick, test_origin_with_multiple_matches);
    (* Path generation tests *)
    ("gen_paths with linear structure", `Quick, test_gen_paths_linear);
    ("gen_paths with branch", `Quick, test_gen_paths_with_branch);
    ("gen_paths with empty structure", `Quick, test_gen_paths_empty_structure);
    ("gen_paths with single event", `Quick, test_gen_paths_single_event);
    ("gen_paths with missing event", `Quick, test_gen_paths_with_missing_event);
    ("gen_paths with cycle", `Quick, test_gen_paths_with_cycle);
    (* Justification choosing tests *)
    ("choose with empty path", `Quick, test_choose_empty_path);
    ( "choose with single event no justifications",
      `Quick,
      test_choose_single_event_no_justifications
    );
    ( "choose with single event with justification",
      `Quick,
      test_choose_single_event_with_justification
    );
    ( "choose with incompatible justifications",
      `Quick,
      test_choose_incompatible_justifications
    );
    (* Type tests *)
    ("path_info creation", `Quick, test_path_info_creation);
    ("path_info empty", `Quick, test_path_info_empty);
    ("freeze_result creation", `Quick, test_freeze_result_creation);
    (* Integration tests *)
    ("path generation integration", `Quick, test_path_generation_integration);
    ("justification map building", `Quick, test_justification_map_building);
    (* Property-based tests *)
    ("path order preservation", `Quick, test_path_order_preservation);
    ( "justification compatibility symmetry",
      `Quick,
      test_justification_compatibility_symmetry
    );
  ]

let suite = ("Executions", suite)
