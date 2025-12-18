open Uset
(* Unit tests for histories, futures, and posterior futures *)

open Alcotest
open Futures
open Types

(* Helper function to create a symbolic execution for testing *)
let make_test_exec ex_e rf dp ppo ex_rmw ex_p fix_rf_map pointer_map final_env :
    symbolic_execution =
  { ex_e; rf; dp; ppo; ex_rmw; ex_p; fix_rf_map; pointer_map; final_env }

(* Helper to create minimal test execution with just events and relations *)
let make_simple_exec events rf dp ppo =
  make_test_exec events rf dp ppo
    (USet.create ()) (* ex_rmw *)
    [] (* ex_p *)
    (Hashtbl.create 10) (* fix_rf_map *)
    None (* pointer_map *)
    (Hashtbl.create 10)
(* final_env *)

(* Custom testable for int USet.t *)
let int_uset_testable =
  let pp fmt s =
    let elements = USet.values s |> List.sort compare in
      Format.fprintf fmt "{%s}"
        (String.concat ", " (List.map string_of_int elements))
  in
  let equal s1 s2 = USet.equal s1 s2 in
    testable pp equal

(* Custom testable for int USet.t USet.t (set of sets) *)
let int_uset_set_testable =
  let pp fmt ss =
    let sets = USet.values ss in
      Format.fprintf fmt "{ %a }"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt s ->
             let elements = USet.values s |> List.sort compare in
               Format.fprintf fmt "{%s}"
                 (String.concat ", " (List.map string_of_int elements))
           )
        )
        sets
  in
  let equal ss1 ss2 =
    USet.size ss1 = USet.size ss2
    && USet.for_all (fun s1 -> USet.exists (fun s2 -> USet.equal s1 s2) ss2) ss1
  in
    testable pp equal

(* Custom testable for (int * int) USet.t (relation/future) *)
let relation_testable =
  let pp fmt s =
    let pairs = USet.values s |> List.sort compare in
      Format.fprintf fmt "{%s}"
        (String.concat ", "
           (List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) pairs)
        )
  in
  let equal s1 s2 = USet.equal s1 s2 in
    testable pp equal

(* Custom testable for future_set *)
let future_set_testable =
  let pp fmt fs =
    let futures = USet.values fs in
      Format.fprintf fmt "{ %a }"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt f ->
             let pairs = USet.values f |> List.sort compare in
               Format.fprintf fmt "{%s}"
                 (String.concat ", "
                    (List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) pairs)
                 )
           )
        )
        futures
  in
  let equal fs1 fs2 =
    USet.size fs1 = USet.size fs2
    && USet.for_all (fun f1 -> USet.exists (fun f2 -> USet.equal f1 f2) fs2) fs1
  in
    testable pp equal

(* Helper to check if a history is downward closed *)
let is_downward_closed exec history =
  let check_relation rel =
    USet.for_all
      (fun (e1, e2) -> if USet.mem history e2 then USet.mem history e1 else true)
      rel
  in
    check_relation exec.ppo && check_relation exec.dp && check_relation exec.rf

(** Tests for calculate_histories **)

let test_histories_empty_execution () =
  let exec =
    make_simple_exec (USet.create ()) (USet.create ()) (USet.create ())
      (USet.create ())
  in
  let histories = calculate_histories exec in
    (* Only the empty history should exist *)
    check int "size" 1 (USet.size histories);
    let empty_hist = USet.create () in
      check bool "contains empty" true
        (USet.exists (fun h -> USet.equal h empty_hist) histories)

let test_histories_single_event_no_deps () =
  let events = USet.of_list [ 1 ] in
  let exec =
    make_simple_exec events (USet.create ()) (USet.create ()) (USet.create ())
  in
  let histories = calculate_histories exec in
    (* Should have: {}, {1} *)
    check int "size" 2 (USet.size histories);
    USet.iter
      (fun h -> check bool "is downward closed" true (is_downward_closed exec h))
      histories

let test_histories_two_independent_events () =
  let events = USet.of_list [ 1; 2 ] in
  let exec =
    make_simple_exec events (USet.create ()) (USet.create ()) (USet.create ())
  in
  let histories = calculate_histories exec in
    (* Should have: {}, {1}, {2}, {1,2} *)
    check int "size" 4 (USet.size histories);
    USet.iter
      (fun h -> check bool "is downward closed" true (is_downward_closed exec h))
      histories

let test_histories_chain_ppo () =
  (* Event 2 depends on event 1 via ppo: (1,2) in ppo *)
  let events = USet.of_list [ 1; 2 ] in
  let ppo = USet.of_list [ (1, 2) ] in
  let exec = make_simple_exec events (USet.create ()) (USet.create ()) ppo in
  let histories = calculate_histories exec in
    (* Should have: {}, {1}, {1,2} *)
    (* Cannot have {2} alone because 2 depends on 1 *)
    check int "size" 3 (USet.size histories);
    USet.iter
      (fun h -> check bool "is downward closed" true (is_downward_closed exec h))
      histories;
    (* Verify {2} without {1} is not in histories *)
    let invalid_hist = USet.of_list [ 2 ] in
      check bool "does not contain {2}" false
        (USet.exists (fun h -> USet.equal h invalid_hist) histories)

let test_histories_multiple_deps () =
  (* Event 3 depends on both 1 and 2 *)
  (* (1,3) in ppo, (2,3) in dp *)
  let events = USet.of_list [ 1; 2; 3 ] in
  let ppo = USet.of_list [ (1, 3) ] in
  let dp = USet.of_list [ (2, 3) ] in
  let exec = make_simple_exec events (USet.create ()) dp ppo in
  let histories = calculate_histories exec in
    (* Valid histories: {}, {1}, {2}, {1,2}, {1,2,3} *)
    (* Cannot have {3} or {1,3} or {2,3} because 3 needs both 1 and 2 *)
    check int "size" 5 (USet.size histories);
    USet.iter
      (fun h -> check bool "is downward closed" true (is_downward_closed exec h))
      histories;
    (* Check that {1,2,3} is present *)
    let full_hist = USet.of_list [ 1; 2; 3 ] in
      check bool "contains {1,2,3}" true
        (USet.exists (fun h -> USet.equal h full_hist) histories)

let test_histories_with_rf () =
  (* Event 2 reads from event 1: (1,2) in rf *)
  let events = USet.of_list [ 1; 2 ] in
  let rf = USet.of_list [ (1, 2) ] in
  let exec = make_simple_exec events rf (USet.create ()) (USet.create ()) in
  let histories = calculate_histories exec in
    (* Should have: {}, {1}, {1,2} *)
    check int "size" 3 (USet.size histories);
    USet.iter
      (fun h -> check bool "is downward closed" true (is_downward_closed exec h))
      histories

let test_histories_complex_dag () =
  (* Complex DAG: 1 -> 2 -> 4
                    \-> 3 -> 4 *)
  let events = USet.of_list [ 1; 2; 3; 4 ] in
  let ppo = USet.of_list [ (1, 2); (2, 4) ] in
  let dp = USet.of_list [ (1, 3); (3, 4) ] in
  let exec = make_simple_exec events (USet.create ()) dp ppo in
  let histories = calculate_histories exec in
    (* All histories must be downward closed *)
    USet.iter
      (fun h -> check bool "is downward closed" true (is_downward_closed exec h))
      histories;
    (* {4} alone is invalid *)
    let invalid = USet.of_list [ 4 ] in
      check bool "does not contain {4}" false
        (USet.exists (fun h -> USet.equal h invalid) histories);
      (* {1,2,3,4} is valid *)
      let full = USet.of_list [ 1; 2; 3; 4 ] in
        check bool "contains full" true
          (USet.exists (fun h -> USet.equal h full) histories)

(** Tests for calculate_future_set **)

let test_future_set_empty () =
  let execs = USet.create () in
  let futures = calculate_future_set execs in
    check int "empty execs gives empty futures" 0 (USet.size futures)

let test_future_set_single_exec_no_relations () =
  let events = USet.of_list [ 1; 2 ] in
  let exec =
    make_simple_exec events (USet.create ()) (USet.create ()) (USet.create ())
  in
  let execs = USet.singleton exec in
  let futures = calculate_future_set execs in
    check int "one future" 1 (USet.size futures);
    (* Future should be identity relation: {(1,1), (2,2)} *)
    let expected = USet.of_list [ (1, 1); (2, 2) ] in
      check bool "contains identity" true
        (USet.exists (fun f -> USet.equal f expected) futures)

let test_future_set_with_ppo () =
  let events = USet.of_list [ 1; 2 ] in
  let ppo = USet.of_list [ (1, 2) ] in
  let exec = make_simple_exec events (USet.create ()) (USet.create ()) ppo in
  let execs = USet.singleton exec in
  let futures = calculate_future_set execs in
  (* Future should be identity + ppo: {(1,1), (2,2), (1,2)} *)
  let expected = USet.of_list [ (1, 1); (2, 2); (1, 2) ] in
    check bool "contains identity + ppo" true
      (USet.exists (fun f -> USet.equal f expected) futures)

let test_future_set_with_dp () =
  let events = USet.of_list [ 1; 2 ] in
  let dp = USet.of_list [ (1, 2) ] in
  let exec = make_simple_exec events (USet.create ()) dp (USet.create ()) in
  let execs = USet.singleton exec in
  let futures = calculate_future_set execs in
  (* Future should be identity + dp: {(1,1), (2,2), (1,2)} *)
  let expected = USet.of_list [ (1, 1); (2, 2); (1, 2) ] in
    check bool "contains identity + dp" true
      (USet.exists (fun f -> USet.equal f expected) futures)

let test_future_set_multiple_execs () =
  let events1 = USet.of_list [ 1; 2 ] in
  let ppo1 = USet.of_list [ (1, 2) ] in
  let exec1 = make_simple_exec events1 (USet.create ()) (USet.create ()) ppo1 in

  let events2 = USet.of_list [ 3; 4 ] in
  let dp2 = USet.of_list [ (3, 4) ] in
  let exec2 = make_simple_exec events2 (USet.create ()) dp2 (USet.create ()) in

  let execs = USet.of_list [ exec1; exec2 ] in
  let futures = calculate_future_set execs in
    check int "two futures" 2 (USet.size futures)

(** Tests for posterior_future **)

let test_posterior_future_empty_history () =
  let future = USet.of_list [ (1, 2); (2, 3); (3, 4) ] in
  let history = USet.create () in
  let post = posterior_future future history in
    (* With empty history, all pairs should remain *)
    check relation_testable "all pairs remain" future post

let test_posterior_future_full_history () =
  let future = USet.of_list [ (1, 2); (2, 3) ] in
  let history = USet.of_list [ 1; 2; 3 ] in
  let post = posterior_future future history in
    (* All first elements are in history, so result should be empty *)
    check int "empty result" 0 (USet.size post)

let test_posterior_future_partial_history () =
  let future = USet.of_list [ (1, 2); (2, 3); (3, 4) ] in
  let history = USet.of_list [ 1; 2 ] in
  let post = posterior_future future history in
  (* Only (3,4) should remain, as 1 and 2 are in history *)
  let expected = USet.of_list [ (3, 4) ] in
    check relation_testable "only (3,4)" expected post

let test_posterior_future_no_overlap () =
  let future = USet.of_list [ (1, 2); (2, 3) ] in
  let history = USet.of_list [ 4; 5 ] in
  let post = posterior_future future history in
    (* No overlap, all pairs should remain *)
    check relation_testable "all remain" future post

let test_posterior_future_identity_pairs () =
  let future = USet.of_list [ (1, 1); (2, 2); (3, 3) ] in
  let history = USet.of_list [ 2 ] in
  let post = posterior_future future history in
  (* Only (2,2) should be removed *)
  let expected = USet.of_list [ (1, 1); (3, 3) ] in
    check relation_testable "remove (2,2)" expected post

(** Tests for posterior_future_set **)

let test_posterior_future_set_empty_set () =
  let future_set = USet.create () in
  let history = USet.of_list [ 1; 2 ] in
  let post_set = posterior_future_set future_set history in
    check int "empty result" 0 (USet.size post_set)

let test_posterior_future_set_single_future () =
  let future = USet.of_list [ (1, 2); (3, 4) ] in
  let future_set = USet.singleton future in
  let history = USet.of_list [ 1 ] in
  let post_set = posterior_future_set future_set history in
    check int "one result" 1 (USet.size post_set);
    let expected = USet.of_list [ (3, 4) ] in
      check bool "correct posterior" true
        (USet.exists (fun f -> USet.equal f expected) post_set)

let test_posterior_future_set_multiple_futures () =
  let future1 = USet.of_list [ (1, 2); (2, 3) ] in
  let future2 = USet.of_list [ (3, 4); (4, 5) ] in
  let future_set = USet.of_list [ future1; future2 ] in
  let history = USet.of_list [ 1; 3 ] in
  let post_set = posterior_future_set future_set history in
    check int "two results" 2 (USet.size post_set);
    (* future1 -> {(2,3)}, future2 -> {(4,5)} *)
    let expected1 = USet.of_list [ (2, 3) ] in
    let expected2 = USet.of_list [ (4, 5) ] in
      check bool "contains first posterior" true
        (USet.exists (fun f -> USet.equal f expected1) post_set);
      check bool "contains second posterior" true
        (USet.exists (fun f -> USet.equal f expected2) post_set)

let test_posterior_future_set_all_filtered () =
  let future = USet.of_list [ (1, 2); (2, 3) ] in
  let future_set = USet.singleton future in
  let history = USet.of_list [ 1; 2; 3; 4 ] in
  let post_set = posterior_future_set future_set history in
    check int "one result" 1 (USet.size post_set);
    let empty_future = USet.create () in
      check bool "empty future" true
        (USet.exists (fun f -> USet.equal f empty_future) post_set)

(** Test suite **)

let histories_tests =
  [
    test_case "empty execution" `Quick test_histories_empty_execution;
    test_case "single event no deps" `Quick test_histories_single_event_no_deps;
    test_case "two independent events" `Quick
      test_histories_two_independent_events;
    test_case "chain with ppo" `Quick test_histories_chain_ppo;
    test_case "multiple dependencies" `Quick test_histories_multiple_deps;
    test_case "with reads-from" `Quick test_histories_with_rf;
    test_case "complex DAG" `Quick test_histories_complex_dag;
  ]

let future_set_tests =
  [
    test_case "empty executions" `Quick test_future_set_empty;
    test_case "single exec no relations" `Quick
      test_future_set_single_exec_no_relations;
    test_case "with ppo" `Quick test_future_set_with_ppo;
    test_case "with dp" `Quick test_future_set_with_dp;
    test_case "multiple executions" `Quick test_future_set_multiple_execs;
  ]

let posterior_future_tests =
  [
    test_case "empty history" `Quick test_posterior_future_empty_history;
    test_case "full history" `Quick test_posterior_future_full_history;
    test_case "partial history" `Quick test_posterior_future_partial_history;
    test_case "no overlap" `Quick test_posterior_future_no_overlap;
    test_case "identity pairs" `Quick test_posterior_future_identity_pairs;
  ]

let posterior_future_set_tests =
  [
    test_case "empty set" `Quick test_posterior_future_set_empty_set;
    test_case "single future" `Quick test_posterior_future_set_single_future;
    test_case "multiple futures" `Quick
      test_posterior_future_set_multiple_futures;
    test_case "all filtered" `Quick test_posterior_future_set_all_filtered;
  ]

let suite =
  ( "Histories and Futures",
    histories_tests
    @ future_set_tests
    @ posterior_future_tests
    @ posterior_future_set_tests
  )
