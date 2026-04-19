(** Unit tests for assertion checking, covering the two bugs fixed in Assertion:

    Bug 1 – allow (ub): UB executions produced no assertion instances because
    [process_executions] only created instances inside the [Some detail] branch
    of [detail_opt], which is always [None] for UB assertions. Fixed by adding a
    [None] branch that synthesises instances from [local_ub_reasons].

    Bug 2 – forbid (ub): [check_outcome_assertion] called [handle_no_executions]
    unconditionally, which returned an early [empty_result] (assertion_instances
    = None) for every non-exhaustive Forbid run, bypassing [process_executions]
    entirely even when executions existed. Fixed by guarding the early return on
    [executions = []]. *)

open Context
open Ir
open Types
open Uset

(* ------------------------------------------------------------------ *)
(*  Helpers                                                            *)
(* ------------------------------------------------------------------ *)

(** Run an Lwt promise synchronously. *)
let sync = Lwt_main.run

(** Build a minimal [event] record. Only [typ] and [loc] are meaningful for UB
    detection; all other fields are set to inert defaults. *)
let make_event typ loc =
  {
    label = 0;
    typ;
    id = None;
    loc = Some loc;
    rval = None;
    wval = None;
    cond = None;
    rmod = Normal;
    wmod = Normal;
    fmod = Normal;
    volatile = false;
    strong = None;
    is_rdmw = false;
  }

(** Build a [symbolic_event_structure] from an event table and the four cached
    event-filter sets that [UBValidation] reads. Every other field is set to an
    empty/unit value. *)
let make_structure ?(fj = USet.create ()) ?(malloc_events = USet.create ())
    ?(free_events = USet.create ()) ?(read_events = USet.create ())
    ?(write_events = USet.create ()) events_tbl =
  {
    e = USet.create ();
    events = events_tbl;
    po = USet.create ();
    po_iter = USet.create ();
    rmw = USet.create ();
    lo = USet.create ();
    restrict = Hashtbl.create 0;
    defacto = Hashtbl.create 0;
    fj;
    p = Hashtbl.create 0;
    constraints = [];
    conflict = USet.create ();
    origin = Hashtbl.create 0;
    loop_indices = Hashtbl.create 0;
    loop_conditions = Hashtbl.create 0;
    thread_index = Hashtbl.create 0;
    write_events;
    read_events;
    rlx_write_events = USet.create ();
    rlx_read_events = USet.create ();
    fence_events = USet.create ();
    branch_events = USet.create ();
    malloc_events;
    free_events;
    terminal_events = USet.create ();
  }

(** Build a [symbolic_execution] with the given event set [e] and id. Accepts
    optional [ppo], [dp], [rf], [fix_rf_map], [final_env]. *)
let make_execution ?(ppo = USet.create ()) ?(dp = USet.create ())
    ?(rf = USet.create ()) ?(fix_rf_map = Hashtbl.create 0)
    ?(final_env = Hashtbl.create 0) ~id e =
  {
    id;
    e;
    rf;
    dp;
    ppo;
    rmw = USet.create ();
    ex_p = [];
    fix_rf_map;
    pointer_map = None;
    final_env;
  }

(** Build an [Outcome] assertion for the given outcome with [CondUB]. *)
let ub_assertion outcome = Outcome { outcome; condition = CondUB; model = None }

let check_assertion = Assertion.check_assertion

(* ------------------------------------------------------------------ *)
(*  Shared UAF fixture                                                 *)
(*                                                                     *)
(*  Events:                                                            *)
(*    1 – Malloc  loc = α                                              *)
(*    2 – Free    loc = α                                              *)
(*    3 – Write   loc = α  (no rhb edge 3→2, so write-after-free)     *)
(*                                                                     *)
(*  This is the minimal structure that makes UBValidation.UAF.check   *)
(*  report a violation.                                                *)
(* ------------------------------------------------------------------ *)

let uaf_loc = EVar "α"

let make_uaf_fixture () =
  let tbl = Hashtbl.create 8 in
    Hashtbl.add tbl 1 (make_event Malloc uaf_loc);
    Hashtbl.add tbl 2 (make_event Free uaf_loc);
    Hashtbl.add tbl 3 (make_event Write uaf_loc);
    let structure =
      make_structure tbl ~malloc_events:(USet.of_list [ 1 ])
        ~free_events:(USet.of_list [ 2 ]) ~write_events:(USet.of_list [ 3 ])
    in
    (* All three events active; no rf, no ppo — so no ordering constrains
     the write relative to the free, admitting UAF. *)
    let execution = make_execution ~id:1 (USet.of_list [ 1; 2; 3 ]) in
      (structure, execution)

(** A clean fixture: malloc + write ordered by ppo, no free — no UAF. Event IDs
    are based on [base] to avoid clashes when merged into a shared structure. *)
let make_clean_events base loc_sym =
  let loc = EVar loc_sym in
  let m = base and w = base + 1 in
  let tbl = Hashtbl.create 4 in
    Hashtbl.add tbl m (make_event Malloc loc);
    Hashtbl.add tbl w (make_event Write loc);
    let ppo = USet.of_list [ (m, w) ] in
    let evts = USet.of_list [ m; w ] in
      (tbl, m, w, ppo, evts)

(* ------------------------------------------------------------------ *)
(*  Test assertion helpers                                             *)
(* ------------------------------------------------------------------ *)

let assert_instances_some_nonempty label (result : Assertion.assertion_result) =
  match result.assertion_instances with
  | None -> Alcotest.fail (label ^ ": assertion_instances is None")
  | Some [] -> Alcotest.fail (label ^ ": assertion_instances is Some [] (empty)")
  | Some _ -> ()

let assert_instances_some label (result : Assertion.assertion_result) =
  match result.assertion_instances with
  | None -> Alcotest.fail (label ^ ": assertion_instances is None")
  | Some _ -> ()

let instances_of (result : Assertion.assertion_result) =
  match result.assertion_instances with
  | Some lst -> lst
  | None -> Alcotest.fail "assertion_instances unexpectedly None"

let assert_all_witnessed label instances =
  List.iter
    (function
      | Witnessed _ -> ()
      | Contradicted { exec_id; _ } ->
          Alcotest.fail
            (Printf.sprintf
               "%s: expected Witnessed, got Contradicted (exec_id=%d)" label
               exec_id
            )
      | Confirmed | Refuted ->
          Alcotest.fail (label ^ ": expected Witnessed, got Confirmed/Refuted")
      )
    instances

let assert_all_contradicted label instances =
  List.iter
    (function
      | Contradicted _ -> ()
      | Witnessed { exec_id; _ } ->
          Alcotest.fail
            (Printf.sprintf
               "%s: expected Contradicted, got Witnessed (exec_id=%d)" label
               exec_id
            )
      | Confirmed | Refuted ->
          Alcotest.fail
            (label ^ ": expected Contradicted, got Confirmed/Refuted")
      )
    instances

(* ================================================================== *)
(*  Bug 1 – allow (ub): instances must be emitted for UB executions   *)
(* ================================================================== *)

(* Data provider: 1, 2, and 3 concurrent UB executions. *)
let ub_exec_counts = [ 1; 2; 3 ]

(** For each exec count: instances must be Some and non-empty. *)
let test_allow_ub_instances_nonempty n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync (check_assertion (ub_assertion Allow) execs structure ~exhaustive:false)
  in
    assert_instances_some_nonempty
      (Printf.sprintf "allow(ub) %d exec(s): non-empty instances" n)
      result

(** For each exec count: exactly one Witnessed instance per UB execution. *)
let test_allow_ub_instance_count n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync (check_assertion (ub_assertion Allow) execs structure ~exhaustive:false)
  in
    Alcotest.(check int)
      (Printf.sprintf "allow(ub) %d exec(s): instance count" n)
      n
      (List.length (instances_of result))

(** All instances must be Witnessed (not Contradicted). *)
let test_allow_ub_instances_witnessed n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync (check_assertion (ub_assertion Allow) execs structure ~exhaustive:false)
  in
    assert_all_witnessed
      (Printf.sprintf "allow(ub) %d exec(s): all Witnessed" n)
      (instances_of result)

(** Witnessed instances carry the correct execution ids. *)
let test_allow_ub_exec_ids n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync (check_assertion (ub_assertion Allow) execs structure ~exhaustive:false)
  in
  let got =
    List.filter_map
      (function
        | Witnessed { exec_id; _ } -> Some exec_id
        | _ -> None
        )
      (instances_of result)
    |> List.sort compare
  in
  let expected = List.init n (fun i -> i + 1) in
    Alcotest.(check (list int))
      (Printf.sprintf "allow(ub) %d exec(s): exec_ids" n)
      expected got

(** allow (ub) is valid when UB is present. *)
let test_allow_ub_valid_when_ub () =
  let structure, ex = make_uaf_fixture () in
  let result =
    sync
      (check_assertion (ub_assertion Allow) [ ex ] structure ~exhaustive:false)
  in
    Alcotest.(check bool)
      "allow(ub) + UB present → valid=true" true result.valid

(** allow (ub) with no UB: Some [] instances, valid=false. *)
let test_allow_ub_no_ub_executions () =
  let tbl, m, w, ppo, evts = make_clean_events 10 "β" in
  let structure =
    make_structure tbl ~malloc_events:(USet.of_list [ m ])
      ~write_events:(USet.of_list [ w ])
  in
  let ex = make_execution ~id:1 ~ppo evts in
  let result =
    sync
      (check_assertion (ub_assertion Allow) [ ex ] structure ~exhaustive:false)
  in
    assert_instances_some "allow(ub) no-UB: instances is Some" result;
    Alcotest.(check int)
      "allow(ub) no-UB: 0 instances" 0
      (List.length (instances_of result));
    Alcotest.(check bool) "allow(ub) no-UB: valid=false" false result.valid

(* ================================================================== *)
(*  Bug 2 – forbid (ub): early return must not bypass process_executions *)
(* ================================================================== *)

(** Primary regression test: assertion_instances must not be None when
    executions are present. Before the fix, [handle_no_executions] returned
    [empty_result] (instances=None) for every non-exhaustive Forbid run. *)
let test_forbid_ub_instances_not_none () =
  let structure, ex = make_uaf_fixture () in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) [ ex ] structure ~exhaustive:false)
  in
    match result.assertion_instances with
    | None ->
        Alcotest.fail
          "forbid(ub) regression: assertion_instances is None (early-return \
           bypass bug)"
    | Some _ -> ()

(** For each exec count: instances must be Some and non-empty. *)
let test_forbid_ub_instances_nonempty n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) execs structure ~exhaustive:false)
  in
    assert_instances_some_nonempty
      (Printf.sprintf "forbid(ub) %d exec(s): non-empty instances" n)
      result

(** Exactly one Contradicted instance per UB execution. *)
let test_forbid_ub_instance_count n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) execs structure ~exhaustive:false)
  in
    Alcotest.(check int)
      (Printf.sprintf "forbid(ub) %d exec(s): instance count" n)
      n
      (List.length (instances_of result))

(** All instances must be Contradicted. *)
let test_forbid_ub_instances_contradicted n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) execs structure ~exhaustive:false)
  in
    assert_all_contradicted
      (Printf.sprintf "forbid(ub) %d exec(s): all Contradicted" n)
      (instances_of result)

(** Contradicted instances carry the correct execution ids. *)
let test_forbid_ub_exec_ids n () =
  let structure, ex0 = make_uaf_fixture () in
  let execs = List.init n (fun i -> { ex0 with id = i + 1 }) in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) execs structure ~exhaustive:false)
  in
  let got =
    List.filter_map
      (function
        | Contradicted { exec_id; _ } -> Some exec_id
        | _ -> None
        )
      (instances_of result)
    |> List.sort compare
  in
  let expected = List.init n (fun i -> i + 1) in
    Alcotest.(check (list int))
      (Printf.sprintf "forbid(ub) %d exec(s): exec_ids" n)
      expected got

(** forbid (ub) is invalid when UB is present (UB occurred but was forbidden).
*)
let test_forbid_ub_invalid_when_ub () =
  let structure, ex = make_uaf_fixture () in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) [ ex ] structure ~exhaustive:false)
  in
    Alcotest.(check bool)
      "forbid(ub) + UB present → valid=false" false result.valid

(** forbid (ub) with no UB: Some [] instances, valid=true. *)
let test_forbid_ub_valid_when_no_ub () =
  let tbl, m, w, ppo, evts = make_clean_events 20 "γ" in
  let structure =
    make_structure tbl ~malloc_events:(USet.of_list [ m ])
      ~write_events:(USet.of_list [ w ])
  in
  let ex = make_execution ~id:1 ~ppo evts in
  let result =
    sync
      (check_assertion (ub_assertion Forbid) [ ex ] structure ~exhaustive:false)
  in
    assert_instances_some "forbid(ub) no-UB: instances is Some" result;
    Alcotest.(check int)
      "forbid(ub) no-UB: 0 instances" 0
      (List.length (instances_of result));
    Alcotest.(check bool) "forbid(ub) no-UB: valid=true" true result.valid

(* ================================================================== *)
(*  Cross-cutting: exhaustive flag must not suppress instances         *)
(*                                                                     *)
(*  The early-return bug was specifically triggered by exhaustive=false *)
(*  for Forbid.  Test all four (outcome × exhaustive) combinations.   *)
(* ================================================================== *)

(** Data provider: (outcome, exhaustive, label). *)
let exhaustive_cases =
  [
    (Allow, false, "allow(ub)  non-exhaustive");
    (Allow, true, "allow(ub)  exhaustive");
    (Forbid, false, "forbid(ub) non-exhaustive");
    (Forbid, true, "forbid(ub) exhaustive");
  ]

let test_instances_regardless_of_exhaustive outcome exhaustive label () =
  let structure, ex = make_uaf_fixture () in
  let result =
    sync (check_assertion (ub_assertion outcome) [ ex ] structure ~exhaustive)
  in
    match result.assertion_instances with
    | None -> Alcotest.fail (label ^ ": assertion_instances is None")
    | Some [] ->
        Alcotest.fail
          (label
          ^ ": assertion_instances is Some [] — UB exec produced no instance"
          )
    | Some _ -> ()

(* ================================================================== *)
(*  Empty execution list: guard must preserve the original behaviour   *)
(*                                                                     *)
(*  The fix adds [if executions = []] around the early-return call.   *)
(*  These tests verify the guard only skips early return for non-empty *)
(*  lists — genuinely empty lists must still behave as before.        *)
(* ================================================================== *)

(** forbid (ub) + empty list + non-exhaustive → valid=true (no UB found). *)
let test_forbid_ub_empty_non_exhaustive () =
  let structure, _ = make_uaf_fixture () in
  let result =
    sync (check_assertion (ub_assertion Forbid) [] structure ~exhaustive:false)
  in
    Alcotest.(check bool)
      "forbid(ub) empty list non-exhaustive: valid=true preserved" true
      result.valid

(** allow (ub) + empty list + non-exhaustive → Some [] instances, valid=false.
*)
let test_allow_ub_empty_non_exhaustive () =
  let structure, _ = make_uaf_fixture () in
  let result =
    sync (check_assertion (ub_assertion Allow) [] structure ~exhaustive:false)
  in
    assert_instances_some "allow(ub) empty list: instances is Some" result;
    Alcotest.(check int)
      "allow(ub) empty list: 0 instances" 0
      (List.length (instances_of result));
    Alcotest.(check bool) "allow(ub) empty list: valid=false" false result.valid

(* ================================================================== *)
(*  Mixed executions: only UB executions produce instances             *)
(*                                                                     *)
(*  Verifies that the [local_ub_reasons <> []] guard in the [None]    *)
(*  branch of process_executions is correctly scoped per-execution:   *)
(*  clean executions must not generate spurious instances.            *)
(* ================================================================== *)

(** allow (ub): one UB exec + one clean exec → exactly 1 Witnessed instance
    belonging to the UB execution. *)
let test_allow_ub_mixed_executions () =
  let structure, uaf_ex = make_uaf_fixture () in
  let uaf_ex = { uaf_ex with id = 1 } in
  (* Add clean events into the shared structure so UBValidation can look them
     up.  Event IDs 20/21 are well clear of the UAF fixture's 1/2/3. *)
  let clean_tbl, m, w, ppo, evts = make_clean_events 20 "δ" in
    Hashtbl.iter (Hashtbl.add structure.events) clean_tbl;
    USet.add structure.malloc_events m |> ignore;
    USet.add structure.write_events w |> ignore;
    let clean_ex = make_execution ~id:2 ~ppo evts in
    let result =
      sync
        (check_assertion (ub_assertion Allow) [ uaf_ex; clean_ex ] structure
           ~exhaustive:false
        )
    in
    let insts = instances_of result in
      Alcotest.(check int)
        "allow(ub) mixed: exactly 1 instance (UB exec only)" 1
        (List.length insts);
      match insts with
      | [ Witnessed { exec_id = 1; _ } ] -> ()
      | [ Witnessed { exec_id; _ } ] ->
          Alcotest.fail
            (Printf.sprintf "allow(ub) mixed: Witnessed has wrong exec_id=%d"
               exec_id
            )
      | _ -> Alcotest.fail "allow(ub) mixed: wrong instance shape"

(** forbid (ub): one UB exec + one clean exec → exactly 1 Contradicted instance
    belonging to the UB execution. *)
let test_forbid_ub_mixed_executions () =
  let structure, uaf_ex = make_uaf_fixture () in
  let uaf_ex = { uaf_ex with id = 1 } in
  let clean_tbl, m, w, ppo, evts = make_clean_events 30 "ε" in
    Hashtbl.iter (Hashtbl.add structure.events) clean_tbl;
    USet.add structure.malloc_events m |> ignore;
    USet.add structure.write_events w |> ignore;
    let clean_ex = make_execution ~id:2 ~ppo evts in
    let result =
      sync
        (check_assertion (ub_assertion Forbid) [ uaf_ex; clean_ex ] structure
           ~exhaustive:false
        )
    in
    let insts = instances_of result in
      Alcotest.(check int)
        "forbid(ub) mixed: exactly 1 instance (UB exec only)" 1
        (List.length insts);
      match insts with
      | [ Contradicted { exec_id = 1; _ } ] -> ()
      | [ Contradicted { exec_id; _ } ] ->
          Alcotest.fail
            (Printf.sprintf
               "forbid(ub) mixed: Contradicted has wrong exec_id=%d" exec_id
            )
      | _ -> Alcotest.fail "forbid(ub) mixed: wrong instance shape"

(* ================================================================== *)
(*  ub field and valid field invariants                                *)
(*                                                                     *)
(*  Ensures the instance-creation fixes don't corrupt the top-level   *)
(*  result fields.                                                     *)
(*                                                                     *)
(*  Data provider: (outcome, has_ub, expected_ub, expected_valid)      *)
(* ================================================================== *)

let ub_validity_cases =
  [
    (Allow, true, true, true, "allow(ub)  + UB    → ub=T valid=T");
    (Allow, false, false, false, "allow(ub)  + no-UB → ub=F valid=F");
    (Forbid, true, true, false, "forbid(ub) + UB    → ub=T valid=F");
    (Forbid, false, false, true, "forbid(ub) + no-UB → ub=F valid=T");
  ]

let test_ub_and_valid_fields outcome has_ub expected_ub expected_valid label ()
    =
  let structure, ex =
    if has_ub then make_uaf_fixture ()
    else begin
      let tbl, m, w, ppo, evts = make_clean_events 40 "ζ" in
      let s =
        make_structure tbl ~malloc_events:(USet.of_list [ m ])
          ~write_events:(USet.of_list [ w ])
      in
        (s, make_execution ~id:1 ~ppo evts)
    end
  in
  let result =
    sync
      (check_assertion (ub_assertion outcome) [ ex ] structure ~exhaustive:false)
  in
    Alcotest.(check bool) (label ^ ": ub") expected_ub result.ub;
    Alcotest.(check bool) (label ^ ": valid") expected_valid result.valid

(* ================================================================== *)
(*  Suite assembly                                                     *)
(* ================================================================== *)

let suite =
  ( "Test_assertion",
    (* Bug 1: allow (ub) — data-driven over exec counts *)
    List.concat_map
      (fun n ->
        [
          Alcotest.test_case
            (Printf.sprintf "allow(ub) %d exec(s): instances non-empty" n)
            `Quick
            (test_allow_ub_instances_nonempty n);
          Alcotest.test_case
            (Printf.sprintf "allow(ub) %d exec(s): instance count" n)
            `Quick
            (test_allow_ub_instance_count n);
          Alcotest.test_case
            (Printf.sprintf "allow(ub) %d exec(s): all Witnessed" n)
            `Quick
            (test_allow_ub_instances_witnessed n);
          Alcotest.test_case
            (Printf.sprintf "allow(ub) %d exec(s): exec_ids match" n)
            `Quick (test_allow_ub_exec_ids n);
        ]
      )
      ub_exec_counts
    @ [
        Alcotest.test_case "allow(ub): valid=true when UB present" `Quick
          test_allow_ub_valid_when_ub;
        Alcotest.test_case "allow(ub): 0 instances and valid=false when no UB"
          `Quick test_allow_ub_no_ub_executions;
      ]
    (* Bug 2: forbid (ub) — primary regression then data-driven *)
    @ [
        Alcotest.test_case
          "forbid(ub) regression: assertion_instances not None with executions \
           present"
          `Quick test_forbid_ub_instances_not_none;
      ]
    @ List.concat_map
        (fun n ->
          [
            Alcotest.test_case
              (Printf.sprintf "forbid(ub) %d exec(s): instances non-empty" n)
              `Quick
              (test_forbid_ub_instances_nonempty n);
            Alcotest.test_case
              (Printf.sprintf "forbid(ub) %d exec(s): instance count" n)
              `Quick
              (test_forbid_ub_instance_count n);
            Alcotest.test_case
              (Printf.sprintf "forbid(ub) %d exec(s): all Contradicted" n)
              `Quick
              (test_forbid_ub_instances_contradicted n);
            Alcotest.test_case
              (Printf.sprintf "forbid(ub) %d exec(s): exec_ids match" n)
              `Quick
              (test_forbid_ub_exec_ids n);
          ]
        )
        ub_exec_counts
    @ [
        Alcotest.test_case "forbid(ub): valid=false when UB present" `Quick
          test_forbid_ub_invalid_when_ub;
        Alcotest.test_case "forbid(ub): 0 instances and valid=true when no UB"
          `Quick test_forbid_ub_valid_when_no_ub;
      ]
    (* Cross-cutting: exhaustive flag *)
    @ List.map
        (fun (outcome, exhaustive, label) ->
          Alcotest.test_case
            (Printf.sprintf "instances present: %s" label)
            `Quick
            (test_instances_regardless_of_exhaustive outcome exhaustive label)
        )
        exhaustive_cases
    (* Empty execution list: guard preserves original behaviour *)
    @ [
        Alcotest.test_case
          "forbid(ub) empty list non-exhaustive: valid=true preserved" `Quick
          test_forbid_ub_empty_non_exhaustive;
        Alcotest.test_case
          "allow(ub) empty list non-exhaustive: Some [] instances, valid=false"
          `Quick test_allow_ub_empty_non_exhaustive;
      ]
    (* Mixed UB + clean executions *)
    @ [
        Alcotest.test_case
          "allow(ub) mixed: only UB exec produces Witnessed instance" `Quick
          test_allow_ub_mixed_executions;
        Alcotest.test_case
          "forbid(ub) mixed: only UB exec produces Contradicted instance" `Quick
          test_forbid_ub_mixed_executions;
      ]
    (* ub and valid field invariants *)
    @ List.map
        (fun (outcome, has_ub, exp_ub, exp_valid, label) ->
          Alcotest.test_case
            (Printf.sprintf "ub+valid invariant: %s" label)
            `Quick
            (test_ub_and_valid_fields outcome has_ub exp_ub exp_valid label)
        )
        ub_validity_cases
  )
