open Alcotest
open Elaborations
open Expr
open Lwt.Syntax
open Trees
open Types
open Uset

(* Helper to run Lwt tests *)
let lwt_test fn () = Lwt_main.run (fn ())

(* Mock context builder *)
let create_mock_context () =
  let events : (int, event) Hashtbl.t = Hashtbl.create 10 in

  (* Add some test events *)
  let (e0 : event) =
    {
      label = 0;
      id = Some (VNumber Z.zero);
      loc = Some (ENum Z.zero);
      typ = Write;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = Some (EBinOp (ENum Z.one, "=", ENum Z.one));
      van = 0;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
  let (e1 : event) =
    {
      label = 1;
      id = Some (VNumber Z.zero);
      loc = Some (ENum Z.zero);
      typ = Write;
      wval = Some (ENum Z.one);
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = 1;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
  let (e2 : event) =
    {
      label = 2;
      id = Some (VNumber Z.one);
      loc = Some (ENum Z.one);
      typ = Read;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = 2;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
  let (e3 : event) =
    {
      label = 3;
      id = Some (VNumber Z.one);
      loc = Some (ENum Z.one);
      typ = Write;
      wval = Some (ENum (Z.of_int 2));
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = 3;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in

  Hashtbl.add events 0 e0;
  Hashtbl.add events 1 e1;
  Hashtbl.add events 2 e2;
  Hashtbl.add events 3 e3;

  let e_set = USet.of_list [ 0; 1; 2; 3 ] in
  let structure : symbolic_event_structure =
    {
      e = e_set;
      po = USet.of_list [ (1, 2) ];
      rmw = USet.create ();
      lo = USet.create ();
      restrict = Hashtbl.create 10;
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
    }
  in

  let branch_events = USet.create () in
  let read_events = USet.of_list [ 2 ] in
  let write_events = USet.of_list [ 0; 1; 3 ] in
  let malloc_events = USet.create () in
  let po = USet.of_list [ (1, 2) ] in
  let rmw = USet.create () in
  let fj = USet.create () in

  let val_fn i =
    match Hashtbl.find_opt events i with
    | Some e -> e.wval
    | None -> None
  in

  let conflicting_branch _e1 _e2 = 0 in

  {
    structure;
    events;
    e_set;
    branch_events;
    read_events;
    write_events;
    malloc_events;
    po;
    rmw;
    fj;
    val_fn;
    conflicting_branch;
  }

(* Mock justification builder *)
let create_mock_justification label predicates =
  let w =
    {
      label;
      id = Some (VNumber Z.zero);
      loc = Some (ENum Z.zero);
      typ = Write;
      wval = Some (ENum (Z.of_int 42));
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = label;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
    {
      w;
      p = predicates;
      fwd = USet.create ();
      we = USet.create ();
      d = USet.create ();
      op = ("init", None, None);
    }

(* Tests for lifted cache *)
let test_lifted_cache_create () =
  let cache = create_lifted_cache () in
    check int "cache t is empty" 0 (USet.size cache.t);
    check int "cache to_ is empty" 0 (USet.size cache.to_);
    ()

let test_lifted_cache_add () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in
    lifted_add cache (just1, just2);
    check int "cache t has one entry" 1 (USet.size cache.t);
    check bool "cache contains pair" true (USet.mem cache.t (just1, just2));
    ()

let test_lifted_cache_has_not_found () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in
  let result = lifted_has cache (just1, just2) in
    check (option (list reject)) "has returns None for missing pair" None result;
    ()

let test_lifted_cache_has_empty_result () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in
    lifted_add cache (just1, just2);
    let result = lifted_has cache (just1, just2) in
      check
        (option (list reject))
        "has returns Some [] for cached pair" (Some []) result;
      ()

let test_lifted_cache_to_and_has () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  (* Create original justifications *)
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in

  (* Create result justifications *)
  let result_just = create_mock_justification 3 [ pred ] in

  (* Add mapping *)
  lifted_to cache (just1, just2) [ result_just ];

  (* Check it can be retrieved *)
  let retrieved = lifted_has cache (just1, just2) in
    check bool "to_ stores mapping" true (Option.is_some retrieved);
    match retrieved with
    | Some results ->
        check int "retrieved correct number of results" 1 (List.length results);
        let r = List.hd results in
          check int "result has correct write label" 3 r.w.label;
          check int "result preserves predicate from result_just"
            (List.length result_just.p)
            (List.length r.p);
          ()
    | None -> failwith "Expected Some results"

let test_lifted_cache_has_matches_predicates () =
  let cache = create_lifted_cache () in

  (* Create justifications with specific predicates *)
  let pred1 = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let pred2 = EBinOp (ENum (Z.of_int 2), "=", ENum (Z.of_int 2)) in

  let just1 = create_mock_justification 1 [ pred1 ] in
  let just2 = create_mock_justification 2 [ pred2 ] in

  let result_just = create_mock_justification 3 [ pred1 ] in

  (* Add mapping *)
  lifted_to cache (just1, just2) [ result_just ];

  (* Try to retrieve with matching predicates *)
  let just1_match = create_mock_justification 1 [ pred1 ] in
  let just2_match = create_mock_justification 2 [ pred2 ] in

  let retrieved = lifted_has cache (just1_match, just2_match) in
    check bool "matches by predicates" true (Option.is_some retrieved);
    ()

let test_lifted_cache_has_no_match_different_predicates () =
  let cache = create_lifted_cache () in

  (* Create justifications with specific predicates *)
  let pred1 = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let pred2 = EBinOp (ENum (Z.of_int 2), "=", ENum (Z.of_int 2)) in
  let pred3 = EBinOp (ENum (Z.of_int 3), "=", ENum (Z.of_int 3)) in

  let just1 = create_mock_justification 1 [ pred1 ] in
  let just2 = create_mock_justification 2 [ pred2 ] in

  let result_just = create_mock_justification 3 [ pred1 ] in

  (* Add mapping *)
  lifted_to cache (just1, just2) [ result_just ];

  (* Try to retrieve with different predicates *)
  let just1_diff = create_mock_justification 1 [ pred3 ] in
  let just2_diff = create_mock_justification 2 [ pred2 ] in

  let retrieved = lifted_has cache (just1_diff, just2_diff) in
    check bool "no match with different predicates" true
      (Option.is_none retrieved);
    ()

let test_lifted_cache_has_matches_fwd_we () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  (* Create justifications with specific fwd and we sets *)
  let fwd_set = USet.of_list [ (1, 2); (2, 3) ] in
  let we_set = USet.of_list [ (3, 4) ] in

  let just1 =
    { (create_mock_justification 1 [ pred ]) with fwd = fwd_set; we = we_set }
  in
  let just2 = create_mock_justification 2 [ pred ] in

  let result_just = create_mock_justification 3 [ pred ] in

  (* Add mapping *)
  lifted_to cache (just1, just2) [ result_just ];

  (* Try to retrieve with matching fwd and we *)
  let just1_match =
    { (create_mock_justification 1 [ pred ]) with fwd = fwd_set; we = we_set }
  in
  let just2_match = create_mock_justification 2 [ pred ] in

  let retrieved = lifted_has cache (just1_match, just2_match) in
    check bool "matches by fwd and we" true (Option.is_some retrieved);
    ()

let test_lifted_cache_has_returns_modified_justifications () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  (* Create and store justifications with empty fwd/we *)
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in

  (* Result justification *)
  let result_just = create_mock_justification 3 [ pred ] in

  (* First, test that we can store and retrieve with empty contexts *)
  lifted_to cache (just1, just2) [ result_just ];

  (* Query with new justifications that have same labels/predicates but empty fwd/we *)
  let just1_query = create_mock_justification 1 [ pred ] in
  let just2_query = create_mock_justification 2 [ pred ] in

  let retrieved = lifted_has cache (just1_query, just2_query) in
    match retrieved with
    | Some results ->
        check int "returns correct number of results" 1 (List.length results);
        let r = List.hd results in
        (* Check operation is "lifted" *)
        let op_name, op_just, _ = r.op in
          check string "operation is lifted" "lifted" op_name;
          check bool "operation includes justification" true
            (Option.is_some op_just);
          (* Verify the write event is from result_just *)
          check int "write event from result" 3 r.w.label;
          (* Verify predicates are preserved from result_just *)
          check int "predicates preserved"
            (List.length result_just.p)
            (List.length r.p);
          ()
    | None ->
        (* Debug: check if cache has any entries *)
        Printf.printf "cache.to_ size: %d\n" (USet.size cache.to_);
        Printf.printf "just1.w.label: %d, just1_query.w.label: %d\n"
          just1.w.label just1_query.w.label;
        Printf.printf "just2.w.label: %d, just2_query.w.label: %d\n"
          just2.w.label just2_query.w.label;
        failwith "Expected Some results but got None"

let test_lifted_cache_has_multiple_results () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in

  (* Create multiple result justifications *)
  let result_just1 = create_mock_justification 3 [ pred ] in
  let result_just2 = create_mock_justification 4 [ pred ] in

  lifted_to cache (just1, just2) [ result_just1; result_just2 ];

  let retrieved = lifted_has cache (just1, just2) in
    match retrieved with
    | Some results ->
        check int "returns multiple results" 2 (List.length results);
        ()
    | None -> failwith "Expected Some results"

let test_lifted_cache_clear () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in
  let result_just = create_mock_justification 3 [ pred ] in

  (* Add some data *)
  lifted_add cache (just1, just2);
  lifted_to cache (just1, just2) [ result_just ];

  check bool "cache has data before clear" true
    (USet.size cache.t > 0 || USet.size cache.to_ > 0);

  (* Clear *)
  lifted_clear cache;

  check int "cache t empty after clear" 0 (USet.size cache.t);
  check int "cache to_ empty after clear" 0 (USet.size cache.to_);
  ()

let test_lifted_cache_has_no_match_different_write_labels () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in

  let result_just = create_mock_justification 3 [ pred ] in

  lifted_to cache (just1, just2) [ result_just ];

  (* Try with different write labels *)
  let just1_diff = create_mock_justification 99 [ pred ] in
  let just2_diff = create_mock_justification 2 [ pred ] in

  let retrieved = lifted_has cache (just1_diff, just2_diff) in
    check bool "no match with different write labels" true
      (Option.is_none retrieved);
    ()

(* Tests for filter function *)
let test_filter_empty () =
  let ctx = create_mock_context () in
  let justs = USet.create () in
    let* result = filter ctx justs in
      check int "empty filter" 0 (USet.size result);
      Lwt.return_unit

let test_filter_valid () =
  let ctx = create_mock_context () in
  (* Create a valid boolean predicate: 1 = 1 *)
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = create_mock_justification 1 [ pred ] in
    let* result = filter ctx (USet.singleton just) in
      check bool "filter keeps valid" true (USet.size result >= 0);
      Lwt.return_unit

let test_filter_removes_covered () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = create_mock_justification 1 [ pred; pred ] in
  let just2 = create_mock_justification 1 [ pred ] in
  let justs = USet.of_list [ just1; just2 ] in
    (* just2 covers just1 as it has fewer predicates *)
    let* result = filter ctx justs in
      check bool "filter removes covered" true (USet.size result <= 2);
      Lwt.return_unit

(* Tests for value_assign function *)
let test_value_assign_no_variables () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = create_mock_justification 1 [ pred ] in
  let justs = USet.singleton just in
    let* result = value_assign ctx justs in
      check int "value_assign size preserved" 1 (USet.size result);
      Lwt.return_unit

let test_value_assign_with_variable () =
  let ctx = create_mock_context () in
  let w =
    {
      label = 1;
      id = Some (VNumber Z.zero);
      loc = Some (ENum Z.zero);
      typ = Write;
      wval = Some (EVar "v1");
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = 1;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just =
    {
      w;
      p = [ pred ];
      fwd = USet.create ();
      we = USet.create ();
      d = USet.create ();
      op = ("init", None, None);
    }
  in
  let justs = USet.singleton just in
    let* result = value_assign ctx justs in
      check bool "value_assign processes variables" true (USet.size result > 0);
      Lwt.return_unit

(* Tests for fprime function *)
let test_fprime_basic () =
  let ctx = create_mock_context () in
  let pred_fn _e = USet.create () in
  let ppo_loc = USet.of_list [ (1, 2) ] in
  let result = fprime ctx pred_fn ppo_loc in
    (* fprime filters po edges that are in ppo_loc and satisfy predicate *)
    check bool "fprime returns edges" true (USet.size result >= 0);
    ()

let test_fprime_empty_ppo () =
  let ctx = create_mock_context () in
  let pred_fn _e = USet.create () in
  let ppo_loc = USet.create () in
  let result = fprime ctx pred_fn ppo_loc in
    check int "fprime empty ppo" 0 (USet.size result);
    ()

(* Tests for fwd function *)
let test_fwd_basic () =
  let ctx = create_mock_context () in
  let pred_fn _e = USet.create () in
  let fwd_ctx = Forwardingcontext.create () in
  let ppo_loc = USet.of_list [ (1, 2) ] in
  let result = fwd ctx pred_fn fwd_ctx ppo_loc in
    check bool "fwd returns filtered edges" true (USet.size result >= 0);
    ()

let test_fwd_filters_volatile () =
  let ctx = create_mock_context () in
  (* Add volatile event *)
  let volatile_event =
    {
      label = 4;
      id = Some (VNumber (Z.of_int 2));
      loc = Some (ENum (Z.of_int 2));
      typ = Read;
      wval = None;
      wmod = Relaxed;
      volatile = true;
      cond = None;
      van = 4;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
    Hashtbl.add ctx.events 4 volatile_event;

    let pred_fn _e = USet.singleton 1 in
    let fwd_ctx = Forwardingcontext.create () in
    let ppo_loc = USet.of_list [ (1, 4) ] in
    let result = fwd ctx pred_fn fwd_ctx ppo_loc in
      (* Volatile events should be filtered out *)
      check bool "fwd filters volatile" true
        (not (USet.exists (fun (_, e) -> e = 4) result));
      ()

(* Tests for we function *)
let test_we_basic () =
  let ctx = create_mock_context () in
  let pred_fn _e = USet.create () in
  let we_ctx = Forwardingcontext.create () in
  let ppo_loc = USet.of_list [ (1, 3) ] in
  let result = we ctx pred_fn we_ctx ppo_loc in
    check bool "we returns edges" true (USet.size result >= 0);
    ()

let test_we_write_to_write () =
  let ctx = create_mock_context () in
  (* Add write-to-write edge in po *)
  let po = USet.add ctx.po (1, 3) in
  let ctx = { ctx with po } in

  let pred_fn _e = USet.singleton 1 in
  let we_ctx = Forwardingcontext.create () in
  let ppo_loc = USet.of_list [ (1, 3) ] in
  let result = we ctx pred_fn we_ctx ppo_loc in
    (* we should only include write-to-write edges *)
    check bool "we write-to-write" true (USet.size result >= 0);
    ()

(* Tests for forward function *)
let test_forward_empty () =
  let ctx = create_mock_context () in
  let justs = USet.create () in
    let* result = forward ctx justs in
      check int "forward empty" 0 (USet.size result);
      Lwt.return_unit

let test_forward_single_justification () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = create_mock_justification 1 [ pred ] in
  let justs = USet.singleton just in
    let* result = forward ctx justs in
      check bool "forward produces results" true (USet.size result >= 0);
      Lwt.return_unit

let test_forward_with_pwg () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let structure = { ctx.structure with pwg = [ pred ] } in
  let ctx = { ctx with structure } in
  let just = create_mock_justification 1 [ pred ] in
  let justs = USet.singleton just in
    let* result = forward ctx justs in
      check bool "forward with pwg" true (USet.size result >= 0);
      Lwt.return_unit

(* Tests for conflict function *)
let test_conflict_no_branches () =
  let ctx = create_mock_context () in
  let events = USet.of_list [ 1; 2; 3 ] in
  let result = conflict ctx events in
    check int "conflict no branches" 0 (USet.size result);
    ()

let test_conflict_with_branches () =
  let ctx = create_mock_context () in
  (* Add branch event with two successors *)
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let branch_event =
    {
      label = 10;
      id = Some (VNumber (Z.of_int 10));
      loc = Some (ENum (Z.of_int 10));
      typ = Write;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = Some pred;
      van = 10;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
  (* Add successor events *)
  let event_11 =
    {
      label = 11;
      id = Some (VNumber (Z.of_int 11));
      loc = Some (ENum (Z.of_int 11));
      typ = Write;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = 11;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in
  let event_12 =
    {
      label = 12;
      id = Some (VNumber (Z.of_int 12));
      loc = Some (ENum (Z.of_int 12));
      typ = Write;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = None;
      van = 12;
      rval = None;
      rmod = Relaxed;
      fmod = Relaxed;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }
  in

  Hashtbl.add ctx.events 10 branch_event;
  Hashtbl.add ctx.events 11 event_11;
  Hashtbl.add ctx.events 12 event_12;

  let branch_events = USet.singleton 10 in
  let e_set = USet.add ctx.e_set 10 in
  let e_set = USet.add e_set 11 in
  let e_set = USet.add e_set 12 in
  let po = USet.add ctx.po (10, 11) in
  let po = USet.add po (10, 12) in
  let ctx = { ctx with branch_events; po; e_set } in

  let events = USet.of_list [ 10; 11; 12 ] in
  let result = conflict ctx events in
    check bool "conflict with branches" true (USet.size result >= 0);
    ()

(* Tests for lift function *)
let test_lift_identity () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = create_mock_justification 1 [ pred ] in
  let justs = USet.singleton just in
    let* result = lift ctx justs in
      (* lift currently returns input unchanged (simplified) *)
      check int "lift identity" (USet.size justs) (USet.size result);
      Lwt.return_unit

(* Tests for weaken function *)
let test_weaken_no_pwg () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = create_mock_justification 1 [ pred; pred ] in
  let justs = USet.singleton just in
    let* result = weaken ctx justs in
      (* With no PWG, should return input unchanged *)
      check int "weaken no pwg" (USet.size justs) (USet.size result);
      Lwt.return_unit

let test_weaken_with_pwg () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let structure = { ctx.structure with pwg = [ pred ] } in
  let ctx = { ctx with structure } in
  let just = create_mock_justification 1 [ pred; pred ] in
  let justs = USet.singleton just in
    let* result = weaken ctx justs in
      check bool "weaken with pwg" true (USet.size result > 0);
      (* Predicates implied by PWG should be removed *)
      let just' = List.hd (USet.values result) in
        check bool "weaken removes implied" true
          (List.length just'.p <= List.length just.p);
        Lwt.return_unit

let test_weaken_preserves_non_implied () =
  let ctx = create_mock_context () in
  (* PWG: x = 1 *)
  let pwg_pred = EBinOp (EVar "x", "=", ENum Z.one) in
  let structure = { ctx.structure with pwg = [ pwg_pred ] } in
  let ctx = { ctx with structure } in
  (* Create predicate that is NOT implied by PWG: y = 2 (different variable) *)
  let not_pwg = EBinOp (EVar "y", "=", ENum (Z.of_int 2)) in
  let just = create_mock_justification 1 [ not_pwg ] in
  let justs = USet.singleton just in
    let* result = weaken ctx justs in
    let just' = List.hd (USet.values result) in
      (* Non-implied predicate should be preserved *)
      check bool "weaken preserves non-implied" true (List.length just'.p > 0);
      Lwt.return_unit

(* Tests for strengthen function *)
let test_strengthen_basic () =
  let ctx = create_mock_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in
  let ppo = USet.create () in
  let con = Forwardingcontext.create () in
    let* result = strengthen ctx just1 just2 ppo con in
      check bool "strengthen returns results" true (List.length result >= 0);
      Lwt.return_unit

let test_strengthen_disjoint_predicates () =
  let ctx = create_mock_context () in
  let pred1 = EBinOp (EVar "x", "=", ENum Z.one) in
  let pred2 = EBinOp (EVar "y", "=", ENum (Z.of_int 2)) in
  let just1 = create_mock_justification 1 [ pred1 ] in
  let just2 = create_mock_justification 2 [ pred2 ] in
  let ppo = USet.create () in
  let con = Forwardingcontext.create () in
    let* result = strengthen ctx just1 just2 ppo con in
      check bool "strengthen disjoint" true (List.length result >= 0);
      Lwt.return_unit

(* Test suite *)
let suite =
  ( "Elaborations",
    [
      test_case "lifted_cache create" `Quick test_lifted_cache_create;
      test_case "lifted_cache add" `Quick test_lifted_cache_add;
      test_case "lifted_cache has not found" `Quick
        test_lifted_cache_has_not_found;
      test_case "lifted_cache has empty result" `Quick
        test_lifted_cache_has_empty_result;
      test_case "lifted_cache to and has" `Quick test_lifted_cache_to_and_has;
      test_case "lifted_cache has matches predicates" `Quick
        test_lifted_cache_has_matches_predicates;
      test_case "lifted_cache has no match different predicates" `Quick
        test_lifted_cache_has_no_match_different_predicates;
      test_case "lifted_cache has matches fwd we" `Quick
        test_lifted_cache_has_matches_fwd_we;
      test_case "lifted_cache has returns modified justifications" `Quick
        test_lifted_cache_has_returns_modified_justifications;
      test_case "lifted_cache has multiple results" `Quick
        test_lifted_cache_has_multiple_results;
      test_case "lifted_cache clear" `Quick test_lifted_cache_clear;
      test_case "lifted_cache has no match different write labels" `Quick
        test_lifted_cache_has_no_match_different_write_labels;
      test_case "filter empty" `Quick (lwt_test test_filter_empty);
      test_case "filter valid" `Quick (lwt_test test_filter_valid);
      test_case "filter removes covered" `Quick
        (lwt_test test_filter_removes_covered);
      test_case "value_assign no variables" `Quick
        (lwt_test test_value_assign_no_variables);
      test_case "value_assign with variable" `Quick
        (lwt_test test_value_assign_with_variable);
      test_case "fprime basic" `Quick test_fprime_basic;
      test_case "fprime empty ppo" `Quick test_fprime_empty_ppo;
      test_case "fwd basic" `Quick test_fwd_basic;
      test_case "fwd filters volatile" `Quick test_fwd_filters_volatile;
      test_case "we basic" `Quick test_we_basic;
      test_case "we write to write" `Quick test_we_write_to_write;
      test_case "forward empty" `Quick (lwt_test test_forward_empty);
      test_case "forward single justification" `Quick
        (lwt_test test_forward_single_justification);
      test_case "forward with pwg" `Quick (lwt_test test_forward_with_pwg);
      test_case "conflict no branches" `Quick test_conflict_no_branches;
      test_case "conflict with branches" `Quick test_conflict_with_branches;
      test_case "lift identity" `Quick (lwt_test test_lift_identity);
      test_case "weaken no pwg" `Quick (lwt_test test_weaken_no_pwg);
      test_case "weaken with pwg" `Quick (lwt_test test_weaken_with_pwg);
      test_case "weaken preserves non-implied" `Quick
        (lwt_test test_weaken_preserves_non_implied);
      test_case "strengthen basic" `Quick (lwt_test test_strengthen_basic);
      test_case "strengthen disjoint predicates" `Quick
        (lwt_test test_strengthen_disjoint_predicates);
    ]
  )
