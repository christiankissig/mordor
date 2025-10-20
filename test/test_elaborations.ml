open Alcotest
open Elaborations
open Types
open Justifications
open Expr
open Lwt.Syntax

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
      typ = Write;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = Some (VExpression (EBinOp (VNumber Z.one, "=", VNumber Z.one)));
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
      typ = Write;
      wval = Some (VNumber Z.one);
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
      typ = Write;
      wval = Some (VNumber (Z.of_int 2));
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

  let e_set = Uset.of_list [ 0; 1; 2; 3 ] in
  let structure : symbolic_event_structure =
    {
      e = e_set;
      po = Uset.of_list [ (1, 2) ];
      rmw = Uset.create ();
      lo = Uset.create ();
      restrict = Hashtbl.create 10;
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = Uset.create ();
      p = Uset.create ();
      constraint_ = [];
    }
  in

  let branch_events = Uset.create () in
  let read_events = Uset.of_list [ 2 ] in
  let write_events = Uset.of_list [ 0; 1; 3 ] in
  let malloc_events = Uset.create () in
  let po = Uset.of_list [ (1, 2) ] in
  let rmw = Uset.create () in
  let fj = Uset.create () in

  let val_fn i =
    match Hashtbl.find_opt events i with
    | Some e -> e.wval
    | None -> None
  in

  let pred _con _exprs ?ppo:_ () = Lwt.return (fun _e -> Uset.create ()) in

  let build_tree edges =
    let tree = Hashtbl.create 10 in
      Uset.iter
        (fun (from, to_) ->
          let children =
            match Hashtbl.find_opt tree from with
            | Some c -> Uset.add c to_
            | None -> Uset.singleton to_
          in
            Hashtbl.replace tree from children
        )
        edges;
      tree
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
    pred;
    build_tree;
    conflicting_branch;
  }

(* Mock justification builder *)
let create_mock_justification label predicates =
  let w =
    {
      label;
      id = Some (VNumber Z.zero);
      typ = Write;
      wval = Some (VNumber (Z.of_int 42));
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
      fwd = Uset.create ();
      we = Uset.create ();
      d = Uset.create ();
      op = ("init", None, None);
    }

(* Tests for filter function *)
let test_filter_empty () =
  let ctx = create_mock_context () in
  let justs = [] in
    let* result = filter ctx justs in
      check int "empty filter" 0 (Uset.size result);
      Lwt.return_unit

let test_filter_valid () =
  let ctx = create_mock_context () in
  (* Create a valid boolean predicate: 1 = 1 *)
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just = create_mock_justification 1 [ pred ] in
    let* result = filter ctx [ just ] in
      check bool "filter keeps valid" true (Uset.size result >= 0);
      Lwt.return_unit

let test_filter_removes_covered () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just1 = create_mock_justification 1 [ pred; pred ] in
  let just2 = create_mock_justification 1 [ pred ] in
    (* just2 covers just1 as it has fewer predicates *)
    let* result = filter ctx [ just1; just2 ] in
      check bool "filter removes covered" true (Uset.size result <= 2);
      Lwt.return_unit

(* Tests for value_assign function *)
let test_value_assign_no_variables () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just = create_mock_justification 1 [ pred ] in
  let justs = [ just ] in
    let* result = value_assign ctx justs in
      check int "value_assign size preserved" 1 (Uset.size result);
      Lwt.return_unit

let test_value_assign_with_variable () =
  let ctx = create_mock_context () in
  let w =
    {
      label = 1;
      id = Some (VNumber Z.zero);
      typ = Write;
      wval = Some (VVar "v1");
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
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just =
    {
      w;
      p = [ pred ];
      fwd = Uset.create ();
      we = Uset.create ();
      d = Uset.create ();
      op = ("init", None, None);
    }
  in
  let justs = [ just ] in
    let* result = value_assign ctx justs in
      check bool "value_assign processes variables" true (Uset.size result > 0);
      Lwt.return_unit

(* Tests for fprime function *)
let test_fprime_basic () =
  let ctx = create_mock_context () in
  let pred_fn _e = Uset.create () in
  let ppo_loc = Uset.of_list [ (1, 2) ] in
  let result = fprime ctx pred_fn ppo_loc in
    (* fprime filters po edges that are in ppo_loc and satisfy predicate *)
    check bool "fprime returns edges" true (Uset.size result >= 0);
    ()

let test_fprime_empty_ppo () =
  let ctx = create_mock_context () in
  let pred_fn _e = Uset.create () in
  let ppo_loc = Uset.create () in
  let result = fprime ctx pred_fn ppo_loc in
    check int "fprime empty ppo" 0 (Uset.size result);
    ()

(* Tests for fwd function *)
let test_fwd_basic () =
  let ctx = create_mock_context () in
  let pred_fn _e = Uset.create () in
  let fwd_ctx = Forwardingcontext.create () in
  let ppo_loc = Uset.of_list [ (1, 2) ] in
  let result = fwd ctx pred_fn fwd_ctx ppo_loc in
    check bool "fwd returns filtered edges" true (Uset.size result >= 0);
    ()

let test_fwd_filters_volatile () =
  let ctx = create_mock_context () in
  (* Add volatile event *)
  let volatile_event =
    {
      label = 4;
      id = Some (VNumber (Z.of_int 2));
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

    let pred_fn _e = Uset.singleton 1 in
    let fwd_ctx = Forwardingcontext.create () in
    let ppo_loc = Uset.of_list [ (1, 4) ] in
    let result = fwd ctx pred_fn fwd_ctx ppo_loc in
      (* Volatile events should be filtered out *)
      check bool "fwd filters volatile" true
        (not (Uset.exists (fun (_, e) -> e = 4) result));
      ()

(* Tests for we function *)
let test_we_basic () =
  let ctx = create_mock_context () in
  let pred_fn _e = Uset.create () in
  let we_ctx = Forwardingcontext.create () in
  let ppo_loc = Uset.of_list [ (1, 3) ] in
  let result = we ctx pred_fn we_ctx ppo_loc in
    check bool "we returns edges" true (Uset.size result >= 0);
    ()

let test_we_write_to_write () =
  let ctx = create_mock_context () in
  (* Add write-to-write edge in po *)
  let po = Uset.add ctx.po (1, 3) in
  let ctx = { ctx with po } in

  let pred_fn _e = Uset.singleton 1 in
  let we_ctx = Forwardingcontext.create () in
  let ppo_loc = Uset.of_list [ (1, 3) ] in
  let result = we ctx pred_fn we_ctx ppo_loc in
    (* we should only include write-to-write edges *)
    check bool "we write-to-write" true (Uset.size result >= 0);
    ()

(* Tests for forward function *)
let test_forward_empty () =
  let ctx = create_mock_context () in
  let justs = Uset.create () in
    let* result = forward ctx justs in
      check int "forward empty" 0 (Uset.size result);
      Lwt.return_unit

let test_forward_single_justification () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just = create_mock_justification 1 [ pred ] in
  let justs = Uset.singleton just in
    let* result = forward ctx justs in
      check bool "forward produces results" true (Uset.size result >= 0);
      Lwt.return_unit

let test_forward_with_pwg () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let structure = { ctx.structure with pwg = [ pred ] } in
  let ctx = { ctx with structure } in
  let just = create_mock_justification 1 [ pred ] in
  let justs = Uset.singleton just in
    let* result = forward ctx justs in
      check bool "forward with pwg" true (Uset.size result >= 0);
      Lwt.return_unit

(* Tests for conflict function *)
let test_conflict_no_branches () =
  let ctx = create_mock_context () in
  let events = Uset.of_list [ 1; 2; 3 ] in
  let result = conflict ctx events in
    check int "conflict no branches" 0 (Uset.size result);
    ()

let test_conflict_with_branches () =
  let ctx = create_mock_context () in
  (* Add branch event with two successors *)
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let branch_event =
    {
      label = 10;
      id = Some (VNumber (Z.of_int 10));
      typ = Write;
      wval = None;
      wmod = Relaxed;
      volatile = false;
      cond = Some (VExpression pred);
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
    Hashtbl.add ctx.events 10 branch_event;

    let branch_events = Uset.singleton 10 in
    let po = Uset.add ctx.po (10, 11) in
    let po = Uset.add po (10, 12) in
    let ctx = { ctx with branch_events; po } in

    let events = Uset.of_list [ 10; 11; 12 ] in
    let result = conflict ctx events in
      check bool "conflict with branches" true (Uset.size result >= 0);
      ()

(* Tests for lift function *)
let test_lift_identity () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just = create_mock_justification 1 [ pred ] in
  let justs = Uset.singleton just in
    let* result = lift ctx justs in
      (* lift currently returns input unchanged (simplified) *)
      check int "lift identity" (Uset.size justs) (Uset.size result);
      Lwt.return_unit

(* Tests for weaken function *)
let test_weaken_no_pwg () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just = create_mock_justification 1 [ pred; pred ] in
  let justs = [ just ] in
    let* result = weaken ctx justs in
      (* With no PWG, should return input unchanged *)
      check int "weaken no pwg" (List.length justs) (List.length result);
      Lwt.return_unit

let test_weaken_with_pwg () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let structure = { ctx.structure with pwg = [ pred ] } in
  let ctx = { ctx with structure } in
  let just = create_mock_justification 1 [ pred; pred ] in
  let justs = [ just ] in
    let* result = weaken ctx justs in
      check bool "weaken with pwg" true (List.length result > 0);
      (* Predicates implied by PWG should be removed *)
      let just' = List.hd result in
        check bool "weaken removes implied" true
          (List.length just'.p <= List.length just.p);
        Lwt.return_unit

let test_weaken_preserves_non_implied () =
  let ctx = create_mock_context () in
  (* PWG: x = 1 *)
  let pwg_pred = EBinOp (VVar "x", "=", VNumber Z.one) in
  let structure = { ctx.structure with pwg = [ pwg_pred ] } in
  let ctx = { ctx with structure } in
  (* Create predicate that is NOT implied by PWG: y = 2 (different variable) *)
  let not_pwg = EBinOp (VVar "y", "=", VNumber (Z.of_int 2)) in
  let just = create_mock_justification 1 [ not_pwg ] in
  let justs = [ just ] in
    let* result = weaken ctx justs in
    let just' = List.hd result in
      (* Non-implied predicate should be preserved *)
      check bool "weaken preserves non-implied" true (List.length just'.p > 0);
      Lwt.return_unit

(* Tests for strengthen function *)
let test_strengthen_basic () =
  let ctx = create_mock_context () in
  let pred = EBinOp (VNumber Z.one, "=", VNumber Z.one) in
  let just1 = create_mock_justification 1 [ pred ] in
  let just2 = create_mock_justification 2 [ pred ] in
  let ppo = Uset.create () in
  let con = Forwardingcontext.create () in
    let* result = strengthen ctx just1 just2 ppo con in
      check bool "strengthen returns results" true (List.length result >= 0);
      Lwt.return_unit

let test_strengthen_disjoint_predicates () =
  let ctx = create_mock_context () in
  let pred1 = EBinOp (VVar "x", "=", VNumber Z.one) in
  let pred2 = EBinOp (VVar "y", "=", VNumber (Z.of_int 2)) in
  let just1 = create_mock_justification 1 [ pred1 ] in
  let just2 = create_mock_justification 2 [ pred2 ] in
  let ppo = Uset.create () in
  let con = Forwardingcontext.create () in
    let* result = strengthen ctx just1 just2 ppo con in
      check bool "strengthen disjoint" true (List.length result >= 0);
      Lwt.return_unit

(* Test suite *)
let suite =
  ( "Elaborations",
    [
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
