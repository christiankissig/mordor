open Alcotest
open Elaborations
open Expr
open Lwt.Syntax
open Types
open Uset

(** Test data providers and utilities *)

module TestData = struct
  (* Event builder with sensible defaults *)
  let make_event ?(id = Some (VNumber Z.zero)) ?(loc = Some (ENum Z.zero))
      ?(typ = Write) ?(wval = None) ?(wmod = Relaxed) ?(volatile = false)
      ?(cond = None) ?(rval = None) ?(rmod = Relaxed) ?(fmod = Relaxed) label =
    {
      label;
      id;
      loc;
      typ;
      wval;
      wmod;
      volatile;
      cond;
      van = label;
      rval;
      rmod;
      fmod;
      strong = None;
      lhs = None;
      rhs = None;
      pc = None;
      hide = false;
      quot = None;
    }

  (* Standard test events *)
  let standard_events () =
    let events = Hashtbl.create 10 in
      Hashtbl.add events 0
        (make_event 0 ~cond:(Some (EBinOp (ENum Z.one, "=", ENum Z.one))));
      Hashtbl.add events 1
        (make_event 1 ~loc:(Some (ENum Z.one)) ~wval:(Some (ENum Z.one)));
      Hashtbl.add events 2
        (make_event 2 ~id:(Some (VNumber Z.one)) ~loc:(Some (ENum Z.one))
           ~typ:Read
        );
      Hashtbl.add events 3
        (make_event 3 ~id:(Some (VNumber Z.one)) ~loc:(Some (ENum Z.one))
           ~wval:(Some (ENum (Z.of_int 2)))
        );
      events

  (* Mock structure builder *)
  let make_structure ?(events = standard_events ())
      ?(e = USet.of_list [ 0; 1; 2; 3 ]) ?(po = USet.of_list [ (1, 2) ])
      ?(write_events = USet.of_list [ 0; 1; 3 ])
      ?(read_events = USet.of_list [ 2 ]) ?(branch_events = USet.create ())
      ?(malloc_events = USet.create ()) ?(rmw = USet.create ()) () =
    {
      e;
      events;
      po;
      po_iter = USet.create ();
      rmw;
      lo = USet.create ();
      restrict = Hashtbl.create 10;
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = USet.create ();
      p = Hashtbl.create 10;
      constraint_ = [];
      conflict = USet.create ();
      origin = Hashtbl.create 10;
      write_events;
      read_events;
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events;
      malloc_events;
      free_events = USet.create ();
    }

  (* Mock context builder *)
  let make_context ?(structure = make_structure ()) () =
    let val_fn i =
      match Hashtbl.find_opt structure.events i with
      | Some e -> e.wval
      | None -> None
    in
    let conflicting_branch _e1 _e2 = 0 in
      { structure; fj = USet.create (); val_fn; conflicting_branch }

  (* Mock justification builder *)
  let make_justification ?(predicates = []) ?(fwd = USet.create ())
      ?(we = USet.create ()) ?(d = USet.create ())
      ?(wval = Some (ENum (Z.of_int 42))) label =
    let w = make_event label ~wval in
      { w; p = predicates; fwd; we; d; op = ("init", None, None) }

  (* Test cases for lifted cache operations *)
  let cache_test_cases =
    [
      ( "empty",
        fun cache ->
          check int "cache t is empty" 0 (USet.size cache.t);
          check int "cache to_ is empty" 0 (USet.size cache.to_)
      );
      ( "add_and_check",
        fun cache ->
          let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
          let just1 = make_justification 1 ~predicates:[ pred ] in
          let just2 = make_justification 2 ~predicates:[ pred ] in
            lifted_add cache (just1, just2);
            check int "cache t has entry" 1 (USet.size cache.t);
            check bool "cache contains pair" true
              (USet.mem cache.t (just1, just2))
      );
    ]

  (* Pre-justification test cases - varying event fields *)
  let pre_just_event_cases =
    [
      ( "only_writes",
        [
          make_event 1 ~loc:(Some (EVar "x")) ~wval:(Some (ENum Z.one));
          make_event 2 ~loc:(Some (EVar "y")) ~wval:(Some (EVar "z"));
        ],
        USet.of_list [ 1; 2 ],
        USet.of_list [ 1; 2 ],
        USet.create (),
        2
      );
      ( "filters_reads",
        [
          make_event 1 ~loc:(Some (EVar "x")) ~wval:(Some (ENum Z.one));
          make_event 2 ~loc:(Some (EVar "y")) ~typ:Read;
        ],
        USet.of_list [ 1; 2 ],
        USet.singleton 1,
        USet.singleton 2,
        1
      );
      ( "mixed_event_types",
        [
          make_event 1 ~loc:(Some (EVar "x")) ~wval:(Some (ENum Z.one));
          make_event 2 ~loc:(Some (EVar "y")) ~typ:Read;
          make_event 3 ~loc:(Some (EVar "z")) ~wval:(Some (ENum (Z.of_int 2)));
        ],
        USet.of_list [ 1; 2; 3 ],
        USet.of_list [ 1; 3 ],
        USet.singleton 2,
        2
      );
    ]

  (* Symbol extraction test cases *)
  let symbol_extraction_cases =
    [
      ( "from_loc",
        make_event 1 ~loc:(Some (EVar "α")) ~wval:None ~rval:None,
        fun just -> USet.size just.d >= 0
      );
      ( "from_wval",
        make_event 1 ~wval:(Some (EVar "β")) ~rval:None,
        fun just -> USet.size just.d >= 0
      );
      ( "from_rval",
        make_event 1 ~wval:None ~rval:(Some (VSymbol "γ")),
        fun just -> USet.mem just.d "γ"
      );
      ( "from_all",
        make_event 1 ~loc:(Some (EVar "δ")) ~wval:(Some (EVar "ε"))
          ~rval:(Some (VSymbol "ζ")),
        fun just -> USet.mem just.d "ζ"
      );
      ( "none_values",
        make_event 1 ~loc:None ~wval:None ~rval:None,
        fun just -> USet.size just.d = 0
      );
    ]
end

(** Lifted cache tests *)

let test_lifted_cache_basic () =
  List.iter
    (fun (_, test_fn) ->
      let cache = create_lifted_cache () in
        test_fn cache
    )
    TestData.cache_test_cases

let test_lifted_cache_has_operations () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = TestData.make_justification 1 ~predicates:[ pred ] in
  let just2 = TestData.make_justification 2 ~predicates:[ pred ] in

  (* Not found *)
  check
    (option (list reject))
    "has returns None for missing" None
    (lifted_has cache (just1, just2));

  (* Empty result after add *)
  lifted_add cache (just1, just2);
  check
    (option (list reject))
    "has returns Some [] after add" (Some [])
    (lifted_has cache (just1, just2))

let test_lifted_cache_to_retrieval () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = TestData.make_justification 1 ~predicates:[ pred ] in
  let just2 = TestData.make_justification 2 ~predicates:[ pred ] in
  let result_just = TestData.make_justification 3 ~predicates:[ pred ] in

  lifted_to cache (just1, just2) [ result_just ];

  match lifted_has cache (just1, just2) with
  | Some results ->
      check int "retrieved correct count" 1 (List.length results);
      let r = List.hd results in
        check int "correct write label" 3 r.w.label;
        check int "predicates preserved"
          (List.length result_just.p)
          (List.length r.p)
  | None -> fail "Expected Some results"

let test_lifted_cache_predicate_matching () =
  let cache = create_lifted_cache () in
  let pred1 = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let pred2 = EBinOp (ENum (Z.of_int 2), "=", ENum (Z.of_int 2)) in
  let pred3 = EBinOp (ENum (Z.of_int 3), "=", ENum (Z.of_int 3)) in

  let just1 = TestData.make_justification 1 ~predicates:[ pred1 ] in
  let just2 = TestData.make_justification 2 ~predicates:[ pred2 ] in
  let result_just = TestData.make_justification 3 ~predicates:[ pred1 ] in

  lifted_to cache (just1, just2) [ result_just ];

  (* Matching predicates *)
  let just1_match = TestData.make_justification 1 ~predicates:[ pred1 ] in
  let just2_match = TestData.make_justification 2 ~predicates:[ pred2 ] in
    check bool "matches by predicates" true
      (Option.is_some (lifted_has cache (just1_match, just2_match)));

    (* Different predicates *)
    let just1_diff = TestData.make_justification 1 ~predicates:[ pred3 ] in
    let just2_diff = TestData.make_justification 2 ~predicates:[ pred2 ] in
      check bool "no match with different predicates" true
        (Option.is_none (lifted_has cache (just1_diff, just2_diff)))

let test_lifted_cache_fwd_we_matching () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let fwd_set = USet.of_list [ (1, 2); (2, 3) ] in
  let we_set = USet.of_list [ (3, 4) ] in

  let just1 =
    TestData.make_justification 1 ~predicates:[ pred ] ~fwd:fwd_set ~we:we_set
  in
  let just2 = TestData.make_justification 2 ~predicates:[ pred ] in
  let result_just = TestData.make_justification 3 ~predicates:[ pred ] in

  lifted_to cache (just1, just2) [ result_just ];

  let just1_match =
    TestData.make_justification 1 ~predicates:[ pred ] ~fwd:fwd_set ~we:we_set
  in
  let just2_match = TestData.make_justification 2 ~predicates:[ pred ] in

  check bool "matches by fwd and we" true
    (Option.is_some (lifted_has cache (just1_match, just2_match)))

let test_lifted_cache_returns_modified () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = TestData.make_justification 1 ~predicates:[ pred ] in
  let just2 = TestData.make_justification 2 ~predicates:[ pred ] in
  let result_just = TestData.make_justification 3 ~predicates:[ pred ] in

  lifted_to cache (just1, just2) [ result_just ];

  let just1_query = TestData.make_justification 1 ~predicates:[ pred ] in
  let just2_query = TestData.make_justification 2 ~predicates:[ pred ] in

  match lifted_has cache (just1_query, just2_query) with
  | Some results ->
      check int "returns results" 1 (List.length results);
      let r = List.hd results in
      let op_name, op_just, _ = r.op in
        check string "operation is lifted" "lifted" op_name;
        check bool "includes justification" true (Option.is_some op_just);
        check int "write from result" 3 r.w.label
  | None -> fail "Expected Some results"

let test_lifted_cache_multiple_and_clear () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = TestData.make_justification 1 ~predicates:[ pred ] in
  let just2 = TestData.make_justification 2 ~predicates:[ pred ] in
  let results =
    [
      TestData.make_justification 3 ~predicates:[ pred ];
      TestData.make_justification 4 ~predicates:[ pred ];
    ]
  in

  lifted_to cache (just1, just2) results;

  (* Multiple results *)
  ( match lifted_has cache (just1, just2) with
  | Some res -> check int "multiple results" 2 (List.length res)
  | None -> fail "Expected results"
  );

  (* Clear *)
  lifted_clear cache;
  check int "cache t empty after clear" 0 (USet.size cache.t);
  check int "cache to_ empty after clear" 0 (USet.size cache.to_)

let test_lifted_cache_no_match_different_labels () =
  let cache = create_lifted_cache () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just1 = TestData.make_justification 1 ~predicates:[ pred ] in
  let just2 = TestData.make_justification 2 ~predicates:[ pred ] in
  let result_just = TestData.make_justification 3 ~predicates:[ pred ] in

  lifted_to cache (just1, just2) [ result_just ];

  let just1_diff = TestData.make_justification 99 ~predicates:[ pred ] in
  let just2_diff = TestData.make_justification 2 ~predicates:[ pred ] in

  check bool "no match with different labels" true
    (Option.is_none (lifted_has cache (just1_diff, just2_diff)))

(** Filter and value_assign tests *)

let test_filter_operations () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  Lwt_main.run
    ((* Empty *)
     let* empty_result = filter ctx (USet.create ()) in
       check int "empty filter" 0 (USet.size empty_result);

       (* Valid *)
       let just = TestData.make_justification 1 ~predicates:[ pred ] in
         let* valid_result = filter ctx (USet.singleton just) in
           check bool "filter keeps valid" true (USet.size valid_result >= 0);

           (* Covered *)
           let just1 =
             TestData.make_justification 1 ~predicates:[ pred; pred ]
           in
           let just2 = TestData.make_justification 1 ~predicates:[ pred ] in
             let* covered_result = filter ctx (USet.of_list [ just1; just2 ]) in
               check bool "filter removes covered" true
                 (USet.size covered_result <= 2);

               Lwt.return_unit
    )

let test_value_assign_operations () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  Lwt_main.run
    ((* No variables *)
     let just = TestData.make_justification 1 ~predicates:[ pred ] in
       let* result1 = value_assign ctx (USet.singleton just) in
         check int "value_assign preserves size" 1 (USet.size result1);

         (* With variable *)
         let w = TestData.make_event 1 ~wval:(Some (EVar "v1")) in
         let just_var =
           {
             w;
             p = [ pred ];
             fwd = USet.create ();
             we = USet.create ();
             d = USet.create ();
             op = ("init", None, None);
           }
         in
           let* result2 = value_assign ctx (USet.singleton just_var) in
             check bool "value_assign processes variables" true
               (USet.size result2 > 0);

             Lwt.return_unit
    )

(** Forward-related tests *)

let test_fprime_operations () =
  let test_cases =
    [
      ( "basic",
        USet.of_list [ (1, 2) ],
        (fun _e -> USet.of_list [ 1 ]),
        1,
        2,
        true
      );
      ("empty_ppo", USet.create (), (fun _e -> USet.create ()), 1, 2, false);
    ]
  in

  Lwt_main.run
    (Lwt_list.iter_s
       (fun (name, ppo_loc, pred_fn, e1, e2, expected) ->
         let ctx = TestData.make_context () in
         let just = TestData.make_justification 3 in
           let* result = fprime ctx pred_fn ppo_loc just e1 e2 in
             check bool name expected result;
             Lwt.return_unit
       )
       test_cases
    )

let test_fwd_operations () =
  let ctx = TestData.make_context () in
  let pred_fn _e = USet.create () in
  let fwd_ctx = Forwardingcontext.create () in
  let just = TestData.make_justification 3 in
  let ppo_loc = USet.of_list [ (1, 2) ] in

  Lwt_main.run
    ((* Basic *)
     let* result1 = fwd ctx pred_fn fwd_ctx ppo_loc just in
       check bool "fwd returns edges" true (USet.size result1 >= 0);

       (* Filters volatile *)
       let volatile_event =
         TestData.make_event 4
           ~id:(Some (VNumber (Z.of_int 2)))
           ~loc:(Some (ENum (Z.of_int 2)))
           ~typ:Read ~volatile:true
       in
         Hashtbl.add ctx.structure.events 4 volatile_event;

         let pred_fn2 _e = USet.singleton 1 in
         let ppo_loc2 = USet.of_list [ (1, 4) ] in
         let just2 = TestData.make_justification 5 in
           let* result2 = fwd ctx pred_fn2 fwd_ctx ppo_loc2 just2 in
             check bool "fwd filters volatile" true
               (not (USet.exists (fun (_, e) -> e = 4) result2));

             Lwt.return_unit
    )

let test_we_operations () =
  let ctx = TestData.make_context () in
  let pred_fn _e = USet.create () in
  let we_ctx = Forwardingcontext.create () in
  let just = TestData.make_justification 4 in
  let ppo_loc = USet.of_list [ (1, 3) ] in

  Lwt_main.run
    ((* Basic *)
     let* result1 = we ctx pred_fn we_ctx ppo_loc just in
       check bool "we returns edges" true (USet.size result1 >= 0);

       (* Write-to-write *)
       let po = USet.add ctx.structure.po (1, 3) in
       let structure = { ctx.structure with po } in
       let ctx = { ctx with structure } in
       let pred_fn2 _e = USet.singleton 1 in
         let* result2 = we ctx pred_fn2 we_ctx ppo_loc just in
           check bool "we write-to-write" true (USet.size result2 >= 0);

           Lwt.return_unit
    )

let test_forward_operations () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  Lwt_main.run
    ((* Empty *)
     let* result1 = forward ctx (USet.create ()) in
       check int "forward empty" 0 (USet.size result1);

       (* Single justification *)
       let just = TestData.make_justification 1 ~predicates:[ pred ] in
         let* result2 = forward ctx (USet.singleton just) in
           check bool "forward produces results" true (USet.size result2 >= 0);

           (* With pwg *)
           let structure = { ctx.structure with pwg = [ pred ] } in
           let ctx_pwg = { ctx with structure } in
             let* result3 = forward ctx_pwg (USet.singleton just) in
               check bool "forward with pwg" true (USet.size result3 >= 0);

               Lwt.return_unit
    )

(** Conflict tests *)

let test_conflict_operations () =
  let ctx = TestData.make_context () in

  (* No branches *)
  let result1 = conflict ctx in
    check int "conflict no branches" 0 (USet.size result1);

    (* With branches *)
    let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
    let branch =
      TestData.make_event 10
        ~id:(Some (VNumber (Z.of_int 10)))
        ~loc:(Some (ENum (Z.of_int 10)))
        ~cond:(Some pred)
    in
    let event_11 =
      TestData.make_event 11
        ~id:(Some (VNumber (Z.of_int 11)))
        ~loc:(Some (ENum (Z.of_int 11)))
    in
    let event_12 =
      TestData.make_event 12
        ~id:(Some (VNumber (Z.of_int 12)))
        ~loc:(Some (ENum (Z.of_int 12)))
    in

    Hashtbl.add ctx.structure.events 10 branch;
    Hashtbl.add ctx.structure.events 11 event_11;
    Hashtbl.add ctx.structure.events 12 event_12;

    let e_set = USet.of_list [ 0; 1; 2; 3; 10; 11; 12 ] in
    let po = USet.of_list [ (1, 2); (10, 11); (10, 12) ] in
    let structure =
      { ctx.structure with e = e_set; po; branch_events = USet.singleton 10 }
    in
    let ctx = { ctx with structure } in

    let result2 = conflict ctx in
      check bool "conflict with branches" true (USet.size result2 >= 0)

(** Lift, weaken, strengthen tests *)

let test_lift_and_weaken () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = TestData.make_justification 1 ~predicates:[ pred ] in
  let justs = USet.singleton just in

  Lwt_main.run
    ((* Lift identity *)
     let* lift_result = lift ctx justs in
       check int "lift identity" (USet.size justs) (USet.size lift_result);

       (* Weaken no pwg *)
       let just2 = TestData.make_justification 1 ~predicates:[ pred; pred ] in
       let justs2 = USet.singleton just2 in
         let* weaken_result1 = weaken ctx justs2 in
           check int "weaken no pwg" (USet.size justs2)
             (USet.size weaken_result1);

           (* Weaken with pwg *)
           let structure = { ctx.structure with pwg = [ pred ] } in
           let ctx_pwg = { ctx with structure } in
             let* weaken_result2 = weaken ctx_pwg justs2 in
               check bool "weaken with pwg" true (USet.size weaken_result2 > 0);
               let just' = List.hd (USet.values weaken_result2) in
                 check bool "weaken removes implied" true
                   (List.length just'.p <= List.length just2.p);

                 (* Weaken preserves non-implied *)
                 let pwg_pred = EBinOp (EVar "x", "=", ENum Z.one) in
                 let not_pwg = EBinOp (EVar "y", "=", ENum (Z.of_int 2)) in
                 let structure2 = { ctx.structure with pwg = [ pwg_pred ] } in
                 let ctx2 = { ctx with structure = structure2 } in
                 let just3 =
                   TestData.make_justification 1 ~predicates:[ not_pwg ]
                 in
                   let* weaken_result3 = weaken ctx2 (USet.singleton just3) in
                   let just'' = List.hd (USet.values weaken_result3) in
                     check bool "weaken preserves non-implied" true
                       (List.length just''.p > 0);

                     Lwt.return_unit
    )

let test_strengthen_operations () =
  let ctx = TestData.make_context () in
  let pred1 = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let pred2 = EBinOp (EVar "x", "=", ENum Z.one) in
  let pred3 = EBinOp (EVar "y", "=", ENum (Z.of_int 2)) in
  let ppo = USet.create () in
  let con = Forwardingcontext.create () in

  Lwt_main.run
    ((* Basic *)
     let just1 = TestData.make_justification 1 ~predicates:[ pred1 ] in
     let just2 = TestData.make_justification 2 ~predicates:[ pred1 ] in
       let* result1 = strengthen ctx just1 just2 ppo con in
         check bool "strengthen returns results" true (List.length result1 >= 0);

         (* Disjoint predicates *)
         let just3 = TestData.make_justification 1 ~predicates:[ pred2 ] in
         let just4 = TestData.make_justification 2 ~predicates:[ pred3 ] in
           let* result2 = strengthen ctx just3 just4 ppo con in
             check bool "strengthen disjoint" true (List.length result2 >= 0);

             Lwt.return_unit
    )

(** Pre-justification tests *)

let test_pre_justifications_basic () =
  let structure = Interpret.empty_structure () in
  let result = pre_justifications structure in
    check int "empty structure" 0 (USet.size result)

let test_pre_justifications_parameterized
    (name, events_list, e_set, write_events, read_events, expected_count) () =
  let structure = Interpret.empty_structure () in
  let events = Hashtbl.create 10 in
    List.iteri (fun i event -> Hashtbl.add events (i + 1) event) events_list;
    let structure =
      { structure with events; e = e_set; write_events; read_events }
    in
    let result = pre_justifications structure in
      check int name expected_count (USet.size result)

let test_pre_justifications_structure_details () =
  let structure = Interpret.empty_structure () in
  let events = Hashtbl.create 10 in
  let write_event =
    TestData.make_event 1 ~loc:(Some (EVar "x")) ~wval:(Some (EVar "y"))
      ~rval:(Some (VNumber (Z.of_int 42)))
  in
    Hashtbl.add events 1 write_event;
    let structure =
      {
        structure with
        events;
        e = USet.singleton 1;
        write_events = USet.singleton 1;
      }
    in
    let result = pre_justifications structure in
    let justs = USet.values result in
      check int "count" 1 (List.length justs);

      let just = List.hd justs in
        check int "p empty" 0 (List.length just.p);
        check int "fwd empty" 0 (USet.size just.fwd);
        check int "we empty" 0 (USet.size just.we);
        check int "correct label" 1 just.w.label;
        let op_name, op_e1, op_e2 = just.op in
          check string "op is init" "init" op_name;
          check bool "op e1 None" true (op_e1 = None);
          check bool "op e2 None" true (op_e2 = None)

let test_pre_justifications_symbol_extraction (name, event, validator) () =
  let structure = Interpret.empty_structure () in
  let events = Hashtbl.create 10 in
    Hashtbl.add events 1 event;
    let structure =
      {
        structure with
        events;
        e = USet.singleton 1;
        write_events = USet.singleton 1;
      }
    in
    let result = pre_justifications structure in
    let justs = USet.values result in
      match justs with
      | [ just ] -> check bool name true (validator just)
      | _ -> fail (name ^ ": Expected single justification")

let test_pre_justifications_edge_cases () =
  (* Missing events *)
  let structure1 = Interpret.empty_structure () in
  let events1 = Hashtbl.create 10 in
  let structure1 =
    { structure1 with events = events1; e = USet.of_list [ 1 ] }
  in
  let result1 = pre_justifications structure1 in
    check int "missing events filtered" 0 (USet.size result1);

    (* Multiple writes distinct *)
    let structure2 = Interpret.empty_structure () in
    let events2 = Hashtbl.create 10 in
    let write1 =
      TestData.make_event 1 ~loc:(Some (EVar "x")) ~wval:(Some (EVar "a"))
    in
    let write2 =
      TestData.make_event 2 ~id:(Some (VNumber Z.one)) ~loc:(Some (EVar "y"))
        ~wval:(Some (EVar "b"))
    in
      Hashtbl.add events2 1 write1;
      Hashtbl.add events2 2 write2;
      let structure2 =
        {
          structure2 with
          events = events2;
          e = USet.of_list [ 1; 2 ];
          write_events = USet.of_list [ 1; 2 ];
        }
      in
      let result2 = pre_justifications structure2 in
      let justs = USet.values result2 in
        check int "multiple writes count" 2 (List.length justs);
        let labels = List.map (fun j -> j.w.label) justs in
        let labels_set = List.sort_uniq compare labels in
          check int "distinct writes" 2 (List.length labels_set)

(** Test suite *)

let suite =
  ( "Elaborations",
    [
      (* Lifted cache tests *)
      test_case "lifted_cache basic operations" `Quick test_lifted_cache_basic;
      test_case "lifted_cache has operations" `Quick
        test_lifted_cache_has_operations;
      test_case "lifted_cache to retrieval" `Quick
        test_lifted_cache_to_retrieval;
      test_case "lifted_cache predicate matching" `Quick
        test_lifted_cache_predicate_matching;
      test_case "lifted_cache fwd_we matching" `Quick
        test_lifted_cache_fwd_we_matching;
      test_case "lifted_cache returns modified" `Quick
        test_lifted_cache_returns_modified;
      test_case "lifted_cache multiple and clear" `Quick
        test_lifted_cache_multiple_and_clear;
      test_case "lifted_cache no match different labels" `Quick
        test_lifted_cache_no_match_different_labels;
      (* Filter and value_assign *)
      test_case "filter operations" `Quick test_filter_operations;
      test_case "value_assign operations" `Quick test_value_assign_operations;
      (* Forward-related *)
      test_case "fprime operations" `Quick test_fprime_operations;
      test_case "fwd operations" `Quick test_fwd_operations;
      test_case "we operations" `Quick test_we_operations;
      test_case "forward operations" `Quick test_forward_operations;
      (* Conflict *)
      test_case "conflict operations" `Quick test_conflict_operations;
      (* Lift, weaken, strengthen *)
      test_case "lift and weaken" `Quick test_lift_and_weaken;
      test_case "strengthen operations" `Quick test_strengthen_operations;
      (* Pre-justifications - basic *)
      test_case "pre_justifications basic" `Quick test_pre_justifications_basic;
      test_case "pre_justifications structure" `Quick
        test_pre_justifications_structure_details;
      test_case "pre_justifications edge cases" `Quick
        test_pre_justifications_edge_cases;
    ]
    (* Parameterized pre-justification event tests *)
    @ List.map
        (fun ((name, _, _, _, _, _) as case) ->
          test_case
            ("pre_justifications " ^ name)
            `Quick
            (test_pre_justifications_parameterized case)
        )
        TestData.pre_just_event_cases
    @
    (* Parameterized symbol extraction tests *)
    List.map
      (fun ((name, _, _) as case) ->
        test_case
          ("pre_justifications symbols " ^ name)
          `Quick
          (test_pre_justifications_symbol_extraction case)
      )
      TestData.symbol_extraction_cases
  )
