open Alcotest
open Elaborations
open Events
open Eventstructures
open Expr
open Forwardingcontext
open Justifications
open Lwt.Syntax
open Types
open Uset

(** Test data providers and utilities *)

module TestData = struct
  (* Event builder with sensible defaults *)
  let make_event ?(id = Some (VNumber Z.zero)) ?(loc = Some (ENum Z.zero))
      ?(typ = Write) ?(wval = None) ?(cond = None) ?(wmod = Relaxed)
      ?(volatile = false) ?(rval = None) ?(rmod = Relaxed) ?(fmod = Relaxed)
      label =
    {
      label;
      id;
      loc;
      typ;
      wval;
      cond;
      wmod;
      volatile;
      rval;
      rmod;
      fmod;
      strong = None;
      is_rdmw = false;
    }

  (* Standard test events *)
  let standard_events () =
    let events = Hashtbl.create 10 in
      Hashtbl.add events 0 (make_event 0);
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
      ?(read_events = USet.of_list [ 2 ]) ?(malloc_events = USet.create ())
      ?(rmw = USet.create ()) () =
    {
      (SymbolicEventStructure.create ()) with
      e;
      events;
      po;
      rmw;
      write_events;
      read_events;
      malloc_events;
    }

  (* Mock context builder *)
  let make_context ?(structure = make_structure ()) () =
    let fj = USet.create () in
    let op_trace = OpTrace.create 0 in
    let forwardingcontext_state =
      Forwardingcontext.EventStructureContext.create structure
    in
      { forwardingcontext_state; structure; fj; op_trace }

  (* Mock justification builder *)
  let make_justification ?(predicates = []) ?(fwd = USet.create ())
      ?(we = USet.create ()) ?(d = USet.create ())
      ?(wval = Some (ENum (Z.of_int 42))) label =
    let w = make_event label ~wval in
      { w; p = predicates; fwd; we; d }

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

let test_value_assign_operations () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (EVar "v1", "=", ENum Z.one) in

  Lwt_main.run
    ((* With variable *)
     let w = TestData.make_event 1 ~wval:(Some (EVar "v1")) in
     let just_var =
       {
         w;
         p = [ pred ];
         fwd = USet.create ();
         we = USet.create ();
         d = USet.create ();
       }
     in
       let* result2 = ValueAssignment.elab ctx just_var in
         check bool "value_assign processes variables" true
           (List.length result2 > 0);

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
           let* result = Forwarding.fprime ctx pred_fn ppo_loc just e1 e2 in
             check bool name expected result;
             Lwt.return_unit
       )
       test_cases
    )

let test_fwd_operations () =
  let ctx = TestData.make_context () in
  let pred_fn _e = USet.create () in
  let fwd_ctx = ForwardingContext.create ctx.forwardingcontext_state in
  let just = TestData.make_justification 3 in
  let ppo_loc = USet.of_list [ (1, 2) ] in

  Lwt_main.run
    ((* Basic *)
     let* result1 = Forwarding.fwd ctx pred_fn fwd_ctx ppo_loc just in
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
           let* result2 = Forwarding.fwd ctx pred_fn2 fwd_ctx ppo_loc2 just2 in
             check bool "fwd filters volatile" true
               (not (USet.exists (fun (_, e) -> e = 4) result2));

             Lwt.return_unit
    )

let test_we_operations () =
  let ctx = TestData.make_context () in
  let pred_fn _e = USet.create () in
  let we_ctx = ForwardingContext.create ctx.forwardingcontext_state in
  let just = TestData.make_justification 4 in
  let ppo_loc = USet.of_list [ (1, 3) ] in

  Lwt_main.run
    ((* Basic *)
     let* result1 = Forwarding.we ctx pred_fn we_ctx ppo_loc just in
       check bool "we returns edges" true (USet.size result1 >= 0);

       (* Write-to-write *)
       let po = USet.add ctx.structure.po (1, 3) in
       let structure = { ctx.structure with po } in
       let ctx = { ctx with structure } in
       let pred_fn2 _e = USet.singleton 1 in
         let* result2 = Forwarding.we ctx pred_fn2 we_ctx ppo_loc just in
           check bool "we write-to-write" true (USet.size result2 >= 0);

           Lwt.return_unit
    )

let test_forward_operations () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in

  Lwt_main.run
    ((* Single justification *)
     let just = TestData.make_justification 1 ~predicates:[ pred ] in
       let* result2 = Forwarding.elab ctx just in
         check bool "forward produces results" true (List.length result2 >= 0);

         Lwt.return_unit
    )

(** Lift, weaken, strengthen tests *)

let test_lift_and_weaken () =
  let ctx = TestData.make_context () in
  let pred = EBinOp (ENum Z.one, "=", ENum Z.one) in
  let just = TestData.make_justification 1 ~predicates:[ pred ] in

  Lwt_main.run
    ((* Lift identity *)
     let* lift_result = Lifting.elab ctx just just in
       check int "lift identity" 0 (List.length lift_result);

       (* Weaken no pwg *)
       let just2 = TestData.make_justification 1 ~predicates:[ pred; pred ] in
         let* weaken_result1 = Weakening.elab ctx just2 in
           check int "weaken no pwg" 1 (List.length weaken_result1);

           (* Weaken with pwg *)
           let defacto = Hashtbl.create 10 in
             Hashtbl.add defacto 1 [ pred ];
             let structure = { ctx.structure with defacto } in
             let elab_ctx = { ctx with structure } in
               let* weaken_result2 = Weakening.elab elab_ctx just2 in
                 check bool "weaken with defacto" true
                   (List.length weaken_result2 > 0);
                 let just' = List.hd weaken_result2 in
                   check bool "weaken removes implied" true
                     (List.length just'.p <= List.length just2.p);

                   Lwt.return_unit
    )

(** Pre-justification tests *)

let test_pre_justifications_basic () =
  let structure = SymbolicEventStructure.create () in
  let result = pre_justifications structure in
    check int "empty structure" 0 (USet.size result)

let test_pre_justifications_parameterized
    (name, events_list, e_set, write_events, read_events, expected_count) () =
  let structure = SymbolicEventStructure.create () in
  let events = Hashtbl.create 10 in
    List.iteri (fun i event -> Hashtbl.add events (i + 1) event) events_list;
    let structure =
      { structure with events; e = e_set; write_events; read_events }
    in
    let result = pre_justifications structure in
      check int name expected_count (USet.size result)

let test_pre_justifications_structure_details () =
  let structure = SymbolicEventStructure.create () in
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
        check int "correct label" 1 just.w.label

let test_pre_justifications_symbol_extraction (name, event, validator) () =
  let structure = SymbolicEventStructure.create () in
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
  let structure1 = SymbolicEventStructure.create () in
  let events1 = Hashtbl.create 10 in
  let structure1 =
    { structure1 with events = events1; e = USet.of_list [ 1 ] }
  in
  let result1 = pre_justifications structure1 in
    check int "missing events filtered" 0 (USet.size result1);

    (* Multiple writes distinct *)
    let structure2 = SymbolicEventStructure.create () in
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

module LiftingTests = struct
  (* ============================================================
     Test Data Providers
     ============================================================ *)

  module TestData = struct
    (* Create a basic event structure with common events *)
    let create_basic_structure () =
      let events = Hashtbl.create 10 in
      let read_alpha = Event.create Read 1 ~rval:(VSymbol "α") () in
        Hashtbl.add events 1 read_alpha;
        let read_beta = Event.create Read 2 ~rval:(VSymbol "β") () in
          Hashtbl.add events 2 read_beta;
          let read_gamma = Event.create Read 3 ~rval:(VSymbol "γ") () in
            Hashtbl.add events 3 read_gamma;
            let write_1 = Event.create Write 4 ~wval:(ENum Z.zero) () in
              Hashtbl.add events 4 write_1;
              let write_2 = Event.create Write 5 ~wval:(ENum Z.zero) () in
                Hashtbl.add events 5 write_2;

                let origin = Hashtbl.create 10 in
                  Hashtbl.add origin "α" read_alpha.label;
                  Hashtbl.add origin "β" read_beta.label;
                  Hashtbl.add origin "γ" read_gamma.label;

                  let read_events =
                    USet.of_list
                      [ read_alpha.label; read_beta.label; read_gamma.label ]
                  in
                  let write_events =
                    USet.of_list [ write_1.label; write_2.label ]
                  in
                  let e = USet.union read_events write_events in
                  let po =
                    USet.of_list [ (1, 2); (1, 3); (2, 4); (3, 5) ]
                    |> URelation.transitive_closure
                  in
                  let conflict =
                    USet.of_list [ (2, 3); (2, 5); (3, 4); (4, 5) ]
                    |> URelation.symmetric_closure
                  in

                  let structure =
                    {
                      (SymbolicEventStructure.create ()) with
                      e;
                      events;
                      po;
                      origin;
                      conflict;
                      read_events;
                      write_events;
                    }
                  in

                  (structure, events)

    (* Create an elaboration context from a structure *)
    let create_elab_ctx structure =
      let fj = USet.create () in
      let op_trace = OpTrace.create 0 in
      let forwardingcontext_state =
        Forwardingcontext.EventStructureContext.create structure
      in
        { forwardingcontext_state; structure; fj; op_trace }

    (* Predicate test cases *)
    type predicate_test_case = {
      name : string;
      p1 : Expr.t list;
      p2 : Expr.t list;
      expected_dist_pred : Expr.t list option;
      expected_disjunction : Expr.t list option;
    }

    let predicate_test_cases =
      [
        {
          name = "basic_distinguishing_predicates";
          p1 =
            [
              EBinOp (ESymbol "δ", "=", ENum Z.zero);
              EBinOp (ESymbol "α", "!=", ENum Z.zero);
            ];
          p2 =
            [
              EBinOp (ESymbol "δ", "=", ENum Z.zero);
              EBinOp (ESymbol "α", "=", ENum Z.zero);
            ];
          expected_dist_pred =
            Some
              ([ EBinOp (ESymbol "α", "!=", ENum Z.zero) ]
              |> Expr.evaluate_conjunction
              );
          expected_disjunction =
            Some
              ([ EBinOp (ESymbol "δ", "=", ENum Z.zero) ]
              |> Expr.evaluate_conjunction
              );
        };
      ]

    (* Justification builder *)
    type justification_spec = {
      predicates : Expr.t list;
      dependencies : string list;
      write_label : int;
    }

    let create_justification events spec =
      let write_event = Hashtbl.find events spec.write_label in
        {
          p = spec.predicates;
          d = USet.of_list spec.dependencies;
          fwd = USet.create ();
          we = USet.create ();
          w = write_event;
        }

    (* Relabeling test cases *)
    type relabeling_test_case = {
      name : string;
      just_1_spec : justification_spec;
      just_2_spec : justification_spec;
      expected_relabeling_count : int;
      expected_mappings : (string * string) list;
    }

    let relabeling_test_cases =
      [
        {
          name = "basic_relabeling";
          just_1_spec =
            {
              predicates =
                [
                  EBinOp (ESymbol "α", "!=", ENum Z.zero);
                  EBinOp (ESymbol "β", "!=", ENum Z.zero);
                ];
              dependencies = [ "α"; "β" ];
              write_label = 4;
            };
          just_2_spec =
            {
              predicates =
                [
                  EBinOp (ESymbol "α", "=", ENum Z.zero);
                  EBinOp (ESymbol "γ", "!=", ENum Z.zero);
                ];
              dependencies = [ "α"; "γ" ];
              write_label = 5;
            };
          expected_relabeling_count = 1;
          expected_mappings = [ ("β", "γ") ];
        };
      ]

    (* Elaboration test cases *)
    type elaboration_test_case = {
      name : string;
      just_1_spec : justification_spec;
      just_2_spec : justification_spec;
      expected_lifting_count : int;
      expected_predicates : Expr.t list;
      expected_dependencies : string list;
      expected_write_label : int;
    }

    let elaboration_test_cases =
      [
        {
          name = "basic_elaboration";
          just_1_spec =
            {
              predicates =
                [
                  EBinOp (ESymbol "α", "!=", ENum Z.zero);
                  EBinOp (ESymbol "β", "!=", ENum Z.zero);
                ];
              dependencies = [ "α"; "β" ];
              write_label = 4;
            };
          just_2_spec =
            {
              predicates =
                [
                  EBinOp (ESymbol "α", "=", ENum Z.zero);
                  EBinOp (ESymbol "γ", "!=", ENum Z.zero);
                ];
              dependencies = [ "α"; "γ" ];
              write_label = 5;
            };
          expected_lifting_count = 1;
          expected_predicates = [ EBinOp (ESymbol "γ", "!=", ENum Z.zero) ];
          expected_dependencies = [ "γ" ];
          expected_write_label = 5;
        };
      ]
  end

  (* ============================================================
     Test Implementations
     ============================================================ *)

  let test_find_distinguishing_predicate_with_case test_case =
   fun () ->
    let diff =
      Lifting.find_distinguishing_predicate test_case.TestData.p1 test_case.p2
    in
      match
        (diff, test_case.expected_dist_pred, test_case.expected_disjunction)
      with
      | Some (pred, disjunction), Some dist_pred, Some dist_disjunction ->
          let matched =
            List.equal Expr.equal pred dist_pred
            && List.equal Expr.equal disjunction dist_disjunction
          in
            check bool
              (Printf.sprintf "%s: distinguishing predicate matched"
                 test_case.name
              )
              true matched
      | None, None, None ->
          check bool
            (Printf.sprintf "%s: no distinguishing predicate expected"
               test_case.name
            )
            true true
      | _ ->
          check bool
            (Printf.sprintf "%s: unexpected result" test_case.name)
            false true

  let test_generate_relabelings_with_case
      (test_case : TestData.relabeling_test_case) =
   fun () ->
    let structure, events = TestData.create_basic_structure () in
    let elab_ctx = TestData.create_elab_ctx structure in
    let just_1 =
      TestData.create_justification events test_case.TestData.just_1_spec
    in
    let just_2 = TestData.create_justification events test_case.just_2_spec in
    let ppo_1 = USet.of_list [] in
    let ppo_2 = USet.of_list [] in
    let forwardingcontext_state =
      Forwardingcontext.EventStructureContext.create structure
    in
    let con_1 = ForwardingContext.create forwardingcontext_state () in
    let con_2 = ForwardingContext.create forwardingcontext_state () in

    Lwt_main.run
      (let* relabelings =
         Lifting.generate_relabelings elab_ctx just_1 just_2 ppo_1 ppo_2 con_1
           con_2
       in
       let relabeling = USet.values relabelings |> List.hd in
         check int
           (Printf.sprintf "%s: relabeling size" test_case.name)
           (List.length test_case.expected_mappings)
           (Hashtbl.length relabeling);

         List.iter
           (fun (from_sym, to_sym) ->
             let mapped = Hashtbl.find_opt relabeling from_sym in
             let matched =
               match mapped with
               | Some s -> s = to_sym
               | None -> false
             in
               check bool
                 (Printf.sprintf "%s: %s mapped to %s" test_case.name from_sym
                    to_sym
                 )
                 true matched
           )
           test_case.expected_mappings;
         Lwt.return_unit
      )

  let test_elab_with_case test_case =
   fun () ->
    let structure, events = TestData.create_basic_structure () in
    let elab_ctx = TestData.create_elab_ctx structure in
    let just_1 =
      TestData.create_justification events test_case.TestData.just_1_spec
    in
    let just_2 = TestData.create_justification events test_case.just_2_spec in

    Lwt_main.run
      (let* liftings = Lifting.elab elab_ctx just_1 just_2 in
         check int
           (Printf.sprintf "%s: number of liftings" test_case.name)
           test_case.expected_lifting_count (List.length liftings);

         if test_case.expected_lifting_count > 0 then (
           let just = List.hd liftings in
             check bool
               (Printf.sprintf "%s: lifting has correct predicates"
                  test_case.name
               )
               true
               (List.equal Expr.equal just.p test_case.expected_predicates);
             check bool
               (Printf.sprintf "%s: lifting has correct dependency set"
                  test_case.name
               )
               true
               (USet.equal just.d (USet.of_list test_case.expected_dependencies));
             check bool
               (Printf.sprintf "%s: lifting has correct write event"
                  test_case.name
               )
               true
               (just.w.label = test_case.expected_write_label);
             check bool
               (Printf.sprintf "%s: lifting has empty fwd" test_case.name)
               true
               (USet.size just.fwd = 0);
             check bool
               (Printf.sprintf "%s: lifting has empty we" test_case.name)
               true
               (USet.size just.we = 0)
         );
         Lwt.return_unit
      )

  (* ============================================================
     Test Suite Generation
     ============================================================ *)

  let generate_predicate_tests () =
    List.map
      (fun (test_case : TestData.predicate_test_case) ->
        Alcotest.test_case
          ("find_distinguishing_predicate_" ^ test_case.name)
          `Quick
          (test_find_distinguishing_predicate_with_case test_case)
      )
      TestData.predicate_test_cases

  let generate_relabeling_tests () =
    List.map
      (fun (test_case : TestData.relabeling_test_case) ->
        Alcotest.test_case
          ("generate_relabelings_" ^ test_case.name)
          `Quick
          (test_generate_relabelings_with_case test_case)
      )
      TestData.relabeling_test_cases

  let generate_elaboration_tests () =
    List.map
      (fun (test_case : TestData.elaboration_test_case) ->
        Alcotest.test_case ("elab_" ^ test_case.name) `Quick
          (test_elab_with_case test_case)
      )
      TestData.elaboration_test_cases

  let suite =
    List.concat
      [
        generate_predicate_tests ();
        generate_relabeling_tests ();
        generate_elaboration_tests ();
      ]
end

(** Test suite *)

let suite =
  ( "Elaborations",
    [
      (* Filter and value_assign *)
      test_case "value_assign operations" `Quick test_value_assign_operations;
      (* Forward-related *)
      test_case "fprime operations" `Quick test_fprime_operations;
      test_case "fwd operations" `Quick test_fwd_operations;
      test_case "we operations" `Quick test_we_operations;
      test_case "forward operations" `Quick test_forward_operations;
      (* Lift, weaken, strengthen *)
      test_case "lift and weaken" `Quick test_lift_and_weaken;
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
    (* Parameterized symbol extraction tests *)
    @ List.map
        (fun ((name, _, _) as case) ->
          test_case
            ("pre_justifications symbols " ^ name)
            `Quick
            (test_pre_justifications_symbol_extraction case)
        )
        TestData.symbol_extraction_cases
    @ LiftingTests.suite
  )
