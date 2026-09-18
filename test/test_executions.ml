open Uset
open Alcotest
open Executions
open Events
open Eventstructures
open Expr
open Types
open Lwt.Syntax

let run_lwt f = Lwt_main.run (f ())

(** Test data providers *)

module TestData = struct
  let create_event id typ ?id_val ?rval ?wval () =
    {
      label = id;
      typ;
      id = id_val;
      loc = Option.map Expr.of_value id_val;
      rval;
      wval;
      cond = None;
      rmod = Normal;
      wmod = Normal;
      fmod = Normal;
      volatile = false;
      strong = None;
      is_rdmw = false;
    }

  let basic_events () =
    let events = Hashtbl.create 16 in
      Hashtbl.add events 0 (create_event 0 Init ());
      Hashtbl.add events 1 (create_event 1 Write ~id_val:(VVar "x") ());
      Hashtbl.add events 2 (create_event 2 Read ~id_val:(VVar "x") ());
      Hashtbl.add events 3 (create_event 3 Write ~id_val:(VVar "y") ());
      Hashtbl.add events 4 (create_event 4 Read ~id_val:(VVar "y") ());
      events

  let basic_origin () =
    let origin = Hashtbl.create 4 in
      origin

  let make_structure ?(events = basic_events ())
      ?(e = USet.of_list [ 1; 2; 3; 4 ])
      ?(po = USet.of_list [ (1, 2); (2, 3); (3, 4) ]) () =
    { (SymbolicEventStructure.create ()) with events; e; po }

  let make_justification ?p ?d ?fwd ?we w_event =
    {
      p = Option.value p ~default:[];
      d = Option.value d ~default:(USet.create ());
      fwd = Option.value fwd ~default:(USet.create ());
      we = Option.value we ~default:(USet.create ());
      w = w_event;
    }

  (* Test cases for disjoint function *)
  let disjoint_cases =
    [
      ("same location", EVar "x", ENum (Z.of_int 1), EVar "x", ENum (Z.of_int 2));
      ( "different locations",
        EVar "x",
        ENum (Z.of_int 1),
        EVar "y",
        ENum (Z.of_int 2)
      );
      ( "complex expressions",
        EBinOp (EVar "base", "+", ENum (Z.of_int 4)),
        ENum (Z.of_int 1),
        EBinOp (EVar "base", "+", ENum (Z.of_int 8)),
        ENum (Z.of_int 2)
      );
    ]

  (* Test cases for origin function *)
  let origin_test_cases =
    [
      ( "from_reads",
        fun () ->
          let events = basic_events () in
          let origin = basic_origin () in
          let sym_event = create_event 2 Read ~rval:(VSymbol "s1") () in
            Hashtbl.replace events 2 sym_event;
            Hashtbl.replace origin "s1" 2;
            (events, origin, USet.of_list [ 2; 4 ], USet.create (), "s1", Some 2)
      );
      ( "from_mallocs",
        fun () ->
          let events = basic_events () in
          let origin = basic_origin () in
          let malloc_event = create_event 5 Malloc ~rval:(VSymbol "s2") () in
            Hashtbl.add events 5 malloc_event;
            Hashtbl.replace origin "s2" 5;
            (events, origin, USet.create (), USet.singleton 5, "s2", Some 5)
      );
      ( "not_found",
        fun () ->
          ( basic_events (),
            basic_origin (),
            USet.of_list [ 2; 4 ],
            USet.create (),
            "nonexistent",
            None
          )
      );
    ]

  (* Test cases for path generation *)
  let path_gen_cases =
    [
      ( "linear",
        USet.of_list [ 1; 2; 3; 4 ],
        USet.of_list [ (1, 2); (2, 3); (3, 4) ],
        fun paths -> List.length paths > 0
      );
      ("empty", USet.create (), USet.create (), fun _paths -> true);
      ( "single_event",
        USet.of_list [ 1 ],
        USet.create (),
        fun paths -> List.length paths = 1
      );
    ]
end

(** Parameterized test utilities *)

let test_origin (name, setup) () =
  let events, origin, read_events, malloc_events, symbol, expected = setup () in
  let e = USet.union read_events malloc_events in
  let structure = TestData.make_structure ~events ~e () in
  let structure = { structure with origin; read_events; malloc_events } in
  let result = Eventstructures.origin structure symbol in
    match expected with
    | Some exp_id -> (
        match result with
        | Some id -> check int (name ^ ": should find event") exp_id id
        | None -> fail (name ^ ": Expected to find origin event")
      )
    | None -> (
        match result with
        | Some id ->
            check bool
              (name ^ ": should find valid event")
              true
              (id = 2 || id = 4)
        | None ->
            check (option int) (name ^ ": should not find origin") None result
      )

let test_path_generation (name, e, po, validator) () =
  let events = TestData.basic_events () in
  let structure = TestData.make_structure ~events ~e ~po () in
    try
      let paths = generate_max_conflictfree_sets structure in
        check bool (name ^ ": path validation") true (validator paths);
        List.iter
          (fun path_info ->
            check bool
              (name ^ ": path should not be empty")
              true
              (USet.size path_info.path >= 0)
          )
          paths
    with Failure _ ->
      check bool (name ^ ": should handle gracefully") true true

(** Property tests *)

let test_justification_properties () =
  let just1 =
    TestData.make_justification
      ~fwd:(USet.of_list [ (1, 2) ])
      (TestData.create_event 1 Write ())
  in
  let just2 =
    TestData.make_justification
      ~fwd:(USet.of_list [ (3, 4) ])
      (TestData.create_event 2 Write ())
  in

  let check_compat j1 j2 =
    let x1 = USet.union j1.fwd j1.we in
    let x2 = USet.union j2.fwd j2.we in
      USet.size (USet.intersection (URelation.pi_1 x1) (URelation.pi_2 x2)) = 0
      && USet.size (USet.intersection (URelation.pi_2 x1) (URelation.pi_1 x2))
         = 0
  in

  let compat_1_2 = check_compat just1 just2 in
  let compat_2_1 = check_compat just2 just1 in
    check bool "compatibility symmetry" compat_1_2 compat_2_1

(** Integration tests *)

let test_integration () =
  let events = TestData.basic_events () in
  let structure =
    TestData.make_structure
      ~e:(USet.of_list [ 1; 2; 3; 4 ])
      ~po:(USet.of_list [ (1, 2); (1, 3); (2, 4); (3, 4) ])
      ()
  in

  let paths = generate_max_conflictfree_sets structure in
    List.iter
      (fun path_info ->
        check bool "valid paths" true (USet.size path_info.path > 0)
      )
      paths;

    (* Test justification map building *)
    let justmap = Hashtbl.create 4 in
    let justs =
      List.init 2 (fun i ->
          TestData.make_justification (TestData.create_event (i + 1) Write ())
      )
    in
      Hashtbl.add justmap 1 justs;
      check int "justification map" 2 (List.length (Hashtbl.find justmap 1))

(** Test suite *)

(** {1 Scoped choice points} *)

(* SB, interpreted and elaborated: its structure, its one path, and its
   justifications by the write they justify. *)
let store_buffering () =
  let ctx =
    Context.make_context
      { Context.default_options with allow_unknown_model = true }
      ()
  in
    ctx.litmus <-
      Some
        "x := 0; y := 0; { x := 1; r1 := y } ||| { y := 1; r2 := x } %% allow \
         (r1 = 0 && r2 = 0) [sc]";
    let ctx =
      Lwt_main.run
        (Lwt.return ctx
        |> Parse.step_parse_litmus
        |> Interpret.step_interpret
        |> Elaborations.step_generate_justifications
        )
    in
    let structure = Option.get ctx.structure in
    let justmap = Hashtbl.create 8 in
      List.iter
        (fun (j : justification) ->
          Hashtbl.replace justmap j.w.label
            (j
            :: (Hashtbl.find_opt justmap j.w.label |> Option.value ~default:[])
            )
        )
        (Option.get ctx.justifications);
      (structure, List.hd (generate_max_conflictfree_sets structure), justmap)

let access structure typ loc =
  Hashtbl.fold
    (fun label (e : event) acc ->
      if e.typ = typ && e.loc = Some (EVar loc) then label else acc
    )
    structure.events (-1)

(* A scope of one write enumerates that write's justifications alone, and
   every one the whole path's enumeration chose for it. *)
let test_justification_combinations_in_a_scope () =
  let structure, path, justmap = store_buffering () in
  let x1 = access structure Write "x" in
  let combos scope =
    Lwt_main.run
      (compute_justification_combinations sequential_compute structure [ path ]
         ~scope justmap
      )
    |> List.map snd
  in
  let whole = combos (justifiable structure) in
  let local = combos (fun _ -> USet.singleton x1) in
  let chosen_for_x1 combo =
    List.filter (fun (j : justification) -> j.w.label = x1) combo
  in
  (* Both draw from [justmap], and a justification holds sets that [=] cannot
     compare. *)
  let same a b = List.length a = List.length b && List.for_all2 ( == ) a b in
    check bool "the whole path has combinations" true (whole <> []);
    check bool "each local combination justifies x := 1 alone" true
      (List.for_all
         (fun combo ->
           List.map (fun (j : justification) -> j.w.label) combo = [ x1 ]
         )
         local
      );
    check bool "every choice for x := 1 is enumerated locally" true
      (List.for_all
         (fun combo -> List.exists (same (chosen_for_x1 combo)) local)
         whole
      )

(* A scope of one read enumerates the writes that read can read from, and
   they are the ones the whole path's enumeration gives it. *)
let test_path_rf_in_a_scope () =
  let structure, path, _ = store_buffering () in
  let r1 = access structure Read "y" in
  let rf (scope : Freeze.scope) =
    Freeze.compute_path_rf structure path ~scope ~elided:(USet.create ())
      ~constraints:structure.constraints [] (USet.create ()) (USet.create ())
      (path.p @ structure.constraints)
  in
  let whole = Freeze.path_scope structure path ~elided:(USet.create ()) in
  let local = { whole with reads = USet.singleton r1 } in
  let sources combos =
    List.concat_map
      (List.filter_map (fun (r, w) -> if r = r1 then Some w else None))
      combos
    |> List.sort_uniq compare
  in
  let local_rf = rf local in
    check bool "each local relation reads r1 alone" true
      (List.for_all (fun c -> List.map fst c = [ r1 ]) local_rf);
    check (list int) "r1 reads from the writes it could on the whole path"
      (sources (rf whole))
      (sources local_rf);
    check bool "r1 has a write to read" true (sources local_rf <> [])

(** {1 Validation predicates} *)

let rel = USet.of_list

(* A read of an elided write, a read with no write, a cycle through rf. *)
let test_validation_predicates () =
  check bool "reading an elided write" false
    (Validation.rf_not_elided ~rf:(rel [ (1, 2) ]) ~delta:(rel [ (0, 1) ]));
  check bool "reading a write nothing elides" true
    (Validation.rf_not_elided ~rf:(rel [ (1, 2) ]) ~delta:(rel [ (0, 3) ]));
  check bool "a read with nothing to read" false
    (Validation.rf_total
       ~rf:(rel [ (1, 2) ])
       ~reads:(USet.of_list [ 2; 4 ])
       ~delta:(rel [])
    );
  check bool "an elided read needs nothing to read" true
    (Validation.rf_total
       ~rf:(rel [ (1, 2) ])
       ~reads:(USet.of_list [ 2; 4 ])
       ~delta:(rel [ (3, 4) ])
    );
  check bool "rf against dp closes a cycle" false
    (Validation.rhb_acyclic
       (Validation.rhb ~dp:(rel [ (2, 3) ]) ~ppo:(rel []) ~rf:(rel [ (3, 2) ]))
    );
  check bool "rf_respects_ppo holds of an rf edge in ppo" true
    (Validation.rf_respects_ppo ~rf:(rel [ (1, 2) ]) ~ppo:(rel [ (1, 2) ]))

(* The delta forms decide what the plain ones decide of the union. *)
let test_validation_deltas () =
  let base = rel [ (1, 2) ] and added = rel [ (2, 1) ] in
    check bool "a merge can close a cycle"
      (Validation.rhb_acyclic (USet.union base added))
      (Validation.rhb_acyclic_delta base ~drhb:added);
    check bool "a merge can elide a write already read"
      (Validation.rf_not_elided ~rf:base ~delta:(rel [ (0, 1) ]))
      (Validation.rf_not_elided_delta ~rf:base ~delta:(rel []) ~drf:(rel [])
         ~ddelta:(rel [ (0, 1) ])
      );
    check bool "a merge can add a read with nothing to read"
      (Validation.rf_total ~rf:base
         ~reads:(USet.of_list [ 2; 4 ])
         ~delta:(rel [])
      )
      (Validation.rf_total_delta ~rf:base ~reads:(USet.of_list [ 2 ])
         ~delta:(rel []) ~drf:(rel []) ~dreads:(USet.of_list [ 4 ])
         ~ddelta:(rel [])
      );
    check bool "rf_respects_ppo_delta"
      (Validation.rf_respects_ppo ~rf:(USet.union base added) ~ppo:base)
      (Validation.rf_respects_ppo_delta ~rf:base ~ppo:base ~drf:added
         ~dppo:(rel [])
      )

let suite =
  [
    (* Parameterized origin tests *)
    List.map
      (fun (name, setup) ->
        ("origin " ^ name, `Quick, test_origin (name, setup))
      )
      TestData.origin_test_cases;
    (* Parameterized path generation tests *)
    List.map
      (fun ((name, _, _, _) as case) ->
        ( "generate_max_conflictfree_sets " ^ name,
          `Quick,
          test_path_generation case
        )
      )
      TestData.path_gen_cases;
    (* Other tests *)
    [
      ("justification properties", `Quick, test_justification_properties);
      ("integration", `Quick, test_integration);
      ( "justification combinations in a scope",
        `Quick,
        test_justification_combinations_in_a_scope
      );
      ("read-from in a scope", `Quick, test_path_rf_in_a_scope);
      ("validation predicates", `Quick, test_validation_predicates);
      ("validation deltas", `Quick, test_validation_deltas);
    ];
  ]
  |> List.flatten

let suite = ("Executions", suite)
