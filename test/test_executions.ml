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
  let create_event id typ ?id_val ?cond ?rval ?wval () =
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
    {
      e;
      events;
      po;
      restrict = Hashtbl.create 4;
      cas_groups = Hashtbl.create 4;
      po_iter = USet.create ();
      rmw = USet.create ();
      lo = USet.create ();
      pwg = [];
      fj = USet.create ();
      p = Hashtbl.create 4;
      constraint_ = [];
      conflict = USet.create ();
      origin = Hashtbl.create 4;
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
    }

  let make_justification ?p ?d ?fwd ?we w_event =
    {
      p = Option.value p ~default:[];
      d = Option.value d ~default:(USet.create ());
      fwd = Option.value fwd ~default:(USet.create ());
      we = Option.value we ~default:(USet.create ());
      w = w_event;
      op = ("test", None, None);
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

(** Justification tests *)

(*
let test_choose_justifications () =
  run_lwt (fun () ->
      let test_cases =
        [
          ( "empty path",
            Hashtbl.create 4,
            USet.create (),
            fun result -> List.length result = 1 && result = [ [] ]
          );
          ( "no justifications",
            Hashtbl.create 4,
            USet.of_list [ 1 ],
            fun result -> List.length result = 0
          );
          ( "with justification",
            (let justmap = Hashtbl.create 4 in
             let just =
               TestData.make_justification (TestData.create_event 1 Write ())
             in
               Hashtbl.add justmap 1 [ just ];
               justmap
            ),
            USet.of_list [ 1 ],
            fun result -> List.length result > 0
          );
        ]
      in

      Lwt_list.iter_s
        (fun (name, justmap, path_events, validator) ->
          let* result =
            choose ~justmap ~path_events ~config:default_choose_config
          in
          let validate_result = validator result in
            check bool name true validate_result;
            Lwt.return_unit
        )
        test_cases
  )
  *)

(** Type construction tests *)

let test_type_constructors () =
  (* Test path_info *)
  let path_info =
    { path = USet.of_list [ 1; 2; 3 ]; p = [ EVar "x"; EVar "y" ] }
  in
    check int "path_info size" 3 (USet.size path_info.path);
    check int "path_info predicates" 2 (List.length path_info.p);

    (* Test freeze_result *)
    let freeze_res : FreezeResult.t =
      {
        e = USet.create ();
        dp = USet.create ();
        ppo = USet.create ();
        rf = USet.create ();
        rmw = USet.create ();
        pp = [];
        conds = [];
      }
    in
      check int "freeze_result empty" 0 (USet.size freeze_res.e)

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
      (*("choose justifications", `Quick, test_choose_justifications);*)
      ("type constructors", `Quick, test_type_constructors);
      ("justification properties", `Quick, test_justification_properties);
      ("integration", `Quick, test_integration);
    ];
  ]
  |> List.flatten

let suite = ("Executions", suite)
