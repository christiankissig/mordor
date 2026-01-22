open Context
open Events
open Eventstructures
open Expr
open Interpret
open Ir
open Lwt.Syntax
open Types
open Uset

let make_ir_node stmt =
  {
    stmt;
    annotations = { source_span = None; thread_ctx = None; loop_ctx = None };
  }

(** Helper to run Lwt tests *)
let run_lwt f () = Lwt_main.run (f ())

(** Reset counters for consistent testing *)
let reset_counters () =
  event_counter := 0;
  greek_counter := 0;
  zh_counter := 0

(** Test event ID generation *)
let test_next_event_id () =
  reset_counters ();
  let id1 = next_event_id () in
  let id2 = next_event_id () in
  let id3 = next_event_id () in
    Alcotest.(check int) "first event id" 1 id1;
    Alcotest.(check int) "second event id" 2 id2;
    Alcotest.(check int) "third event id" 3 id3

(** Test Greek symbol generation *)
let test_next_greek () =
  reset_counters ();
  let g1 = next_greek () in
  let g2 = next_greek () in
    Alcotest.(check string) "first greek symbol" "α" g1;
    Alcotest.(check string) "second greek symbol" "β" g2

let test_next_greek_overflow () =
  reset_counters ();
  (* Generate more symbols than in the alphabet to test suffix *)
  for _i = 1 to String.length greek_alpha do
    let _ = next_greek () in
      ()
  done;
  let overflow = next_greek () in
    Alcotest.(check string) "greek with suffix" "α2" overflow

(** Test Chinese symbol generation *)
let test_next_zh () =
  reset_counters ();
  let z1 = next_zh () in
  let z2 = next_zh () in
    Alcotest.(check bool) "first zh is string" true (String.length z1 > 0);
    Alcotest.(check bool) "second zh is string" true (String.length z2 > 0);
    Alcotest.(check bool) "zh symbols differ" true (z1 <> z2)

(** Test events collection creation *)
let test_create_events () =
  let events = create_events () in
    Alcotest.(check int) "initial label is 1" 0 events.label;
    Alcotest.(check int) "events table is empty" 0 (Hashtbl.length events.events)

(** Test adding events *)
let test_add_event () =
  reset_counters ();
  let events = create_events () in
  let evt = Event.create Read 0 () in
  let env = Hashtbl.create 16 in
  let added_evt =
    add_event events evt env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
    Alcotest.(check int) "event label assigned" 0 added_evt.label;
    Alcotest.(check int) "label counter incremented" 1 events.label;
    Alcotest.(check int) "event added to table" 1 (Hashtbl.length events.events)

let test_add_multiple_events () =
  reset_counters ();
  let events = create_events () in
  let evt1 = Event.create Read 0 () in
  let evt2 = Event.create Write 0 () in
  let env = Hashtbl.create 16 in
  let _ =
    add_event events evt1 env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
  let added_evt2 =
    add_event events evt2 env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
    Alcotest.(check int) "second event label" 1 added_evt2.label;
    Alcotest.(check int) "events in table" 2 (Hashtbl.length events.events)

(** Test empty structure *)
let test_empty_structure () =
  let s = SymbolicEventStructure.create () in
    Alcotest.(check int) "empty events" 0 (USet.size s.e);
    Alcotest.(check int) "empty po" 0 (USet.size s.po);
    Alcotest.(check int) "empty rmw" 0 (USet.size s.rmw);
    Alcotest.(check int) "empty lo" 0 (USet.size s.lo);
    Alcotest.(check int) "empty fj" 0 (USet.size s.fj);
    (* Alcotest.(check int) "empty p" 0 (Hashtbl.size s.p); TODO *)
    Alcotest.(check int) "empty constraints" 0 (List.length s.constraints);
    Alcotest.(check int) "empty pwg" 0 (List.length s.pwg)

(** Test SymbolicEventStructure.dot operation *)
let test_dot () =
  let s = SymbolicEventStructure.create () in
  let s' = { s with e = USet.of_list [ 2; 3 ] } in
  let evt = Event.create Read 1 () in
  let result = SymbolicEventStructure.dot evt s' [] in
    Alcotest.(check bool) "event 1 in result" true (USet.mem result.e 1);
    Alcotest.(check bool) "event 2 in result" true (USet.mem result.e 2);
    Alcotest.(check bool) "event 3 in result" true (USet.mem result.e 3);
    Alcotest.(check int) "result has 3 events" 3 (USet.size result.e);
    (* Check po relations added *)
    Alcotest.(check bool) "po (1,2) exists" true (USet.mem result.po (1, 2));
    Alcotest.(check bool) "po (1,3) exists" true (USet.mem result.po (1, 3))

(** Test SymbolicEventStructure.plus operation *)
let test_plus () =
  let s1 =
    { (SymbolicEventStructure.create ()) with e = USet.of_list [ 1; 2 ] }
  in
  let s2 =
    { (SymbolicEventStructure.create ()) with e = USet.of_list [ 3; 4 ] }
  in
  let result = SymbolicEventStructure.plus s1 s2 in
    Alcotest.(check int) "merged events" 4 (USet.size result.e);
    Alcotest.(check bool) "has event 1" true (USet.mem result.e 1);
    Alcotest.(check bool) "has event 2" true (USet.mem result.e 2);
    Alcotest.(check bool) "has event 3" true (USet.mem result.e 3);
    Alcotest.(check bool) "has event 4" true (USet.mem result.e 4)

let test_plus_with_relations () =
  let s1 =
    {
      (SymbolicEventStructure.create ()) with
      e = USet.of_list [ 1 ];
      po = USet.of_list [ (1, 2) ];
      rmw = USet.of_list [ (1, 3) ];
    }
  in
  let s2 =
    {
      (SymbolicEventStructure.create ()) with
      e = USet.of_list [ 4 ];
      po = USet.of_list [ (4, 5) ];
      rmw = USet.of_list [ (4, 6) ];
    }
  in
  let result = SymbolicEventStructure.plus s1 s2 in
    Alcotest.(check int) "merged po relations" 2 (USet.size result.po);
    Alcotest.(check int) "merged rmw relations" 2 (USet.size result.rmw)

(** Test SymbolicEventStructure.cross operation *)
let test_cross () =
  let s1 =
    { (SymbolicEventStructure.create ()) with e = USet.of_list [ 1; 2 ] }
  in
  let s2 =
    { (SymbolicEventStructure.create ()) with e = USet.of_list [ 3; 4 ] }
  in
  let result = SymbolicEventStructure.cross s1 s2 in
    Alcotest.(check int) "crossed events" 4 (USet.size result.e);
    Alcotest.(check bool) "has event 1" true (USet.mem result.e 1);
    Alcotest.(check bool) "has event 4" true (USet.mem result.e 4)

(** Test interpret_statements with empty list *)
let test_interpret_empty_statements =
  run_lwt (fun () ->
      let env = Hashtbl.create 16 in
      let events = create_events () in
        let* result = interpret_statements [] env [] events in
          Alcotest.(check int) "only terminal event" 1 (USet.size result.e);
          Lwt.return_unit
  )

(** Test interpret GlobalStore statement *)
let test_interpret_global_store =
  run_lwt (fun () ->
      reset_counters ();
      let env = Hashtbl.create 16 in
      let events = create_events () in
      let mode = Types.SC in
      let expr = ENum Z.zero in
      let stmt =
        GlobalStore { global = "x"; expr; assign = { mode; volatile = false } }
      in
        let* result =
          interpret_statements [ make_ir_node stmt ] env [] events
        in
          Alcotest.(check int) "two events created" 2 (USet.size result.e);
          (* includes terminal event *)
          Alcotest.(check int)
            "two events in table" 2
            (Hashtbl.length events.events);
          Lwt.return_unit
  )

(** Test interpret GlobalLoad statement *)
let test_interpret_global_load =
  run_lwt (fun () ->
      reset_counters ();
      let env = Hashtbl.create 16 in
      let events = create_events () in
      let mode = Types.SC in
      let stmt =
        GlobalLoad
          { register = "r"; global = "x"; load = { mode; volatile = false } }
      in
        let* result =
          interpret_statements [ make_ir_node stmt ] env [] events
        in
          Alcotest.(check int) "one event created" 1 (USet.size result.e);
          Alcotest.(check bool) "register in env" true (Hashtbl.mem env "r");
          Lwt.return_unit
  )

(** Test interpret Fence statement *)
let test_interpret_fence =
  run_lwt (fun () ->
      reset_counters ();
      let env = Hashtbl.create 16 in
      let events = create_events () in
      let mode = Types.SC in
      let stmt = Ir.Fence { mode } in
        let* result =
          interpret_statements [ make_ir_node stmt ] env [] events
        in
          Alcotest.(check int)
            "one fence event SymbolicEventStructure.plus terminal event" 2
            (USet.size result.e);
          let evt = Hashtbl.find events.events 0 in
            Alcotest.(check bool) "is fence" true (evt.typ = Fence);
            Lwt.return_unit
  )

(** Test interpret multiple statements *)
let test_interpret_multiple_statements =
  run_lwt (fun () ->
      reset_counters ();
      let env = Hashtbl.create 16 in
      let events = create_events () in
      let stmts =
        List.map make_ir_node
          [
            Ir.Fence { mode = Types.SC };
            GlobalStore
              {
                global = "x";
                expr = ENum Z.zero;
                assign = { mode = Types.Release; volatile = false };
              };
          ]
      in
        let* result = interpret_statements stmts env [] events in
          Alcotest.(check int) "three events" 3 (USet.size result.e);
          (* includes terminal event *)
          Alcotest.(check int)
            "three events in table" 3
            (Hashtbl.length events.events);
          Lwt.return_unit
  )

(** Test main interpret function *)
let test_interpret_main =
  run_lwt (fun () ->
      reset_counters ();
      let ast =
        List.map make_ir_node
          [
            GlobalStore
              {
                global = "x";
                expr = ENum Z.zero;
                assign = { mode = Types.SC; volatile = false };
              };
          ]
      in
        let* structure, events_tbl, _ = interpret ast None [] [] in
          Alcotest.(check int)
            "has init and store and terminal events" 3 (USet.size structure.e);
          Alcotest.(check bool)
            "init event present" true (USet.mem structure.e 0);
          (* includes terminal event *)
          Alcotest.(check int)
            "three events in table" 3
            (Hashtbl.length events_tbl);
          Lwt.return_unit
  )

let test_interpret_main_with_po =
  run_lwt (fun () ->
      reset_counters ();
      let ast =
        List.map make_ir_node
          [
            GlobalStore
              {
                global = "x";
                expr = ENum Z.zero;
                assign = { mode = Types.SC; volatile = false };
              };
            GlobalStore
              {
                global = "y";
                expr = ENum Z.one;
                assign = { mode = Types.SC; volatile = false };
              };
          ]
      in
        let* structure, _, _ = interpret ast None [] [] in
          Alcotest.(check int) "has four events" 4 (USet.size structure.e);
          (* Check that po relations exist *)
          Alcotest.(check bool) "po not empty" true (USet.size structure.po > 0);
          Lwt.return_unit
  )

(** Test suite *)
let suite =
  ( "Interpreter",
    [
      Alcotest.test_case "Event ID generation" `Quick test_next_event_id;
      Alcotest.test_case "Greek symbol generation" `Quick test_next_greek;
      Alcotest.test_case "Greek symbol overflow" `Quick test_next_greek_overflow;
      Alcotest.test_case "Chinese symbol generation" `Quick test_next_zh;
      Alcotest.test_case "Create events collection" `Quick test_create_events;
      Alcotest.test_case "Add single event" `Quick test_add_event;
      Alcotest.test_case "Add multiple events" `Quick test_add_multiple_events;
      Alcotest.test_case "Empty structure" `Quick test_empty_structure;
      Alcotest.test_case "Dot operation" `Quick test_dot;
      Alcotest.test_case "Plus operation" `Quick test_plus;
      Alcotest.test_case "Plus with relations" `Quick test_plus_with_relations;
      Alcotest.test_case "Cross operation" `Quick test_cross;
      Alcotest.test_case "Interpret empty statements" `Quick
        test_interpret_empty_statements;
      Alcotest.test_case "Interpret GlobalStore" `Quick
        test_interpret_global_store;
      Alcotest.test_case "Interpret Fence" `Quick test_interpret_fence;
      Alcotest.test_case "Interpret multiple statements" `Quick
        test_interpret_multiple_statements;
      Alcotest.test_case "Main interpret function" `Quick test_interpret_main;
      Alcotest.test_case "Main interpret with PO" `Quick
        test_interpret_main_with_po;
    ]
  )
