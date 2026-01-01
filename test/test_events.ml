(** Unit tests for Events module *)
open Uset

open Alcotest
open Expr
open Types
open Events

(** Helper to create test events *)
let make_test_event typ label = Event.create typ label ()

let make_read label (id : string) rval rmod =
  let id_val = if is_symbol id then VSymbol id else VVar id in
  let loc = if is_symbol id then ESymbol id else EVar id in
    Event.create Read label ~id:id_val ~loc ~rval:(VSymbol rval) ~rmod ()

let make_write label (id : string) wval wmod =
  let id_val = if is_symbol id then VSymbol id else VVar id in
  let loc = if is_symbol id then ESymbol id else EVar id in
    Event.create Write label ~id:id_val ~loc ~wval:(ESymbol wval) ~wmod ()

let make_fence label fmod = Event.create Fence label ~fmod ()

let make_rmw label (id : string) rval wval rmod wmod =
  let id_val = if is_symbol id then VSymbol id else VVar id in
  let loc = if is_symbol id then ESymbol id else EVar id in
    Event.create RMW label ~id:id_val ~loc ~rval:(VSymbol rval)
      ~wval:(ESymbol wval) ~rmod ~wmod ()

(** Test ModeOps *)
let test_mode_to_string_or () =
  check string "relaxed is empty" "" (Events.ModeOps.to_string_or Relaxed);
  check string "acquire" "acq" (Events.ModeOps.to_string_or Acquire);
  check string "release" "rel" (Events.ModeOps.to_string_or Release);
  check string "sc" "sc" (Events.ModeOps.to_string_or SC)

let test_mode_checked_read () =
  check bool "relaxed ok" true (Events.ModeOps.checked_read Relaxed = Relaxed);
  check bool "acquire ok" true (Events.ModeOps.checked_read Acquire = Acquire);
  check bool "sc becomes acquire" true (Events.ModeOps.checked_read SC = Acquire);
  check_raises "release fails" (Failure "Read cannot be release") (fun () ->
      Events.ModeOps.checked_read Release |> ignore
  )

let test_mode_checked_write () =
  check bool "relaxed ok" true (Events.ModeOps.checked_write Relaxed = Relaxed);
  check bool "release ok" true (Events.ModeOps.checked_write Release = Release);
  check bool "sc becomes release" true
    (Events.ModeOps.checked_write SC = Release);
  check_raises "acquire fails" (Failure "Write cannot be acquire") (fun () ->
      Events.ModeOps.checked_write Acquire |> ignore
  )

let test_mode_ordering () =
  check bool "relaxed <= relaxed" true (Events.ModeOps.mode_le Relaxed Relaxed);
  check bool "relaxed <= acquire" true (Events.ModeOps.mode_le Relaxed Acquire);
  check bool "relaxed <= release" true (Events.ModeOps.mode_le Relaxed Release);
  check bool "relaxed <= sc" true (Events.ModeOps.mode_le Relaxed SC);
  check bool "acquire <= sc" true (Events.ModeOps.mode_le Acquire SC);
  check bool "release <= sc" true (Events.ModeOps.mode_le Release SC);
  check bool "acquire not <= release" false
    (Events.ModeOps.mode_le Acquire Release);
  check bool "sc not <= acquire" false (Events.ModeOps.mode_le SC Acquire)

(** Test event predicates *)
let test_event_predicates () =
  let cases =
    [
      ("is_read", true, Event.is_read, Read);
      ("not,is_read", false, Event.is_read, Write);
      ("is_write", true, Event.is_write, Write);
      ("is_fence", true, Event.is_fence, Fence);
      ("is_lock", true, Event.is_lock, Lock);
      ("is_unlock", true, Event.is_unlock, Unlock);
      ("is_malloc", true, Event.is_malloc, Malloc);
      ("is_free", true, Event.is_free, Free);
      ("is_rmw", true, Event.is_rmw, RMW);
      ("is_read_write,read", true, Event.is_read_write, Read);
      ("is_read_write,write", true, Event.is_read_write, Write);
      ("not,is_read_write,fence", false, Event.is_read_write, Fence);
      ("is_mem_func,malloc", true, Event.is_mem_func, Malloc);
      ("is_mem_func,free", true, Event.is_mem_func, Free);
      ("is_lock_unlock,lock", true, Event.is_lock_unlock, Lock);
      ("is_lock_unlock,unlock", true, Event.is_lock_unlock, Unlock);
      ("is_ordering,fence", true, Event.is_ordering, Fence);
      ("is_ordering,lock", true, Event.is_ordering, Lock);
    ]
  in

  List.iter
    (fun (msg, expected, test_fun, typ) ->
      let event = make_test_event typ 0 in
        check bool msg expected (test_fun event)
    )
    cases;
  ()

(** Test event field accessors *)
let test_has_fields () =
  let read_ev = make_test_event Read 1 in
  let write_ev = make_test_event Write 2 in
  let fence_ev = make_test_event Fence 3 in
  let branch_ev = make_test_event Branch 4 in
  let malloc_ev = make_test_event Malloc 5 in

  check bool "read has_id" true (Event.has_id read_ev);
  check bool "write has_id" true (Event.has_id write_ev);
  check bool "fence not has_id" false (Event.has_id fence_ev);

  check bool "read has_val" true (Event.has_val read_ev);
  check bool "fence not has_val" false (Event.has_val fence_ev);

  check bool "read has_rval" true (Event.has_rval read_ev);
  check bool "write not has_rval" false (Event.has_rval write_ev);

  check bool "write has_wval" true (Event.has_wval write_ev);
  check bool "read not has_wval" false (Event.has_wval read_ev);

  check bool "branch has_cond" true (Event.has_cond branch_ev);
  check bool "read not has_cond" false (Event.has_cond read_ev);

  check bool "malloc has_id" true (Event.has_id malloc_ev);
  check bool "malloc has_rval" true (Event.has_rval malloc_ev);
  check bool "malloc has_wval" true (Event.has_wval malloc_ev)

let test_get_fields () =
  let read_ev = make_read 1 "x" "v1" Relaxed in
  let write_ev = make_write 2 "y" "v2" Release in

  check bool "get_id read" true
    ( match Event.get_id read_ev with
    | VVar "x" -> true
    | _ -> false
    );
  check bool "get_rval read" true
    ( match Event.get_rval read_ev with
    | VSymbol "v1" -> true
    | _ -> false
    );
  check bool "get_id write" true
    ( match Event.get_id write_ev with
    | VVar "y" -> true
    | _ -> false
    );
  check bool "get_wval write" true
    ( match Event.get_wval write_ev with
    | ESymbol "v2" -> true
    | _ -> false
    );

  let fence_ev = make_test_event Fence 3 in
    check_raises "get_id on fence fails"
      (Failure "Event 3 type does not support id") (fun () ->
        Event.get_id fence_ev |> ignore
    )

let test_event_order () =
  let read_ev = make_read 1 "x" "v" Acquire in
  let write_ev = make_write 2 "y" "v" Release in
  let fence_ev = make_fence 3 SC in

  check bool "read order is acquire" true (Event.event_order read_ev = Acquire);
  check bool "write order is release" true (Event.event_order write_ev = Release);
  check bool "fence order is sc" true (Event.event_order fence_ev = SC)

(** Test event creation *)
let test_event_creation () =
  let e = Event.create Read 1 () in
    check int "label is 1" 1 e.label;
    check bool "type is read" true (e.typ = Read);
    check bool "id is none" true (e.id = None);
    check bool "default rmod is relaxed" true (e.rmod = Relaxed)

let test_fence_creation () =
  let e = Event.create Fence 1 ~fmod:SC ~volatile:false () in
    check bool "fence rmod adjusted" true (e.rmod = Acquire);
    check bool "fence wmod adjusted" true (e.wmod = Release);
    check bool "fence fmod is sc" true (e.fmod = SC)

let test_malloc_creation () =
  let rval = VSymbol "α" in
  let e = Event.create Malloc 1 ~rval ~wval:(ENum Z.one) ~volatile:false () in
    check bool "malloc id set to rval" true
      ( match e.id with
      | Some (VSymbol "α") -> true
      | _ -> false
      )

let test_clone_event () =
  let e1 = make_read 1 "x" "v" Acquire in
  let e2 = Event.clone e1 in
  let result = Event.equal e1 e2 in
    check bool "cloned event equals original" true (Event.equal e1 e2);
    check bool "cloned event same label" true (e1.label = e2.label)

(** Test event to string *)
let test_event_to_string () =
  let read_rlx = make_read 1 "x" "v1" Relaxed in
  let read_acq = make_read 2 "x" "v2" Acquire in
  let write_rel = make_write 3 "y" "v3" Release in
  let fence_sc = make_fence 4 SC in

  check string "read relaxed" "1: R x v1" (Event.to_string read_rlx);
  check string "read acquire" "2: Racq x v2" (Event.to_string read_acq);
  check string "write release" "3: Wrel y v3" (Event.to_string write_rel);
  check string "fence sc" "4: Fsc" (Event.to_string fence_sc);

  let volatile_read = { read_rlx with volatile = true } in
    check string "volatile read" "1: vR x v1" (Event.to_string volatile_read)

let test_rmw_to_string () =
  let rmw = make_rmw 1 "x" "v1" "v2" Acquire Release in
  let s = Event.to_string rmw in
    check bool "rmw contains id" true (String.contains s 'x');
    check bool "rmw contains R" true (String.contains s 'R');
    check bool "rmw contains W" true (String.contains s 'W')

let test_event_equality () =
  let e1 = make_read 1 "x" "v" Relaxed in
  let e2 = make_read 1 "x" "v" Relaxed in
  let e3 = make_read 1 "y" "v" Relaxed in
  let e4 = make_read 2 "x" "v" Relaxed in

  check bool "equal events" true (Event.equal e1 e2);
  check bool "different id" false (Event.equal e1 e3);
  check bool "different label" false (Event.equal e1 e4)

(** Test EventsContainer *)
let test_container_create () =
  let c = EventsContainer.create () in
    check int "initial next_label" 1 c.next_label

let test_container_add () =
  let c = EventsContainer.create () in
  let e1 = make_test_event Read 0 in
  let e1' = EventsContainer.add c e1 in

  check int "auto assigned label" 1 e1'.label;
  check int "next_label incremented" 2 c.next_label;

  let e2 = make_test_event Write 0 in
  let e2' = EventsContainer.add c ~label:10 e2 in
    check int "explicit label" 10 e2'.label;
    check int "next_label updated" 11 c.next_label

let test_container_get () =
  let c = EventsContainer.create () in
  let e = make_test_event Read 0 in
  let e' = EventsContainer.add c e in

  match EventsContainer.get c e'.label with
  | Some retrieved ->
      check bool "retrieved event matches" true (Event.equal e' retrieved)
  | None -> fail "event not found"

let test_container_all () =
  let c = EventsContainer.create () in
  let _ = EventsContainer.add c (make_test_event Read 0) in
  let _ = EventsContainer.add c (make_test_event Write 0) in
  let _ = EventsContainer.add c (make_test_event Fence 0) in

  let all = EventsContainer.all c in
    check int "all returns 3 events" 3 (USet.size all)

let test_container_map_filter () =
  let c = EventsContainer.create () in
  let e1 = EventsContainer.add c (make_read 0 "x" "v1" Relaxed) in
  let _e2 = EventsContainer.add c (make_write 0 "y" "v2" Release) in
  let e3 = EventsContainer.add c (make_read 0 "z" "v3" Acquire) in
  let _e4 = EventsContainer.add c (make_fence 0 SC) in

  let all_labels = EventsContainer.all c in

  (* Filter only reads *)
  let reads = EventsContainer.map c all_labels ~typ:Read () in
    check int "map finds 2 reads" 2 (USet.size reads);
    check bool "contains e1" true (USet.mem reads e1.label);
    check bool "contains e3" true (USet.mem reads e3.label);

    (* Filter only writes *)
    let writes = EventsContainer.map c all_labels ~typ:Write () in
      check int "map finds 1 write" 1 (USet.size writes);

      (* Filter by mode *)
      let acquire_events = EventsContainer.map c all_labels ~mode:Acquire () in
        check int "map finds 1 acquire" 1 (USet.size acquire_events);

        (* Filter by mode with ordering *)
        let relaxed_or_higher =
          EventsContainer.map c all_labels ~mode:Relaxed ~mode_op:">" ()
        in
          check bool "relaxed or higher includes all" true
            (USet.size relaxed_or_higher >= 3)

let test_container_clone () =
  let c1 = EventsContainer.create () in
  let _ = EventsContainer.add c1 (make_test_event Read 0) in
  let _ = EventsContainer.add c1 (make_test_event Write 0) in

  let c2 = EventsContainer.clone c1 in
    check int "cloned size matches"
      (USet.size (EventsContainer.all c1))
      (USet.size (EventsContainer.all c2));
    check int "cloned next_label matches" c1.next_label c2.next_label;

    (* Add to original, shouldn't affect clone *)
    let _ = EventsContainer.add c1 (make_test_event Fence 0) in
      check bool "clone unaffected by add" true
        (USet.size (EventsContainer.all c1) > USet.size (EventsContainer.all c2))

let test_container_rewrite () =
  let c = EventsContainer.create () in
  let e = EventsContainer.add c (make_read 0 "x" "v1" Relaxed) in
  let new_e = make_read e.label "y" "v2" Acquire in

  let _ = EventsContainer.rewrite c e.label new_e in

  match EventsContainer.get c e.label with
  | Some retrieved ->
      check bool "rewritten event has new id" true
        ( match Event.get_id retrieved with
        | VVar "y" -> true
        | _ -> false
        )
  | None -> fail "event not found after rewrite"

(** Test suite *)
let suite =
  ( "Events",
    [
      test_case "mode_to_string_or" `Quick test_mode_to_string_or;
      test_case "mode_checked_read" `Quick test_mode_checked_read;
      test_case "mode_checked_write" `Quick test_mode_checked_write;
      test_case "mode_ordering" `Quick test_mode_ordering;
      test_case "event_predicates" `Quick test_event_predicates;
      test_case "has_fields" `Quick test_has_fields;
      test_case "get_fields" `Quick test_get_fields;
      test_case "event_order" `Quick test_event_order;
      test_case "basic_creation" `Quick test_event_creation;
      test_case "fence_creation" `Quick test_fence_creation;
      test_case "malloc_creation" `Quick test_malloc_creation;
      test_case "clone_event" `Quick test_clone_event;
      test_case "event_to_string" `Quick test_event_to_string;
      test_case "rmw_to_string" `Quick test_rmw_to_string;
      test_case "event_equality" `Quick test_event_equality;
      test_case "container_create" `Quick test_container_create;
      test_case "container_add" `Quick test_container_add;
      test_case "container_get" `Quick test_container_get;
      test_case "container_all" `Quick test_container_all;
      test_case "container_map_filter" `Quick test_container_map_filter;
      test_case "container_clone" `Quick test_container_clone;
      test_case "container_rewrite" `Quick test_container_rewrite;
    ]
  )
