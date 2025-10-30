(** Unit tests for Events module *)

open Alcotest
open Expr
open Types

(** Helper to create test events *)
let make_test_event typ label = Types.make_event typ label

let make_read label id rval rmod =
  {
    (Types.make_event Read label) with
    id = Some (VSymbol id);
    loc = Some (ESymbol id);
    rval = Some (VSymbol rval);
    rmod;
  }

let make_write label id wval wmod =
  {
    (Types.make_event Write label) with
    id = Some (VSymbol id);
    loc = Some (ESymbol id);
    wval = Some (ESymbol wval);
    wmod;
  }

let make_fence label fmod = { (Types.make_event Fence label) with fmod }

let make_rmw label id rval wval rmod wmod =
  {
    (Types.make_event RMW label) with
    id = Some (VSymbol id);
    loc = Some (ESymbol id);
    rval = Some (VSymbol rval);
    wval = Some (ESymbol wval);
    rmod;
    wmod;
  }

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
  let read_ev = make_test_event Read 1 in
  let write_ev = make_test_event Write 2 in
  let fence_ev = make_test_event Fence 3 in
  let lock_ev = make_test_event Lock 4 in
  let unlock_ev = make_test_event Unlock 5 in
  let malloc_ev = make_test_event Malloc 6 in
  let free_ev = make_test_event Free 7 in
  let rmw_ev = make_test_event RMW 8 in

  check bool "is_read" true (Events.is_read read_ev);
  check bool "not is_read" false (Events.is_read write_ev);
  check bool "is_write" true (Events.is_write write_ev);
  check bool "is_fence" true (Events.is_fence fence_ev);
  check bool "is_lock" true (Events.is_lock lock_ev);
  check bool "is_unlock" true (Events.is_unlock unlock_ev);
  check bool "is_malloc" true (Events.is_malloc malloc_ev);
  check bool "is_free" true (Events.is_free free_ev);
  check bool "is_rmw" true (Events.is_rmw rmw_ev);

  check bool "is_read_write read" true (Events.is_read_write read_ev);
  check bool "is_read_write write" true (Events.is_read_write write_ev);
  check bool "not is_read_write fence" false (Events.is_read_write fence_ev);

  check bool "is_mem_func malloc" true (Events.is_mem_func malloc_ev);
  check bool "is_mem_func free" true (Events.is_mem_func free_ev);

  check bool "is_lock_unlock lock" true (Events.is_lock_unlock lock_ev);
  check bool "is_lock_unlock unlock" true (Events.is_lock_unlock unlock_ev);

  check bool "is_ordering fence" true (Events.is_ordering fence_ev);
  check bool "is_ordering lock" true (Events.is_ordering lock_ev)

(** Test event field accessors *)
let test_has_fields () =
  let read_ev = make_test_event Read 1 in
  let write_ev = make_test_event Write 2 in
  let fence_ev = make_test_event Fence 3 in
  let branch_ev = make_test_event Branch 4 in
  let malloc_ev = make_test_event Malloc 5 in

  check bool "read has_id" true (Events.has_id read_ev);
  check bool "write has_id" true (Events.has_id write_ev);
  check bool "fence not has_id" false (Events.has_id fence_ev);

  check bool "read has_val" true (Events.has_val read_ev);
  check bool "fence not has_val" false (Events.has_val fence_ev);

  check bool "read has_rval" true (Events.has_rval read_ev);
  check bool "write not has_rval" false (Events.has_rval write_ev);

  check bool "write has_wval" true (Events.has_wval write_ev);
  check bool "read not has_wval" false (Events.has_wval read_ev);

  check bool "branch has_cond" true (Events.has_cond branch_ev);
  check bool "read not has_cond" false (Events.has_cond read_ev);

  check bool "malloc has_id" true (Events.has_id malloc_ev);
  check bool "malloc has_rval" true (Events.has_rval malloc_ev);
  check bool "malloc has_wval" true (Events.has_wval malloc_ev)

let test_get_fields () =
  let read_ev = make_read 1 "x" "v1" Relaxed in
  let write_ev = make_write 2 "y" "v2" Release in

  check bool "get_id read" true
    ( match Events.get_id read_ev with
    | VSymbol "x" -> true
    | _ -> false
    );
  check bool "get_rval read" true
    ( match Events.get_rval read_ev with
    | VSymbol "v1" -> true
    | _ -> false
    );
  check bool "get_id write" true
    ( match Events.get_id write_ev with
    | VSymbol "y" -> true
    | _ -> false
    );
  check bool "get_wval write" true
    ( match Events.get_wval write_ev with
    | ESymbol "v2" -> true
    | _ -> false
    );

  let fence_ev = make_test_event Fence 3 in
    check_raises "get_id on fence fails"
      (Failure "Event 3 type does not support id") (fun () ->
        Events.get_id fence_ev |> ignore
    )

let test_event_order () =
  let read_ev = make_read 1 "x" "v" Acquire in
  let write_ev = make_write 2 "y" "v" Release in
  let fence_ev = make_fence 3 SC in

  check bool "read order is acquire" true (Events.event_order read_ev = Acquire);
  check bool "write order is release" true
    (Events.event_order write_ev = Release);
  check bool "fence order is sc" true (Events.event_order fence_ev = SC)

(** Test event creation *)
let test_event_creation () =
  let e = Types.make_event Read 1 in
    check int "label is 1" 1 e.label;
    check int "van equals label" 1 e.van;
    check bool "type is read" true (e.typ = Read);
    check bool "id is none" true (e.id = None);
    check bool "default rmod is relaxed" true (e.rmod = Relaxed)

let test_fence_creation () =
  let e =
    Events.make_event_with Fence 1 ~id:None ~rval:None ~wval:None ~rmod:None
      ~wmod:None ~fmod:(Some SC) ~cond:None ~volatile:false ~strong:None
      ~lhs:None ~rhs:None ~pc:None
  in
    check bool "fence rmod adjusted" true (e.rmod = Acquire);
    check bool "fence wmod adjusted" true (e.wmod = Release);
    check bool "fence fmod is sc" true (e.fmod = SC)

let test_malloc_creation () =
  let rval = VSymbol "α" in
  let e =
    Events.make_event_with Malloc 1 ~id:None ~rval:(Some rval)
      ~wval:(Some (ENum Z.one)) ~rmod:None ~wmod:None ~fmod:None ~cond:None
      ~volatile:false ~strong:None ~lhs:None ~rhs:None ~pc:None
  in
    check bool "malloc id set to rval" true
      ( match e.id with
      | Some (VSymbol "α") -> true
      | _ -> false
      )

let test_clone_event () =
  let e1 = make_read 1 "x" "v" Acquire in
    Printf.printf "Original event: %s\n" (Events.event_to_string e1);
    let e2 = Events.clone_event e1 in
      Printf.printf "Cloned event: %s\n" (Events.event_to_string e2);
      let result = Events.event_equal e1 e2 in
        Printf.printf "Events equal: %b\n" result;
        flush stdout;
        check bool "cloned event equals original" true (Events.event_equal e1 e2);
        check bool "cloned event same label" true (e1.label = e2.label)

(** Test event to string *)
let test_event_to_string () =
  let read_rlx = make_read 1 "x" "v1" Relaxed in
  let read_acq = make_read 2 "x" "v2" Acquire in
  let write_rel = make_write 3 "y" "v3" Release in
  let fence_sc = make_fence 4 SC in

  check string "read relaxed" "1: R x v1" (Events.event_to_string read_rlx);
  check string "read acquire" "2: Racq x v2" (Events.event_to_string read_acq);
  check string "write release" "3: Wrel y v3" (Events.event_to_string write_rel);
  check string "fence sc" "4: Fsc" (Events.event_to_string fence_sc);

  let volatile_read = { read_rlx with volatile = true } in
    check string "volatile read" "1: vR x v1"
      (Events.event_to_string volatile_read)

let test_rmw_to_string () =
  let rmw = make_rmw 1 "x" "v1" "v2" Acquire Release in
  let s = Events.event_to_string rmw in
    check bool "rmw contains id" true (String.contains s 'x');
    check bool "rmw contains R" true (String.contains s 'R');
    check bool "rmw contains W" true (String.contains s 'W')

(** Test value equality *)
let test_value_equality () =
  let v1 = VNumber Z.one in
  let v2 = VNumber Z.one in
  let v3 = VNumber Z.zero in
  let v4 = VSymbol "α" in
  let v5 = VSymbol "α" in
  let v6 = VSymbol "β" in

  check bool "equal numbers" true (Value.equal v1 v2);
  check bool "unequal numbers" false (Value.equal v1 v3);
  check bool "equal symbols" true (Value.equal v4 v5);
  check bool "unequal symbols" false (Value.equal v4 v6);
  check bool "number not equal symbol" false (Value.equal v1 v4)

let test_event_equality () =
  let e1 = make_read 1 "x" "v" Relaxed in
  let e2 = make_read 1 "x" "v" Relaxed in
  let e3 = make_read 1 "y" "v" Relaxed in
  let e4 = make_read 2 "x" "v" Relaxed in

  check bool "equal events" true (Events.event_equal e1 e2);
  check bool "different id" false (Events.event_equal e1 e3);
  check bool "different label" false (Events.event_equal e1 e4)

(** Test EventsContainer *)
let test_container_create () =
  let c = Events.EventsContainer.create () in
    check int "initial next_label" 1 c.next_label;
    check int "initial next_van" 1 c.next_van

let test_container_add () =
  let c = Events.EventsContainer.create () in
  let e1 = make_test_event Read 0 in
  let e1' = Events.EventsContainer.add c e1 in

  check int "auto assigned label" 1 e1'.label;
  check int "auto assigned van" 1 e1'.van;
  check int "next_label incremented" 2 c.next_label;
  check int "next_van incremented" 2 c.next_van;

  let e2 = make_test_event Write 0 in
  let e2' = Events.EventsContainer.add c ~label:10 e2 in
    check int "explicit label" 10 e2'.label;
    check int "next_label updated" 11 c.next_label

let test_container_get () =
  let c = Events.EventsContainer.create () in
  let e = make_test_event Read 0 in
  let e' = Events.EventsContainer.add c e in

  match Events.EventsContainer.get c e'.label with
  | Some retrieved ->
      check bool "retrieved event matches" true (Events.event_equal e' retrieved)
  | None -> fail "event not found"

let test_container_all () =
  let c = Events.EventsContainer.create () in
  let _ = Events.EventsContainer.add c (make_test_event Read 0) in
  let _ = Events.EventsContainer.add c (make_test_event Write 0) in
  let _ = Events.EventsContainer.add c (make_test_event Fence 0) in

  let all = Events.EventsContainer.all c in
    check int "all returns 3 events" 3 (Uset.size all)

let test_container_map_filter () =
  let c = Events.EventsContainer.create () in
  let e1 = Events.EventsContainer.add c (make_read 0 "x" "v1" Relaxed) in
  let _e2 = Events.EventsContainer.add c (make_write 0 "y" "v2" Release) in
  let e3 = Events.EventsContainer.add c (make_read 0 "z" "v3" Acquire) in
  let _e4 = Events.EventsContainer.add c (make_fence 0 SC) in

  let all_labels = Events.EventsContainer.all c in

  (* Filter only reads *)
  let reads = Events.EventsContainer.map c all_labels ~typ:Read () in
    check int "map finds 2 reads" 2 (Uset.size reads);
    check bool "contains e1" true (Uset.mem reads e1.label);
    check bool "contains e3" true (Uset.mem reads e3.label);

    (* Filter only writes *)
    let writes = Events.EventsContainer.map c all_labels ~typ:Write () in
      check int "map finds 1 write" 1 (Uset.size writes);

      (* Filter by mode *)
      let acquire_events =
        Events.EventsContainer.map c all_labels ~mode:Acquire ()
      in
        check int "map finds 1 acquire" 1 (Uset.size acquire_events);

        (* Filter by mode with ordering *)
        let relaxed_or_higher =
          Events.EventsContainer.map c all_labels ~mode:Relaxed ~mode_op:">" ()
        in
          check bool "relaxed or higher includes all" true
            (Uset.size relaxed_or_higher >= 3)

let test_container_clone () =
  let c1 = Events.EventsContainer.create () in
  let _ = Events.EventsContainer.add c1 (make_test_event Read 0) in
  let _ = Events.EventsContainer.add c1 (make_test_event Write 0) in

  let c2 = Events.EventsContainer.clone c1 in
    check int "cloned size matches"
      (Uset.size (Events.EventsContainer.all c1))
      (Uset.size (Events.EventsContainer.all c2));
    check int "cloned next_label matches" c1.next_label c2.next_label;

    (* Add to original, shouldn't affect clone *)
    let _ = Events.EventsContainer.add c1 (make_test_event Fence 0) in
      check bool "clone unaffected by add" true
        (Uset.size (Events.EventsContainer.all c1)
        > Uset.size (Events.EventsContainer.all c2)
        )

let test_container_rewrite () =
  let c = Events.EventsContainer.create () in
  let e = Events.EventsContainer.add c (make_read 0 "x" "v1" Relaxed) in
  let new_e = make_read e.label "y" "v2" Acquire in

  let _ = Events.EventsContainer.rewrite c e.label new_e in

  match Events.EventsContainer.get c e.label with
  | Some retrieved ->
      check bool "rewritten event has new id" true
        ( match Events.get_id retrieved with
        | VSymbol "y" -> true
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
      test_case "value_equality" `Quick test_value_equality;
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
