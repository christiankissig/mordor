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

(** Labels count from zero *)
let test_next_label () =
  let alloc = Allocator.create () in
  let l1 = Allocator.next_label alloc in
  let l2 = Allocator.next_label alloc in
  let l3 = Allocator.next_label alloc in
    Alcotest.(check int) "first label" 0 l1;
    Alcotest.(check int) "second label" 1 l2;
    Alcotest.(check int) "third label" 2 l3

(** Test Greek symbol generation *)
let test_next_greek () =
  let alloc = Allocator.create () in
  let g1 = Allocator.next_greek alloc in
  let g2 = Allocator.next_greek alloc in
    Alcotest.(check string) "first greek symbol" "α" g1;
    Alcotest.(check string) "second greek symbol" "β" g2

let test_next_greek_overflow () =
  let alloc = Allocator.create () in
    (* Generate more symbols than in the alphabet to test suffix *)
    for _i = 1 to String.length greek_alpha do
      let _ = Allocator.next_greek alloc in
        ()
    done;
    let overflow = Allocator.next_greek alloc in
      Alcotest.(check string) "greek with suffix" "α2" overflow

(** Test Chinese symbol generation *)
let test_next_zh () =
  let alloc = Allocator.create () in
  let z1 = Allocator.next_zh alloc in
  let z2 = Allocator.next_zh alloc in
    Alcotest.(check bool) "first zh is string" true (String.length z1 > 0);
    Alcotest.(check bool) "second zh is string" true (String.length z2 > 0);
    Alcotest.(check bool) "zh symbols differ" true (z1 <> z2)

(** Two allocators share nothing: what one hands out does not move the other,
    which is what lets an interpretation, and later a fragment, own one. *)
let test_allocators_are_independent () =
  let a = Allocator.create () and b = Allocator.create () in
    ignore (Allocator.next_label a, Allocator.next_greek a, Allocator.next_zh a);
    Alcotest.(check int) "b's labels start at 0" 0 (Allocator.next_label b);
    Alcotest.(check string) "b's greek starts at α" "α" (Allocator.next_greek b);
    Alcotest.(check string) "b's zh starts at 一" "一" (Allocator.next_zh b)

(** Test events collection creation *)
let test_create_events () =
  let events = create_events [] in
    Alcotest.(check int) "events table is empty" 0 (Hashtbl.length events.events);
    Alcotest.(check int) "first label is 0" 0 (Allocator.next_label events.alloc)

(** Test adding events *)
let test_add_event () =
  let events = create_events [] in
  let evt = Event.create Read 0 () in
  let env = Hashtbl.create 16 in
  let added_evt =
    add_event events evt env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
    Alcotest.(check int) "event label assigned" 0 added_evt.label;
    Alcotest.(check int)
      "label counter incremented" 1
      (Allocator.next_label events.alloc);
    Alcotest.(check int) "event added to table" 1 (Hashtbl.length events.events)

let test_add_multiple_events () =
  let events = create_events [] in
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
    Alcotest.(check int) "empty p" 0 (Hashtbl.length s.p);
    Alcotest.(check int) "empty constraints" 0 (List.length s.constraints)

(** Test SymbolicEventStructure.dot operation *)
let test_dot () =
  let s = SymbolicEventStructure.create () in
  let s' = { s with e = USet.of_list [ 2; 3 ] } in
  let evt = Event.create Read 1 () in
  let result = SymbolicEventStructure.dot evt s' [] [] in
    Alcotest.(check bool) "event 1 in result" true (USet.mem result.e 1);
    Alcotest.(check bool) "event 2 in result" true (USet.mem result.e 2);
    Alcotest.(check bool) "event 3 in result" true (USet.mem result.e 3);
    Alcotest.(check int) "result has 3 events" 3 (USet.size result.e);
    (* Check po relations added *)
    Alcotest.(check bool) "po (1,2) exists" true (USet.mem result.po (1, 2));
    Alcotest.(check bool) "po (1,3) exists" true (USet.mem result.po (1, 3))

(** [dot] leaves its operand as it found it: the path condition and de facto
    constraints of the prefixed event go into the result's tables, not the
    operand's, so prefixing one structure twice gives two results that know
    nothing of each other. *)
let test_dot_leaves_operand_alone () =
  let s = { (SymbolicEventStructure.create ()) with e = USet.of_list [ 3 ] } in
  let phi = [ EBoolean true ] in
  let r1 = SymbolicEventStructure.dot (Event.create Read 1 ()) s phi phi in
  let r2 = SymbolicEventStructure.dot (Event.create Write 2 ()) s [] [] in
    Alcotest.(check int)
      "operand restrict untouched" 0
      (Hashtbl.length s.restrict);
    Alcotest.(check int) "operand defacto untouched" 0 (Hashtbl.length s.defacto);
    Alcotest.(check bool)
      "first result restricts 1" true
      (Hashtbl.find_opt r1.restrict 1 = Some phi);
    Alcotest.(check bool)
      "first result has defacto for 1" true
      (Hashtbl.find_opt r1.defacto 1 = Some phi);
    Alcotest.(check bool)
      "first result does not see 2" false
      (Hashtbl.mem r1.restrict 2 || Hashtbl.mem r1.defacto 2);
    Alcotest.(check bool)
      "second result does not see 1" false
      (Hashtbl.mem r2.restrict 1 || Hashtbl.mem r2.defacto 1)

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
      rmw = USet.of_list [ (1, EBoolean true, 3) ];
    }
  in
  let s2 =
    {
      (SymbolicEventStructure.create ()) with
      e = USet.of_list [ 4 ];
      po = USet.of_list [ (4, 5) ];
      rmw = USet.of_list [ (4, EBoolean true, 6) ];
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

(** A structure that owns its tables: one event [label], known to [events],
    [origin] (under [symbol]), [p], [restrict] and [defacto]. *)
let owned_structure label symbol =
  let s =
    { (SymbolicEventStructure.create ()) with e = USet.of_list [ label ] }
  in
    Hashtbl.replace s.events label (Event.create Read label ());
    Hashtbl.replace s.origin symbol label;
    Hashtbl.replace s.p label (Hashtbl.create 0);
    Hashtbl.replace s.restrict label [ EBoolean true ];
    Hashtbl.replace s.defacto label [];
    s

(** [plus] and [cross] merge their operands' tables rather than keeping the left
    one's: operands that own their tables come out with the union, in tables
    that are neither operand's, and the operands are left alone. *)
let test_combinators_merge_owned_tables () =
  List.iter
    (fun (name, combine) ->
      let a = owned_structure 1 "α" and b = owned_structure 2 "β" in
      let r : SymbolicEventStructure.t = combine a b in
      let has tbl k = Hashtbl.mem tbl k in
        Alcotest.(check bool)
          (name ^ ": events of both")
          true
          (has r.events 1 && has r.events 2);
        Alcotest.(check bool)
          (name ^ ": origins of both")
          true
          (has r.origin "α" && has r.origin "β");
        Alcotest.(check bool)
          (name ^ ": envs of both") true
          (has r.p 1 && has r.p 2);
        Alcotest.(check bool)
          (name ^ ": restrict of both")
          true
          (has r.restrict 1 && has r.restrict 2);
        Alcotest.(check bool)
          (name ^ ": defacto of both")
          true
          (has r.defacto 1 && has r.defacto 2);
        Alcotest.(check bool)
          (name ^ ": tables are fresh")
          true
          (r.events != a.events && r.origin != a.origin && r.p != a.p);
        Alcotest.(check bool)
          (name ^ ": operands untouched")
          false
          (has a.events 2 || has a.origin "β" || has a.p 2 || has b.events 1)
    )
    [
      ("plus", SymbolicEventStructure.plus);
      ("cross", SymbolicEventStructure.cross);
    ]

(** The case interpretation is in today: both operands hold the same tables.
    Merging a table with itself gives a copy of it and nothing more. *)
let test_combinators_merge_shared_tables () =
  let a = owned_structure 1 "α" in
  let b = { a with e = USet.of_list [ 2 ] } in
  let r = SymbolicEventStructure.plus a b in
    Alcotest.(check int) "one event, once" 1 (Hashtbl.length r.events);
    Alcotest.(check int) "one origin, once" 1 (Hashtbl.length r.origin);
    Alcotest.(check int) "one env, once" 1 (Hashtbl.length r.p)

(** Test interpret_statements with empty list *)
let test_interpret_empty_statements =
  run_lwt (fun () ->
      let env = Hashtbl.create 16 in
      let events = create_events [] in
      let result = interpret_statements [] env [] events in
        Alcotest.(check int) "only terminal event" 1 (USet.size result.e);
        Lwt.return_unit
  )

(** Test interpret GlobalStore statement *)
let test_interpret_global_store =
  run_lwt (fun () ->
      let env = Hashtbl.create 16 in
      let events = create_events [] in
      let mode = Types.SC in
      let expr = ENum Z.zero in
      let stmt =
        GlobalStore { global = "x"; expr; assign = { mode; volatile = false } }
      in
      let result = interpret_statements [ make_ir_node stmt ] env [] events in
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
      let env = Hashtbl.create 16 in
      let events = create_events [] in
      let mode = Types.SC in
      let stmt =
        GlobalLoad
          { register = "r"; global = "x"; load = { mode; volatile = false } }
      in
      let result = interpret_statements [ make_ir_node stmt ] env [] events in
        Alcotest.(check int) "one event created" 1 (USet.size result.e);
        Alcotest.(check bool) "register in env" true (Hashtbl.mem env "r");
        Lwt.return_unit
  )

(** Test interpret Fence statement *)
let test_interpret_fence =
  run_lwt (fun () ->
      let env = Hashtbl.create 16 in
      let events = create_events [] in
      let mode = Types.SC in
      let stmt = Ir.Fence { mode } in
      let result = interpret_statements [ make_ir_node stmt ] env [] events in
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
      let env = Hashtbl.create 16 in
      let events = create_events [] in
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
      let result = interpret_statements stmts env [] events in
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
      let structure, _ = interpret ast in
        Alcotest.(check int)
          "has init and store and terminal events" 3 (USet.size structure.e);
        Alcotest.(check bool) "init event present" true (USet.mem structure.e 0);
        (* includes terminal event *)
        Alcotest.(check int)
          "three events in table" 3
          (Hashtbl.length structure.events);
        Lwt.return_unit
  )

let test_interpret_main_with_po =
  run_lwt (fun () ->
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
      let structure, _ = interpret ast in
        Alcotest.(check int) "has four events" 4 (USet.size structure.e);
        (* Check that po relations exist *)
        Alcotest.(check bool) "po not empty" true (USet.size structure.po > 0);
        Lwt.return_unit
  )

(** {1 Symbolic loop semantics regression tests}

    Regression tests for the symbolic [while]-loop semantics. A while loop is
    modelled as a branch between "run the body once then continue" and "skip the
    body and continue". An earlier implementation shared a single continuation
    structure between both branches, so [plus] (which adds an all-pairs conflict
    between its operands) marked the shared continuation events as conflicting
    with themselves and with their po-predecessors. The resulting malformed
    event structure produced zero executions. *)

(** Run the pipeline up to interpretation with symbolic loop semantics and
    return the resulting event structure. *)
let interpret_symbolic program =
  let ctx =
    make_context { default_options with loop_semantics = Symbolic } ()
  in
    ctx.litmus <- Some program;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx |> Parse.step_parse_litmus |> Interpret.step_interpret)
    in
      Option.get ctx.structure

(** Run the full pipeline with symbolic loop semantics and return the number of
    generated executions. *)
let count_executions_symbolic program =
  let ctx =
    make_context { default_options with loop_semantics = Symbolic } ()
  in
    ctx.litmus <- Some program;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx
        |> Parse.step_parse_litmus
        |> Interpret.step_interpret
        |> Elaborations.step_generate_justifications
        |> Executions.step_calculate_dependencies
        )
    in
      USet.size (Option.get ctx.executions)

(** A well-formed event structure never has an event in conflict with itself,
    and conflict and program order are disjoint (conflicting events cannot be
    po-ordered). *)
let check_structure_wellformed name structure =
  let self_conflict =
    USet.values structure.conflict |> List.exists (fun (a, b) -> a = b)
  in
    Alcotest.(check bool) (name ^ ": no self-conflict") false self_conflict;
    Alcotest.(check int)
      (name ^ ": po and conflict are disjoint")
      0
      (USet.size (USet.intersection structure.po structure.conflict))

(* A structure describes the events that are in it, and no others.

   The interpreter creates a branch event before it knows whether the branch
   survives: a guard that folds to a constant is elided, and its event, already
   labelled and recorded, never enters the structure. While the structure was
   handed the interpreter's program-wide tables it described those events too,
   and [po_iter], built from [loop_indices], ordered them. This is
   branch_condition/nested_fail, whose loop came back with two members that
   were not events of the structure. *)
let test_structure_describes_its_events_only () =
  let structure =
    interpret_symbolic
      "x := 0; y := 1; rval := x; rtest := y; do { ri := 0; if (rval = 0) { if \
       (rtest = 1) { ri := 1; } } } while (ri = 0)"
  in
  let here label = USet.mem structure.e label in
  let keys_here name tbl =
    Alcotest.(check bool)
      (name ^ " binds events of the structure only")
      true
      (Hashtbl.fold (fun label _ acc -> acc && here label) tbl true)
  in
    keys_here "events" structure.events;
    keys_here "p" structure.p;
    keys_here "loop_indices" structure.loop_indices;
    keys_here "thread_index" structure.thread_index;
    Alcotest.(check bool)
      "origin names events of the structure only" true
      (Hashtbl.fold (fun _ label acc -> acc && here label) structure.origin true);
    Alcotest.(check int)
      "every event is described" (USet.size structure.e)
      (Hashtbl.length structure.events);
    Alcotest.(check bool)
      "po_iter orders events of the structure only" true
      (USet.for_all (fun (a, b) -> here a && here b) structure.po_iter)

(* A while loop whose guard reads a value updated by the body branches on a
   symbolic guard: both "enter" and "exit" branches are feasible. *)
let test_while_symbolic_guard_wellformed () =
  let structure =
    interpret_symbolic "x := 0; r1 := x; while (r1 = 0) { r1 := x }"
  in
    check_structure_wellformed "while symbolic guard" structure;
    Alcotest.(check bool)
      "has a branch event" true
      (USet.size structure.branch_events > 0)

let test_while_symbolic_guard_yields_executions () =
  Alcotest.(check bool)
    "while loop yields at least one execution" true
    (count_executions_symbolic "x := 0; r1 := x; while (r1 = 0) { r1 := x }" > 0)

(* A while loop whose guard is statically true on entry must enter the body; the
   exit branch is pruned, so no branch event is created, and it still yields an
   execution. *)
let test_while_constant_guard_yields_executions () =
  let program = "x := 0; r1 := 0; while (r1 = 0) { r1 := x }" in
  let structure = interpret_symbolic program in
    check_structure_wellformed "while constant guard" structure;
    Alcotest.(check bool)
      "constant-guard while loop yields at least one execution" true
      (count_executions_symbolic program > 0)

(** {1 Do-while loop semantics}

    [do { body } while (cond)] is [body] followed by [while (cond) { body }]:
    one unravelling of the loop body, then the residual while loop. An earlier
    implementation dropped the residual loop entirely (the continuation of the
    first unravelling was the program's terminal structure), so a do-while loop
    produced neither a branch event nor a loop condition. *)

let do_while_program = "x := 0; do { r1 := x } while (r1 = 0)"

(* [body; while (cond) { body }], the hand-unravelled equivalent of
   [do_while_program]. *)
let unravelled_while_program = "x := 0; r1 := x; while (r1 = 0) { r1 := x }"

let test_do_while_symbolic_guard_wellformed () =
  let structure = interpret_symbolic do_while_program in
    check_structure_wellformed "do-while symbolic guard" structure;
    Alcotest.(check int)
      "has one branch event" 1
      (USet.size structure.branch_events);
    Alcotest.(check bool)
      "tracks the loop condition" true
      (Hashtbl.length structure.loop_conditions > 0)

let test_do_while_yields_executions () =
  Alcotest.(check bool)
    "do-while loop yields at least one execution" true
    (count_executions_symbolic do_while_program > 0)

let sorted_bindings tbl =
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl [] |> List.sort compare

(* The whole point: the do-while structure is the structure of the
   hand-unravelled while loop. Event labels are allocated in the same order in
   both, so the relations compare literally. *)
let test_do_while_matches_unravelled_while () =
  let do_while = interpret_symbolic do_while_program in
  let unravelled = interpret_symbolic unravelled_while_program in
  let sorted set = USet.values set |> List.sort compare in
  let check_ints name f =
    Alcotest.(check int) name (USet.size (f unravelled)) (USet.size (f do_while))
  in
  let check_pairs name f =
    Alcotest.(check (list (pair int int)))
      name
      (sorted (f unravelled))
      (sorted (f do_while))
  in
    check_ints "same number of events" (fun s -> s.e);
    check_ints "same number of branch events" (fun s -> s.branch_events);
    check_ints "same number of terminal events" (fun s -> s.terminal_events);
    check_ints "same number of read events" (fun s -> s.read_events);
    check_ints "same number of write events" (fun s -> s.write_events);
    check_pairs "same program order" (fun s -> s.po);
    check_pairs "same conflict relation" (fun s -> s.conflict);
    Alcotest.(check (list (pair int (list int))))
      "same loop membership"
      (sorted_bindings unravelled.loop_indices)
      (sorted_bindings do_while.loop_indices)

(* The peeled first unravelling precedes the loop rather than belonging to it,
   exactly as in the hand-written [body; while (cond) { body }]. Only the
   residual loop's copy of the body is the loop's symbolic iteration, which is
   what [po_iter] and the episodicity checks assume. *)
let test_do_while_peeled_unravelling_is_outside_the_loop () =
  let in_a_loop structure =
    Hashtbl.fold
      (fun _ loops acc -> if loops = [] then acc else acc + 1)
      structure.loop_indices 0
  in
    Alcotest.(check int)
      "only the residual body belongs to the loop"
      (in_a_loop (interpret_symbolic unravelled_while_program))
      (in_a_loop (interpret_symbolic do_while_program))

(* [cross] hands the combined structure the thread fold's seed tables, and
   [interpret_generic] re-attaches the global ones afterwards. Leaving
   loop_conditions out of that re-attachment dropped every loop's guard as soon
   as a program had more than one thread, which silently emptied the write
   condition's last-iteration filter. *)
let test_loop_conditions_survive_threads () =
  let loop = "rtest := x; while (rtest = 0) { rtest := x }" in
  let single = interpret_symbolic ("x := 0; " ^ loop) in
  let threaded =
    interpret_symbolic ("x := 0; { " ^ loop ^ " } ||| { x := 1 }")
  in
    Alcotest.(check bool)
      "a single-threaded loop records its guard" true
      (Hashtbl.length single.loop_conditions > 0);
    Alcotest.(check int)
      "a second thread does not drop loop conditions"
      (Hashtbl.length single.loop_conditions)
      (Hashtbl.length threaded.loop_conditions)

(* The recorded guard is the one that decides whether the iteration just
   modelled is followed by another, so it is evaluated at the end of the body.
   Here the body assigns [r1 := 1], so no second iteration is possible and the
   guard is [false]. Taking it before the body instead would record [(α = 0)]
   over the pre-loop read, which says nothing about this iteration. *)
let test_loop_condition_is_taken_at_the_end_of_the_body () =
  let structure =
    interpret_symbolic
      "x := 0; y := 0; r1 := x; while (r1 = 0) { r2 := y; y := 1; r1 := 1 }"
  in
  let recorded =
    Hashtbl.find_opt structure.loop_conditions 1 |> Option.value ~default:[]
  in
    Alcotest.(check int) "one guard is recorded" 1 (List.length recorded);
    Alcotest.(check bool)
      "the loop cannot continue after its iteration" false
      (List.exists (fun guard -> Solver.is_sat [ guard ]) recorded)

(* A loop node is interpreted once per enclosing branch, and each occurrence
   reaches the end of the body in its own environment. Recording by
   [Hashtbl.replace] kept only whichever was interpreted last. Here the two
   branches leave [r2] at 0 and 1, so one occurrence can iterate again and the
   other cannot, and both have to survive. *)
let test_loop_conditions_are_recorded_per_occurrence () =
  let structure =
    interpret_symbolic
      "x := 0; r0 := x; if (r0 = 1) { r2 := 0 } else { r2 := 1 }; r1 := 0; \
       while (r1 = 0) { r1 := r2 }"
  in
  let recorded =
    Hashtbl.find_opt structure.loop_conditions 1 |> Option.value ~default:[]
  in
    Alcotest.(check int)
      "both occurrences of the loop are recorded" 2 (List.length recorded);
    Alcotest.(check int)
      "only the occurrence that iterates again can continue" 1
      (List.length (List.filter (fun guard -> Solver.is_sat [ guard ]) recorded))

(** {1 Globals and references} *)

(* [x := malloc n] is an allocation followed by a store of its address to x. The
   store was missing, so x never held the address. *)
let test_global_malloc_stores_the_address () =
  let structure = interpret_symbolic "p := malloc 1" in
  let events =
    Hashtbl.fold (fun _ (e : event) acc -> e :: acc) structure.events []
  in
  let alloc = List.find (fun (e : event) -> e.typ = Malloc) events in
  let store =
    List.find_opt
      (fun (e : event) ->
        e.typ = Write && e.loc = Some (EVar "p") && e.wval = alloc.loc
      )
      events
  in
    Alcotest.(check bool) "the address is stored to p" true (store <> None);
    Alcotest.(check bool)
      "after the allocation" true
      (USet.mem structure.po (alloc.label, (Option.get store).label))

(* A global reached only through a reference is as distinct from the others as
   one named by a load or a store. Forwarding and elaboration read these
   constraints, and without it a write through the reference could overwrite
   any global. *)
let test_referenced_global_is_distinct () =
  let structure = interpret_symbolic "x := 0; rq := &y; *rq := 1" in
    Alcotest.(check bool)
      "x != y" true
      (List.exists
         (Expr.equal (EBinOp (EVar "x", "!=", EVar "y")))
         structure.constraints
      )

(* Each thread is interpreted with labels of its own and relabelled into place.
   Labels still count up in program order with no gap or overlap, symbols are
   fresh across threads, and the threads of a nested block are numbered after
   the thread they are in. *)
let test_threads_relabelled_into_place () =
  let structure =
    interpret_symbolic
      "x := 0; { r1 := x; y := 1 } ||| { { r2 := y } ||| { z := 2 } }; w := 1"
  in
  let find typ loc =
    Hashtbl.fold
      (fun _ (e : event) acc ->
        if e.typ = typ && e.loc = Some (EVar loc) then Some e.label else acc
      )
      structure.events None
    |> Option.get
  in
  let accesses =
    [
      ("x := 0", find Write "x", 0);
      ("r1 := x", find Read "x", 1);
      ("y := 1", find Write "y", 1);
      ("r2 := y", find Read "y", 3);
      ("z := 2", find Write "z", 4);
      ("w := 1", find Write "w", 0);
    ]
  in
  let labels = List.map (fun (_, l, _) -> l) accesses in
  let read_symbol loc = (Hashtbl.find structure.events (find Read loc)).rval in
    Alcotest.(check bool)
      "the threads' reads are of different symbols" false
      (read_symbol "x" = read_symbol "y");
    Alcotest.(check (list int))
      "labels are dense"
      (List.init (USet.size structure.e) Fun.id)
      (USet.values structure.e |> List.sort compare);
    Alcotest.(check (list int))
      "labels follow program order" (List.sort compare labels) labels;
    List.iter
      (fun (name, label, thread) ->
        Alcotest.(check (option int))
          (name ^ " is in its thread")
          (Some thread)
          (Hashtbl.find_opt structure.thread_index label)
      )
      accesses

(** Test suite *)
let suite =
  ( "Interpreter",
    [
      Alcotest.test_case "Structure describes its events only" `Quick
        test_structure_describes_its_events_only;
      Alcotest.test_case "Threads are relabelled into place" `Quick
        test_threads_relabelled_into_place;
      Alcotest.test_case "While symbolic guard well-formed" `Quick
        test_while_symbolic_guard_wellformed;
      Alcotest.test_case "While symbolic guard yields executions" `Quick
        test_while_symbolic_guard_yields_executions;
      Alcotest.test_case "While constant guard yields executions" `Quick
        test_while_constant_guard_yields_executions;
      Alcotest.test_case "Do-while symbolic guard well-formed" `Quick
        test_do_while_symbolic_guard_wellformed;
      Alcotest.test_case "Do-while yields executions" `Quick
        test_do_while_yields_executions;
      Alcotest.test_case "Do-while matches unravelled while" `Quick
        test_do_while_matches_unravelled_while;
      Alcotest.test_case "Do-while peeled unravelling is outside the loop"
        `Quick test_do_while_peeled_unravelling_is_outside_the_loop;
      Alcotest.test_case "Loop conditions survive thread composition" `Quick
        test_loop_conditions_survive_threads;
      Alcotest.test_case "Loop condition is taken at the end of the body" `Quick
        test_loop_condition_is_taken_at_the_end_of_the_body;
      Alcotest.test_case "Loop conditions are recorded per occurrence" `Quick
        test_loop_conditions_are_recorded_per_occurrence;
      Alcotest.test_case "Global malloc stores the address" `Quick
        test_global_malloc_stores_the_address;
      Alcotest.test_case "Referenced global is distinct" `Quick
        test_referenced_global_is_distinct;
      Alcotest.test_case "Label generation" `Quick test_next_label;
      Alcotest.test_case "Allocators are independent" `Quick
        test_allocators_are_independent;
      Alcotest.test_case "Greek symbol generation" `Quick test_next_greek;
      Alcotest.test_case "Greek symbol overflow" `Quick test_next_greek_overflow;
      Alcotest.test_case "Chinese symbol generation" `Quick test_next_zh;
      Alcotest.test_case "Create events collection" `Quick test_create_events;
      Alcotest.test_case "Add single event" `Quick test_add_event;
      Alcotest.test_case "Add multiple events" `Quick test_add_multiple_events;
      Alcotest.test_case "Empty structure" `Quick test_empty_structure;
      Alcotest.test_case "Dot operation" `Quick test_dot;
      Alcotest.test_case "Dot leaves its operand alone" `Quick
        test_dot_leaves_operand_alone;
      Alcotest.test_case "Plus operation" `Quick test_plus;
      Alcotest.test_case "Plus with relations" `Quick test_plus_with_relations;
      Alcotest.test_case "Cross operation" `Quick test_cross;
      Alcotest.test_case "Combinators merge owned tables" `Quick
        test_combinators_merge_owned_tables;
      Alcotest.test_case "Combinators merge shared tables" `Quick
        test_combinators_merge_shared_tables;
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
