open Alcotest
open Eventstructures
open Executions_export
open Types
open Uset

(** Minimal test fixtures for the executions export module. *)
module TestData = struct
  let make_event ?(label = 0) ?(typ = Read) ?id ?loc ?rval ?wval ?cond
      ?(rmod = Relaxed) ?(wmod = Relaxed) ?(fmod = Relaxed) ?(volatile = false)
      ?(is_rdmw = false) () : event =
    {
      label;
      typ;
      id;
      loc;
      rval;
      wval;
      cond;
      rmod;
      wmod;
      fmod;
      volatile;
      strong = None;
      is_rdmw;
    }

  (** Build a tiny event structure with one init event, one write to [x], and
      one read of [x]. Two threads: init in thread 0, write in thread 1, read in
      thread 2. *)
  let make_structure () =
    let s = SymbolicEventStructure.create () in
    let e0 = make_event ~label:0 ~typ:Init () in
    let e1 =
      make_event ~label:1 ~typ:Write ~loc:(EVar "x")
        ~wval:(ENum (Z.of_int 1))
        ()
    in
    let e2 =
      make_event ~label:2 ~typ:Read ~loc:(EVar "x") ~rval:(VSymbol "α") ()
    in
      Hashtbl.add s.events 0 e0;
      Hashtbl.add s.events 1 e1;
      Hashtbl.add s.events 2 e2;
      Hashtbl.add s.thread_index 0 0;
      Hashtbl.add s.thread_index 1 1;
      Hashtbl.add s.thread_index 2 2;
      Hashtbl.add s.restrict 1 [ EBoolean true ];
      let s =
        {
          s with
          e = USet.of_list [ 0; 1; 2 ];
          po = USet.of_list [ (0, 1); (0, 2); (1, 2) ];
        }
      in
        s

  let make_execution ?(id = 0) ?(events = USet.of_list [ 0; 1; 2 ])
      ?(rf = USet.of_list [ (1, 2) ]) ?(dp = USet.create ())
      ?(ppo = USet.of_list [ (0, 1); (1, 2) ]) ?(rmw = USet.create ())
      ?(ex_p = []) () : symbolic_execution =
    {
      id;
      e = events;
      rf;
      dp;
      ppo;
      rmw;
      ex_p;
      fix_rf_map = Hashtbl.create 0;
      pointer_map = None;
      final_env = Hashtbl.create 0;
    }
end

let pair_testable = pair int int
let pair_list = list pair_testable

(** event_to_json fills the documented fields from the structure. *)
let test_event_to_json_write () =
  let s = TestData.make_structure () in
  let j = event_to_json s 1 in
    check string "type" "W" j.type_;
    check int "label" 1 j.label;
    check (option int) "thread" (Some 1) j.thread;
    check (option string) "location" (Some "x") j.location;
    check (option string) "wval" (Some "1") j.wval;
    check (option string) "rval" None j.rval;
    check bool "volatile" false j.volatile;
    check bool "is_rmw" false j.is_rmw;
    check (list string) "constraints" [ "true" ] j.constraints

let test_event_to_json_read () =
  let s = TestData.make_structure () in
  let j = event_to_json s 2 in
    check string "type" "R" j.type_;
    check (option string) "location" (Some "x") j.location;
    check (option string) "rval" (Some "α") j.rval;
    check (option string) "wval" None j.wval

(** execution_to_json filters PO to events in the execution and copies the other
    relations verbatim from the symbolic_execution record. *)
let test_execution_to_json_filters_po () =
  let s = TestData.make_structure () in
  let exec = TestData.make_execution ~events:(USet.of_list [ 1; 2 ]) () in
  let j = execution_to_json s exec in
    check int "exec id" 0 j.id;
    check int "event count" 2 (List.length j.events);
    (* PO must only contain pairs whose endpoints are in exec.e. *)
    check pair_list "po restricted to {1,2}" [ (1, 2) ] (List.sort compare j.po);
    check pair_list "rf" [ (1, 2) ] j.rf

let test_execution_to_json_relations () =
  let s = TestData.make_structure () in
  let exec =
    TestData.make_execution
      ~ppo:(USet.of_list [ (1, 2); (0, 2) ])
      ~dp:(USet.of_list [ (1, 2) ])
      ~rmw:(USet.create ()) ~ex_p:[ EBoolean true ] ()
  in
  let j = execution_to_json s exec in
    check pair_list "dp" [ (1, 2) ] j.dp;
    check pair_list "ppo" [ (0, 2); (1, 2) ] (List.sort compare j.ppo);
    check (list string) "predicates" [ "true" ] j.predicates

(** build_executions_document returns None until the pipeline has produced both
    a structure and an executions set. *)
let test_build_document_requires_structure_and_executions () =
  let s = TestData.make_structure () in
  let exec = TestData.make_execution () in
  let ctx =
    Context.make_context Context.default_options ~output_mode:Context.Json
      ~num_threads:1 ()
  in
    ctx.litmus_name <- "fixture";
    check bool "empty ctx returns None" true
      (build_executions_document ctx = None);
    ctx.structure <- Some s;
    check bool "structure alone returns None" true
      (build_executions_document ctx = None);
    ctx.executions <- Some (USet.of_list [ exec ]);
    match build_executions_document ctx with
    | Some doc ->
        check string "program" "fixture" doc.program;
        check int "executions" 1 (List.length doc.executions)
    | None -> fail "expected Some document"

(** to_json_string produces valid JSON that round-trips through Yojson. *)
let test_to_json_string_is_valid_json () =
  let s = TestData.make_structure () in
  let exec = TestData.make_execution () in
  let ctx =
    Context.make_context Context.default_options ~output_mode:Context.Json
      ~num_threads:1 ()
  in
    ctx.litmus_name <- "fixture";
    ctx.structure <- Some s;
    ctx.executions <- Some (USet.of_list [ exec ]);
    match to_json_string ctx with
    | None -> fail "expected JSON output"
    | Some content -> (
        let parsed = Yojson.Safe.from_string content in
          match parsed with
          | `Assoc fields ->
              check bool "has program field" true
                (List.mem_assoc "program" fields);
              check bool "has executions field" true
                (List.mem_assoc "executions" fields)
          | _ -> fail "expected JSON object at top level"
      )

let suite =
  ( "ExecutionsExport",
    [
      ("event_to_json write", `Quick, test_event_to_json_write);
      ("event_to_json read", `Quick, test_event_to_json_read);
      ("execution_to_json filters po", `Quick, test_execution_to_json_filters_po);
      ("execution_to_json relations", `Quick, test_execution_to_json_relations);
      ( "build_executions_document preconditions",
        `Quick,
        test_build_document_requires_structure_and_executions
      );
      ("to_json_string round-trips", `Quick, test_to_json_string_is_valid_json);
    ]
  )
