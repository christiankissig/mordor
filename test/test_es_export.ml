open Alcotest
open Types
open Uset

(** Tests for the event structure export ([interpret --output-mode json]). *)

let field k = function
  | `Assoc l -> List.assoc k l
  | _ -> failf "expected object when looking up %s" k

let as_list = function
  | `List l -> l
  | _ -> fail "expected JSON list"

(** A structure with an init event, a write to [x] and a read of [x]. *)
let structure () =
  let ev ~label ~typ ?loc ?rval ?wval () : event =
    {
      label;
      typ;
      id = None;
      loc;
      rval;
      wval;
      cond = None;
      rmod = Relaxed;
      wmod = Release;
      fmod = Relaxed;
      volatile = false;
      strong = None;
      is_rdmw = false;
    }
  in
  let s = Eventstructures.SymbolicEventStructure.create () in
    Hashtbl.add s.events 0 (ev ~label:0 ~typ:Init ());
    Hashtbl.add s.events 1
      (ev ~label:1 ~typ:Write ~loc:(EVar "x") ~wval:(ENum Z.one) ());
    Hashtbl.add s.events 2
      (ev ~label:2 ~typ:Read ~loc:(EVar "x") ~rval:(VSymbol "α") ());
    Hashtbl.add s.thread_index 1 1;
    Hashtbl.add s.thread_index 2 1;
    Hashtbl.add s.restrict 2 [ EBinOp (ESymbol "α", "=", ENum Z.one) ];
    Hashtbl.add s.origin "α" 2;
    {
      s with
      e = USet.of_list [ 0; 1; 2 ];
      po = USet.of_list [ (0, 1); (0, 2); (1, 2) ];
    }

let doc () =
  let ctx =
    Context.make_context Context.default_options ~output_mode:Context.Json
      ~num_threads:1 ()
  in
    ctx.litmus_name <- "fixture";
    ctx.structure <- Some (structure ());
    Es_export.to_json ctx

(** Events come sorted by id with their action, orders, thread and value
    restriction; po and the origins of symbols come along. *)
let test_events () =
  let s = field "structure" (doc ()) in
  let events = field "events" s |> as_list in
  let str k e = field k e |> Yojson.Safe.Util.to_string in
    check (list string) "types" [ "Init"; "W"; "R" ]
      (List.map (str "type") events);
    let w = List.nth events 1 and r = List.nth events 2 in
      check string "wmod" "rel" (str "wmod" w);
      check bool "loc" true (field "loc" w = `Assoc [ ("reg", `String "x") ]);
      check bool "rval" true (field "rval" r = `Assoc [ ("sym", `String "α") ]);
      check int "thread" 1 (field "thread" r |> Yojson.Safe.Util.to_int);
      check int "restrict" 1 (field "restrict" r |> as_list |> List.length);
      check int "po" 3 (field "po" s |> as_list |> List.length);
      check bool "origin" true (field "origin" s = `Assoc [ ("α", `Int 2) ])

(** Without a structure the document says so rather than failing. *)
let test_no_structure () =
  let ctx =
    Context.make_context Context.default_options ~output_mode:Context.Json
      ~num_threads:1 ()
  in
    check bool "null" true (field "structure" (Es_export.to_json ctx) = `Null)

let suite =
  ( "EsExport",
    [
      ("events", `Quick, test_events);
      ("no structure", `Quick, test_no_structure);
    ]
  )
