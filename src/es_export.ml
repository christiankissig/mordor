(** {1 Event Structure Export ([interpret --output-mode json])}

    Serialises the symbolic event structure the interpreter generated: every
    event with its action, memory orders, thread, loop iterations and value
    restriction, together with program order, the RMW triples and the origin of
    each symbol. Expressions use the expression grammar of the Isabelle
    interchange export ({!Isa_export.expr_json}), so that a program exported
    with [parse --output-mode isa] and its event structure share one encoding.

    Consumers compare event structures up to the renaming of event ids and
    symbols, for instance against another implementation of the semantics. *)

open Context
open Types
open Uset

let opt_json f = function
  | Some x -> f x
  | None -> `Null

let value_json (v : value_type) : Yojson.Safe.t =
  match v with
  | VNumber n -> `Assoc [ ("int", `Intlit (Z.to_string n)) ]
  | VSymbol s -> `Assoc [ ("sym", `String s) ]
  | VVar x -> `Assoc [ ("var", `String x) ]
  | VBoolean b -> `Assoc [ ("bool", `Bool b) ]

let type_string (t : event_type) : string =
  match t with
  | Read -> "R"
  | Write -> "W"
  | Malloc -> "Alloc"
  | Free -> "Dealloc"
  | Lock -> "Lock"
  | Unlock -> "Unlock"
  | Fence -> "Fence"
  | Branch -> "Branch"
  | Init -> "Init"
  | Terminal -> "Terminal"

let ints (l : int list) : Yojson.Safe.t = `List (List.map (fun i -> `Int i) l)
let find_list tbl k = Option.value (Hashtbl.find_opt tbl k) ~default:[]

let event_json (s : symbolic_event_structure) (id : int) (e : event) :
    Yojson.Safe.t =
  `Assoc
    [
      ("id", `Int id);
      ("type", `String (type_string e.typ));
      ("thread", opt_json (fun t -> `Int t) (Hashtbl.find_opt s.thread_index id));
      ("loc", opt_json Isa_export.expr_json e.loc);
      ("rval", opt_json value_json e.rval);
      ("wval", opt_json Isa_export.expr_json e.wval);
      ("cond", opt_json Isa_export.expr_json e.cond);
      ("alloc", opt_json value_json e.id);
      ("rmod", Isa_export.order_json e.rmod);
      ("wmod", Isa_export.order_json e.wmod);
      ("fmod", Isa_export.order_json e.fmod);
      ("volatile", `Bool e.volatile);
      ("is_rdmw", `Bool e.is_rdmw);
      ("loop_indices", ints (find_list s.loop_indices id));
      ( "restrict",
        `List (List.map Isa_export.expr_json (find_list s.restrict id))
      );
    ]

let pairs (r : (int * int) uset) : Yojson.Safe.t =
  `List
    (List.sort compare (USet.to_list r)
    |> List.map (fun (a, b) -> `List [ `Int a; `Int b ])
    )

let to_json (ctx : mordor_ctx) : Yojson.Safe.t =
  match ctx.structure with
  | None ->
      `Assoc [ ("program", `String ctx.litmus_name); ("structure", `Null) ]
  | Some s ->
      let ids = List.sort compare (USet.to_list s.e) in
      let events =
        List.filter_map
          (fun id -> Option.map (event_json s id) (Hashtbl.find_opt s.events id))
          ids
      in
      let rmw =
        List.sort compare (USet.to_list s.rmw)
        |> List.map (fun (r, c, w) ->
            `Assoc
              [ ("r", `Int r); ("cond", Isa_export.expr_json c); ("w", `Int w) ]
        )
      in
      let origin =
        Hashtbl.fold (fun sym ev acc -> (sym, `Int ev) :: acc) s.origin []
        |> List.sort compare
      in
        `Assoc
          [
            ("program", `String ctx.litmus_name);
            ( "structure",
              `Assoc
                [
                  ("events", `List events);
                  ("po", pairs s.po);
                  ("rmw", `List rmw);
                  ("origin", `Assoc origin);
                  ( "constraints",
                    `List (List.map Isa_export.expr_json s.constraints)
                  );
                ]
            );
          ]

let emit (ctx : mordor_ctx) : unit =
  let content = Yojson.Safe.pretty_to_string (to_json ctx) in
    ctx.output <- Some content;
    match ctx.output_file with
    | "stdout" ->
        print_string content;
        print_newline ();
        flush stdout
    | path ->
        let oc = open_out path in
          output_string oc content;
          close_out oc;
          Logs_safe.info (fun m -> m "Event structure JSON written to %s" path)
