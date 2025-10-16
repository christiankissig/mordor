(** Program interpreter *)

open Lwt.Syntax
open Types

(** Event counter *)
let event_counter = ref 0

let next_event_id () =
  incr event_counter;
  !event_counter

(** Symbol generators *)
let greek_counter = ref 0

let next_greek () =
  let idx = !greek_counter mod String.length greek_alpha in
  let suffix = !greek_counter / String.length greek_alpha in
    incr greek_counter;
    let base = String.make 1 greek_alpha.[idx] in
      if suffix = 0 then base else base ^ string_of_int suffix

let zh_counter = ref 0

let next_zh () =
  let idx = !zh_counter mod (String.length zh_alpha / 3) in
    incr zh_counter;
    (* Chinese characters are 3 bytes in UTF-8 *)
    String.sub zh_alpha (idx * 3) 3

(** Events collection *)
type events_t = {
  events : (int, event) Hashtbl.t;
  mutable label : int;
  mutable van : int;
}

let create_events () = { events = Hashtbl.create 256; label = 1; van = 1 }

let add_event events event =
  let lbl = events.label in
    events.label <- events.label + 1;
    let v = events.van in
      events.van <- events.van + 1;
      let event' : event = { event with label = lbl; van = v } in
        Hashtbl.add events.events lbl event';
        event'

(** Symbolic Event Structure builders *)
let dot a b phi =
  {
    e = Uset.union b.e (Uset.singleton a);
    po = Uset.union b.po (Uset.map (fun e -> (a, e)) b.e);
    rmw = b.rmw;
    lo = b.lo;
    restrict = b.restrict;
    cas_groups = b.cas_groups;
    pwg = b.pwg;
    fj = b.fj;
    p = b.p;
    constraint_ = b.constraint_;
  }

let plus a b =
  {
    e = Uset.union a.e b.e;
    po = Uset.union a.po b.po;
    rmw = Uset.union a.rmw b.rmw;
    lo = Uset.union a.lo b.lo;
    restrict = a.restrict;
    (* Simplified merge *)
    cas_groups = a.cas_groups;
    pwg = a.pwg @ b.pwg;
    fj = Uset.union a.fj b.fj;
    p = Uset.union a.p b.p;
    constraint_ = a.constraint_ @ b.constraint_;
  }

let cross a b =
  {
    e = Uset.union a.e b.e;
    po = Uset.union a.po b.po;
    rmw = Uset.union a.rmw b.rmw;
    lo = Uset.union a.lo b.lo;
    restrict = a.restrict;
    cas_groups = a.cas_groups;
    pwg = a.pwg @ b.pwg;
    fj = Uset.union a.fj b.fj;
    p = Uset.union a.p b.p;
    constraint_ = a.constraint_ @ b.constraint_;
  }

(** Create empty structure *)
let empty_structure () =
  {
    e = Uset.create ();
    po = Uset.create ();
    rmw = Uset.create ();
    lo = Uset.create ();
    restrict = Hashtbl.create 16;
    cas_groups = Hashtbl.create 16;
    pwg = [];
    fj = Uset.create ();
    p = Uset.create ();
    constraint_ = [];
  }

(** Interpret statements *)
let rec interpret_statements stmts env phi events =
  match stmts with
  | [] -> Lwt.return (empty_structure ())
  | stmt :: rest ->
      let* structure = interpret_stmt stmt env phi events in
        let* rest_structure = interpret_statements rest env phi events in
          Lwt.return (plus structure rest_structure)

and interpret_stmt stmt env phi events =
  match stmt with
  | `GlobalStore (global, mode, expr, volatile) ->
      let base_evt : event = make_event Write 0 in
      let evt =
        {
          base_evt with
          id = Some (VVar global);
          wval = Some (VNumber Z.zero);
          (* Simplified *)
          wmod = mode;
          volatile;
        }
      in
      let event' = add_event events evt in
        let* cont = interpret_statements [] env phi events in
          Lwt.return (dot event'.label cont phi)
  | `GlobalLoad (register, global, mode, volatile) ->
      let rval = VSymbol (next_greek ()) in
      let base_evt : event = make_event Read 0 in
      let evt =
        {
          base_evt with
          id = Some (VVar global);
          rval = Some rval;
          rmod = mode;
          volatile;
        }
      in
      let event' = add_event events evt in
        Hashtbl.replace env register rval;
        let* cont = interpret_statements [] env phi events in
          Lwt.return (dot event'.label cont phi)
  | `Fence mode ->
      let base_evt : event = make_event Fence 0 in
      let evt = { base_evt with fmod = mode } in
      let event' = add_event events evt in
        let* cont = interpret_statements [] env phi events in
          Lwt.return (dot event'.label cont phi)
  | `Thread (lhs_stmts, rhs_stmts) ->
      let* lhs_structure = interpret_statements lhs_stmts env phi events in
        let* rhs_structure = interpret_statements rhs_stmts env phi events in
          Lwt.return (cross lhs_structure rhs_structure)
  | _ ->
      (* Simplified - return empty structure for unhandled cases *)
      Lwt.return (empty_structure ())

(** Main interpret function *)
let interpret ast defacto restrictions constraint_ =
  let events = create_events () in
  let env = Hashtbl.create 32 in

  let* structure = interpret_statements ast env [] events in

  (* Add init event *)
  let init_event = make_event Init 0 in
  let init_event' = add_event events { init_event with label = 0 } in

  let structure' =
    {
      structure with
      e = Uset.add structure.e 0;
      po = Uset.union structure.po (Uset.map (fun e -> (0, e)) structure.e);
    }
  in

  Lwt.return (structure', events.events)
