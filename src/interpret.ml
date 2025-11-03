(** Program interpreter *)

open Lwt.Syntax
open Types
open Expr
open Ir

(** Event counter *)
let event_counter = ref 0

let next_event_id () =
  incr event_counter;
  !event_counter

(** Symbol generators *)
let greek_counter = ref 0

let next_greek () =
  let idx = !greek_counter mod (String.length greek_alpha / 2) in
  let suffix = !greek_counter / String.length greek_alpha in
    (* divide by byte length *)
    incr greek_counter;
    (* Greek characters are 2 bytes in UTF-8 *)
    let base = String.sub greek_alpha (idx * 2) 2 in
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

let create_events () = { events = Hashtbl.create 256; label = 0; van = 0 }

let add_event (events : events_t) event =
  let lbl = events.label in
    Printf.printf "Adding event with label %d\n" lbl;
    events.label <- events.label + 1;
    let v = events.van in
      events.van <- events.van + 1;
      let event' : event = { event with label = lbl; van = v } in
        Hashtbl.add events.events lbl event';
        event'

(** Symbolic Event Structure builders *)
let dot label structure phi : symbolic_event_structure =
  Printf.printf "Dotting event %d to structure\n" label;
  {
    e = Uset.union structure.e (Uset.singleton label);
    po = Uset.union structure.po (Uset.map (fun e -> (label, e)) structure.e);
    rmw = structure.rmw;
    lo = structure.lo;
    restrict = structure.restrict;
    cas_groups = structure.cas_groups;
    pwg = structure.pwg;
    fj = structure.fj;
    p = structure.p;
    constraint_ = structure.constraint_;
  }

let plus a b : symbolic_event_structure =
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

let cross a b : symbolic_event_structure =
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
let empty_structure () : symbolic_event_structure =
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

let update_env (env : (string, expr) Hashtbl.t) (register : string) (expr : expr)
    =
  let regexpr : expr = Expr.evaluate expr (Hashtbl.find_opt env) in
  let env' = Hashtbl.copy env in
    Hashtbl.replace env' register regexpr;
    env'

(* TODO handle labels *)
(* TODO check id makes sense here *)
(* TODO step counter *)

(** Interpret IR - create symbolic event structures *)

let rec interpret_statements (stmts : ir_stmt list) env phi events =
  match stmts with
  | [] ->
      Printf.printf "End of program.\n";
      Lwt.return (empty_structure ())
  | stmt :: rest ->
      Printf.printf "Interpreting statement: %s\n" (Ir.to_string stmt);
      flush stdout;
      let* structure =
        match stmt with
        | Threads { threads } ->
            let interpret_threads ts =
              List.fold_left
                (fun acc t ->
                  let* t_structure = interpret_statements t env phi events in
                    let* acc_structure = acc in
                      Lwt.return (cross acc_structure t_structure)
                )
                (Lwt.return (empty_structure ()))
                ts
            in
              interpret_threads threads
        | RegisterStore { register; expr } ->
            let env' = update_env env register expr in
              let* cont = interpret_statements rest env' phi events in
                Lwt.return cont
        | GlobalStore { global; expr; assign } ->
            let base_evt : event = make_event Write 0 in
            let evt =
              {
                base_evt with
                id = Some (VVar global);
                loc = Some (EVar global);
                wval = Some (Expr.evaluate expr (Hashtbl.find_opt env));
                wmod = assign.mode;
                volatile = assign.volatile;
              }
            in
            let event' = add_event events evt in
              let* cont = interpret_statements rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | DerefStore { address; expr; assign } ->
            let base_evt : event = make_event Write 0 in
            let evt =
              {
                base_evt with
                loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                wval = Some (Expr.evaluate expr (Hashtbl.find_opt env));
                wmod = assign.mode;
                volatile = assign.volatile;
              }
            in
            let event' = add_event events evt in
              let* cont = interpret_statements rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | GlobalLoad { register; global; load } ->
            let rval = VSymbol (next_greek ()) in
            let base_evt : event = make_event Read 0 in
            let evt =
              {
                base_evt with
                id = Some (VVar global);
                loc = Some (EVar global);
                rval = Some rval;
                rmod = load.mode;
                volatile = load.volatile;
              }
            in
            let event' = add_event events evt in
            let env' = Hashtbl.copy env in
              Hashtbl.replace env' register (Expr.of_value rval);
              let* cont = interpret_statements rest env' phi events in
                Lwt.return (dot event'.label cont phi)
        | If { condition; then_body; else_body } -> (
            let cond_val = Expr.evaluate condition (Hashtbl.find_opt env) in
              let* then_structure =
                interpret_statements then_body env (cond_val :: phi) events
              in
                match else_body with
                | Some eb ->
                    let* else_structure =
                      interpret_statements eb env
                        (Expr.unop "~" cond_val :: phi)
                        events
                    in
                      Lwt.return (plus then_structure else_structure)
                | None -> Lwt.return then_structure
          )
        (* | `While (condition, body) ->
          (* Simplified - ignore loops for now *)
          Lwt.return (empty_structure ()) *)
        (* | `Do (body, condition) ->
          (* Simplified - ignore loops for now *)
          Lwt.return (empty_structure ()) *)
        | Fence { mode } ->
            let base_evt : event = make_event Fence 0 in
            let evt = { base_evt with fmod = mode } in
            let event' = add_event events evt in
              let* cont = interpret_statements rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Lock { global } ->
            let base_evt : event = make_event Lock 0 in
            let evt =
              match global with
              | Some g -> { base_evt with id = Some (VVar g) }
              | None -> base_evt
            in
            let event' = add_event events evt in
              let* cont = interpret_statements rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Unlock { global } ->
            let base_evt : event = make_event Unlock 0 in
            let evt =
              match global with
              | Some g -> { base_evt with id = Some (VVar g) }
              | None -> base_evt
            in
            let event' = add_event events evt in
              let* cont = interpret_statements rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Malloc { register; size } ->
            let rval = VSymbol (next_zh ()) in
            let base_evt : event = make_event Malloc 0 in
            let evt = { base_evt with rval = Some rval } in
            let event' = add_event events evt in
            let env' = Hashtbl.copy env in
              Hashtbl.replace env' register (Expr.of_value rval);
              let* cont = interpret_statements rest env' phi events in
                Lwt.return (dot event'.label cont phi)
        | Free { register } ->
            let base_evt : event = make_event Free 0 in
            let evt = base_evt in
            let event' = add_event events evt in
              let* cont = interpret_statements rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Labeled { label; stmt } ->
            (* TODO *)
            Printf.printf "[WARN] Labeled event\n";
            let* structure = interpret_statements [ stmt ] env phi events in
              Lwt.return structure
        | _ ->
            (* Simplified - return empty structure for unhandled cases *)
            Printf.printf
              "[ERROR] Statement not handled %s, returning empty structure.\n"
              (Ir.to_string stmt);
            flush stdout;
            Lwt.return (empty_structure ())
      in
        Lwt.return structure

(** Main interpret function *)
let interpret ast defacto restrictions constraint_ =
  let events = create_events () in
  let env = Hashtbl.create 32 in

  let init_event = make_event Init 0 in
  let init_event' = add_event events { (make_event Init 4) with label = 0 } in

  let* structure = interpret_statements ast env [] events in
  let structure' = dot init_event'.label structure [] in

  Lwt.return (structure', events.events)
