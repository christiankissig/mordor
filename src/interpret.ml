(** Program interpreter *)

open Context
open Events
open Expr
open Ir
open Lwt.Syntax
open Types
open Uset

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
    events.label <- events.label + 1;
    let v = events.van in
      events.van <- events.van + 1;
      let event' : event = { event with label = lbl; van = v } in
        Hashtbl.add events.events lbl event';
        event'

(** Symbolic Event Structure builders *)
let dot label structure phi : symbolic_event_structure =
  {
    e = USet.union structure.e (USet.singleton label);
    po = USet.union structure.po (USet.map (fun e -> (label, e)) structure.e);
    po_iter = USet.create ();
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
    e = USet.union a.e b.e;
    po = USet.union a.po b.po;
    po_iter = USet.create ();
    rmw = USet.union a.rmw b.rmw;
    lo = USet.union a.lo b.lo;
    restrict = a.restrict;
    (* Simplified merge *)
    cas_groups = a.cas_groups;
    pwg = a.pwg @ b.pwg;
    fj = USet.union a.fj b.fj;
    p = USet.union a.p b.p;
    constraint_ = a.constraint_ @ b.constraint_;
  }

let cross a b : symbolic_event_structure =
  {
    e = USet.union a.e b.e;
    po = USet.union a.po b.po;
    po_iter = USet.create ();
    rmw = USet.union a.rmw b.rmw;
    lo = USet.union a.lo b.lo;
    restrict = a.restrict;
    cas_groups = a.cas_groups;
    pwg = a.pwg @ b.pwg;
    fj = USet.union a.fj b.fj;
    p = USet.union a.p b.p;
    constraint_ = a.constraint_ @ b.constraint_;
  }

(** Create empty structure *)
let empty_structure () : symbolic_event_structure =
  {
    e = USet.create ();
    po = USet.create ();
    po_iter = USet.create ();
    rmw = USet.create ();
    lo = USet.create ();
    restrict = Hashtbl.create 16;
    cas_groups = Hashtbl.create 16;
    pwg = [];
    fj = USet.create ();
    p = USet.create ();
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

(** Interpret IR - create symbolic event structures *)

let interpret_statements_base ~recurse (stmts : ir_stmt list) env phi events =
  (* note that negative step counters are treated as infinite steps *)
  match stmts with
  | [] -> Lwt.return (empty_structure ())
  | stmt :: rest ->
      Logs.debug (fun m -> m "Interpreting statement: %s" (Ir.to_string stmt));
      let* structure =
        match stmt with
        | Threads { threads } ->
            let interpret_threads ts =
              List.fold_left
                (fun acc t ->
                  let* t_structure = recurse t env phi events in
                    let* acc_structure = acc in
                      Lwt.return (cross acc_structure t_structure)
                )
                (Lwt.return (empty_structure ()))
                ts
            in
              interpret_threads threads
        | RegisterStore { register; expr } ->
            let env' = update_env env register expr in
              let* cont = recurse rest env' phi events in
                Lwt.return cont
        | GlobalStore { global; expr; assign } ->
            let base_evt : event = Event.create Write 0 () in
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
              let* cont = recurse rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | DerefStore { address; expr; assign } ->
            let base_evt : event = Event.create Write 0 () in
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
              let* cont = recurse rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | DerefLoad { register; address; load } ->
            let rval = VSymbol (next_greek ()) in
            let base_evt : event = Event.create Read 0 () in
            let evt =
              {
                base_evt with
                loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                rval = Some rval;
                rmod = load.mode;
                volatile = load.volatile;
              }
            in
            let event' = add_event events evt in
            let env' = Hashtbl.copy env in
              Hashtbl.replace env' register (Expr.of_value rval);
              let* cont = recurse rest env' phi events in
                Lwt.return (dot event'.label cont phi)
        | GlobalLoad { register; global; load } ->
            let rval = VSymbol (next_greek ()) in
            let base_evt : event = Event.create Read 0 () in
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
              let* cont = recurse rest env' phi events in
                Lwt.return (dot event'.label cont phi)
        | If { condition; then_body; else_body } -> (
            let cond_val = Expr.evaluate condition (Hashtbl.find_opt env) in
              let* then_structure =
                recurse then_body env (cond_val :: phi) events
              in
                match else_body with
                | Some eb ->
                    let* else_structure =
                      recurse eb env (Expr.unop "~" cond_val :: phi) events
                    in
                      Lwt.return (plus then_structure else_structure)
                | None -> Lwt.return then_structure
          )
        | Fence { mode } ->
            let base_evt : event = Event.create Fence 0 () in
            let evt = { base_evt with fmod = mode } in
            let event' = add_event events evt in
              let* cont = recurse rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Lock { global } ->
            let base_evt : event = Event.create Lock 0 () in
            let evt =
              match global with
              | Some g -> { base_evt with id = Some (VVar g) }
              | None -> base_evt
            in
            let event' = add_event events evt in
              let* cont = recurse rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Unlock { global } ->
            let base_evt : event = Event.create Unlock 0 () in
            let evt =
              match global with
              | Some g -> { base_evt with id = Some (VVar g) }
              | None -> base_evt
            in
            let event' = add_event events evt in
              let* cont = recurse rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | Malloc { register; size } ->
            let rval = VSymbol (next_zh ()) in
            let base_evt : event = Event.create Malloc 0 () in
            let evt = { base_evt with rval = Some rval } in
            let event' = add_event events evt in
            let env' = Hashtbl.copy env in
              Hashtbl.replace env' register (Expr.of_value rval);
              let* cont = recurse rest env' phi events in
                Lwt.return (dot event'.label cont phi)
        | Free { register } ->
            let base_evt : event = Event.create Free 0 () in
            let evt = base_evt in
            let event' = add_event events evt in
              let* cont = recurse rest env phi events in
                Lwt.return (dot event'.label cont phi)
        | _ ->
            (* Simplified - return empty structure for unhandled cases *)
            Logs.err (fun m -> m "Statement not handled: %s" (Ir.to_string stmt));
            Lwt.return (empty_structure ())
      in
        Lwt.return structure

(** No interpretation of while statements *)

let rec interpret_statements stmts env phi events =
  interpret_statements_base ~recurse:interpret_statements stmts env phi events

(** Step-counter semantics of unbounded loops *)

let rec interpret_statements_step_counter step_counter stmts env phi events =
  if step_counter = 0 then Lwt.return (empty_structure ())
  else
    match stmts with
    | Do { body; condition } :: rest ->
        let unrolled =
          body
          @ If
              {
                condition;
                then_body = [ Do { body; condition } ];
                else_body = None;
              }
            :: rest
        in
          interpret_statements_step_counter (step_counter - 1) unrolled env phi
            events
    | While { condition; body } :: rest ->
        let unrolled =
          If
            {
              condition;
              then_body = body @ [ While { condition; body } ];
              else_body = None;
            }
          :: rest
        in
          interpret_statements_step_counter (step_counter - 1) unrolled env phi
            events
    | _ ->
        interpret_statements_base
          ~recurse:(interpret_statements_step_counter step_counter)
          stmts env phi events

(** Generic interpretation function **)

let interpret_generic ~stmt_semantics stmts defacto restrictions constraint_ =
  let events = create_events () in
  let env = Hashtbl.create 32 in

  let init_event = Event.create Init 0 () in
  let init_event' =
    add_event events { (Event.create Init 4 ()) with label = 0 }
  in

  let* structure = stmt_semantics stmts env [] events in
  (* prefix with init event *)
  let structure' = dot init_event'.label structure [] in

  Lwt.return (structure', events.events)

(** Default interpretation function **)

let interpret stmts env restrictions constraint_ =
  interpret_generic ~stmt_semantics:interpret_statements stmts env restrictions
    constraint_

(** Pipeline step for interpretation **)
let step_interpret (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match (ctx.program_stmts, ctx.litmus_constraints) with
    | Some stmts, Some constraints ->
        let* structure, events =
          interpret_generic ~stmt_semantics:interpret_statements stmts []
            (Hashtbl.create 16) []
        in
          ctx.structure <- Some structure;
          ctx.events <- Some events;
          Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "No program statements or constraints for interpretation."
        );
        Lwt.return ctx
