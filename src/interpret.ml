(** Program interpreter *)

open Lwt.Syntax
open Types
open Expr

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
let dot a b phi : symbolic_event_structure =
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

(** Interpret statements *)
let rec interpret_statements stmts env phi events =
  match stmts with
  | [] -> Lwt.return (empty_structure ())
  | stmt :: rest ->
      let* structure = interpret_stmt stmt env phi events in
        let* rest_structure = interpret_statements rest env phi events in
          Lwt.return (plus structure rest_structure)

and interpret_stmt stmt env phi events =
  let* structure =
    match stmt with
    | `Threads threads ->
        let rec interpret_threads ts =
          match ts with
          | [] -> Lwt.return (empty_structure ())
          | t :: rest ->
              let* t_structure = interpret_statements t env phi events in
                let* rest_structure = interpret_threads rest in
                  Lwt.return (cross t_structure rest_structure)
        in
          interpret_threads threads
    | `RegisterStore (register, e) ->
        let expr = interpret_expr e env in
        let env' = update_env env register expr in
          let* cont = interpret_statements [] env' phi events in
            Lwt.return cont
    | `GlobalStore (global, e, (mode, volatile)) ->
        let expr = interpret_expr e env in
        let base_evt : event = make_event Write 0 in
        let evt =
          {
            base_evt with
            id = Some (VVar global);
            wval = Some (Expr.evaluate expr (Hashtbl.find_opt env));
            (* Simplified *)
            wmod = mode;
            volatile;
          }
        in
        let event' = add_event events evt in
          let* cont = interpret_statements [] env phi events in
            Lwt.return (dot event'.label cont phi)
    | `SStore (address, e, (mode, volatile)) ->
        let expr = interpret_expr e env in
        let base_evt : event = make_event Write 0 in
        let evt =
          {
            base_evt with
            loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
            wval = Some (Expr.evaluate expr (Hashtbl.find_opt env));
            wmod = mode;
            volatile;
          }
        in
        let event' = add_event events evt in
          let* cont = interpret_statements [] env phi events in
            Lwt.return (dot event'.label cont phi)
    | `GlobalLoad (register, global, (mode, volatile)) ->
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
        let env' = Hashtbl.copy env in
          Hashtbl.replace env' register (Expr.of_value rval);
          let* cont = interpret_statements [] env' phi events in
            Lwt.return (dot event'.label cont phi)
    | `If (cond, then_body, else_body_opt) -> (
        let condition = interpret_expr cond env in
        let cond_val = Expr.evaluate condition (Hashtbl.find_opt env) in
          let* then_structure =
            interpret_statements then_body env (cond_val :: phi) events
          in
            match else_body_opt with
            | Some else_body ->
                let* else_structure =
                  interpret_statements else_body env
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
    (* | `QDo (body, condition) ->
          (* Simplified - ignore loops for now *)
          Lwt.return (empty_structure ()) *)
    | `Fence mode ->
        let base_evt : event = make_event Fence 0 in
        let evt = { base_evt with fmod = mode } in
        let event' = add_event events evt in
          let* cont = interpret_statements [] env phi events in
            Lwt.return (dot event'.label cont phi)
    | `Lock global ->
        let base_evt : event = make_event Lock 0 in
        let evt =
          match global with
          | Some g -> { base_evt with id = Some (VVar g) }
          | None -> base_evt
        in
        let event' = add_event events evt in
          let* cont = interpret_statements [] env phi events in
            Lwt.return (dot event'.label cont phi)
    | `Unlock global ->
        let base_evt : event = make_event Unlock 0 in
        let evt =
          match global with
          | Some g -> { base_evt with id = Some (VVar g) }
          | None -> base_evt
        in
        let event' = add_event events evt in
          let* cont = interpret_statements [] env phi events in
            Lwt.return (dot event'.label cont phi)
        (* TODO | `Malloc (register, size, pc, label) ->
          let rval = VSymbol (next_zh ()) in
          let base_evt : event = make_event Malloc 0 in
          let evt =
            {
              base_evt with
              rval = Some rval;
              (* msize = Some (Expr.evaluate size (Hashtbl.find_opt env)); *)
              pc;
              label;
            }
          in
          let event' = add_event events evt in
          let env' = Hashtbl.copy env in
            Hashtbl.replace env' register (Expr.of_value rval);
            let* cont = interpret_statements [] env' phi events in
              Lwt.return (dot event'.label cont phi) *)
        (* TODO Free, Labeled *)
    | _ ->
        (* Simplified - return empty structure for unhandled cases *)
        Lwt.return (empty_structure ())
  in
    Lwt.return structure

and interpret_expr (e : Ast.ast_expr) env =
  match e with
  | Ast.EInt n -> Expr.num n
  | Ast.ERegister v ->
      Hashtbl.find_opt env v |> Option.value ~default:(Expr.var v)
  | Ast.EGlobal v -> Expr.var v
  | Ast.EBinOp (lhs, op, rhs) ->
      let lhs' = interpret_expr lhs env in
      let rhs' = interpret_expr rhs env in
        Expr.binop lhs' op rhs'
  | Ast.EUnOp (op, expr) ->
      let expr' = interpret_expr expr env in
        Expr.unop op expr'
  | _ -> failwith "Unhandled expression type in interpret_expr"

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
