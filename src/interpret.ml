(** Program interpreter *)

open Context
open Events
open Expr
open Ir
open Lwt.Syntax
open Types
open Uset

type ir_stmt = unit Ir.ir_stmt
type ir_node = unit Ir.ir_node

let ir_node_to_string = Ir.to_string ~ann_to_string:(fun () -> "")

(** Event counter *)
let event_counter = ref 0

let next_event_id () =
  incr event_counter;
  !event_counter

(** Symbol generators *)
let greek_counter = ref 0

let next_greek () =
  let num_greek_letters = String.length greek_alpha / 2 in
  (* 24 letters *)
  let idx = !greek_counter mod num_greek_letters in
  let suffix = !greek_counter / num_greek_letters in
    incr greek_counter;
    let base = String.sub greek_alpha (idx * 2) 2 in
      if suffix = 0 then base else base ^ string_of_int suffix

let zh_counter = ref 0

let next_zh () =
  let num_zh_chars = String.length zh_alpha / 3 in
  let idx = !zh_counter mod num_zh_chars in
  let suffix = !zh_counter / num_zh_chars in
    incr zh_counter;
    let base = String.sub zh_alpha (idx * 3) 3 in
      if suffix = 0 then base else base ^ string_of_int suffix

(** Events collection *)
type events_t = {
  (* events indexed by label *)
  events : (int, event) Hashtbl.t;
  (* origin mapping for symbols *)
  origin : (string, int) Hashtbl.t;
  mutable label : int;
  mutable van : int;
}

let create_events () =
  {
    events = Hashtbl.create 256;
    origin = Hashtbl.create 256;
    label = 0;
    van = 0;
  }

let add_event (events : events_t) event =
  let lbl = events.label in
    events.label <- events.label + 1;
    let v = events.van in
      events.van <- events.van + 1;
      let event' : event = { event with label = lbl; van = v } in
        Hashtbl.replace events.events lbl event';
        event'

(** Symbolic Event Structure builders *)
let dot (event : event) structure phi : symbolic_event_structure =
  if List.exists (fun p -> p = EBoolean false) phi then
    Logs.warn (fun m ->
        m "Adding event %d under unsatisfiable path condition.\n" event.label
    );
  Hashtbl.replace structure.restrict event.label phi;
  {
    e = USet.union structure.e (USet.singleton event.label);
    events = structure.events;
    po =
      USet.union structure.po (USet.map (fun e -> (event.label, e)) structure.e);
    po_iter = USet.create ();
    rmw = structure.rmw;
    lo = structure.lo;
    restrict = structure.restrict;
    cas_groups = structure.cas_groups;
    pwg = structure.pwg;
    fj = structure.fj;
    p = structure.p;
    constraint_ = structure.constraint_;
    conflict = structure.conflict;
    origin = structure.origin;
    write_events =
      ( if event.typ = Write then
          USet.union structure.write_events (USet.singleton event.label)
        else structure.write_events
      );
    read_events =
      ( if event.typ = Read then
          USet.union structure.read_events (USet.singleton event.label)
        else structure.read_events
      );
    rlx_write_events =
      ( if event.typ = Write && event.wmod = Relaxed then
          USet.union structure.rlx_write_events (USet.singleton event.label)
        else structure.rlx_write_events
      );
    rlx_read_events =
      ( if event.typ = Read && event.rmod = Relaxed then
          USet.union structure.rlx_read_events (USet.singleton event.label)
        else structure.rlx_read_events
      );
    fence_events =
      ( if event.typ = Fence then
          USet.union structure.fence_events (USet.singleton event.label)
        else structure.fence_events
      );
    branch_events =
      ( if event.typ = Branch then
          USet.union structure.branch_events (USet.singleton event.label)
        else structure.branch_events
      );
    malloc_events =
      ( if event.typ = Malloc then
          USet.union structure.malloc_events (USet.singleton event.label)
        else structure.malloc_events
      );
    free_events =
      ( if event.typ = Free then
          USet.union structure.free_events (USet.singleton event.label)
        else structure.free_events
      );
  }

let plus a b : symbolic_event_structure =
  let restrict = Hashtbl.copy a.restrict in
    Hashtbl.iter (fun k v -> Hashtbl.replace restrict k v) b.restrict;
    {
      e = USet.union a.e b.e;
      events = a.events;
      (* a and b share the same events table *)
      po = USet.union a.po b.po;
      po_iter = USet.create ();
      rmw = USet.union a.rmw b.rmw;
      lo = USet.union a.lo b.lo;
      restrict;
      cas_groups = a.cas_groups;
      pwg = a.pwg @ b.pwg;
      fj = USet.union a.fj b.fj;
      p = USet.union a.p b.p;
      constraint_ = a.constraint_ @ b.constraint_;
      conflict =
        USet.union (URelation.cross a.e b.e) (USet.union a.conflict b.conflict);
      (* a and b share the same origin table *)
      origin = a.origin;
      write_events = USet.union a.write_events b.write_events;
      read_events = USet.union a.read_events b.read_events;
      rlx_write_events = USet.union a.rlx_write_events b.rlx_write_events;
      rlx_read_events = USet.union a.rlx_read_events b.rlx_read_events;
      fence_events = USet.union a.fence_events b.fence_events;
      branch_events = USet.union a.branch_events b.branch_events;
      malloc_events = USet.union a.malloc_events b.malloc_events;
      free_events = USet.union a.free_events b.free_events;
    }

let cross a b : symbolic_event_structure =
  let restrict = Hashtbl.copy a.restrict in
    Hashtbl.iter (fun k v -> Hashtbl.replace restrict k v) b.restrict;
    {
      e = USet.union a.e b.e;
      events = a.events;
      (* a and b share the same events table *)
      po = USet.union a.po b.po;
      po_iter = USet.create ();
      rmw = USet.union a.rmw b.rmw;
      lo = USet.union a.lo b.lo;
      restrict;
      cas_groups = a.cas_groups;
      pwg = a.pwg @ b.pwg;
      fj = USet.union a.fj b.fj;
      p = USet.union a.p b.p;
      constraint_ = a.constraint_ @ b.constraint_;
      conflict = USet.union a.conflict b.conflict;
      (* a and b share the same origin table *)
      origin = a.origin;
      write_events = USet.union a.write_events b.write_events;
      read_events = USet.union a.read_events b.read_events;
      rlx_write_events = USet.union a.rlx_write_events b.rlx_write_events;
      rlx_read_events = USet.union a.rlx_read_events b.rlx_read_events;
      fence_events = USet.union a.fence_events b.fence_events;
      branch_events = USet.union a.branch_events b.branch_events;
      malloc_events = USet.union a.malloc_events b.malloc_events;
      free_events = USet.union a.free_events b.free_events;
    }

(** Create empty structure *)
let empty_structure () : symbolic_event_structure =
  {
    e = USet.create ();
    events = Hashtbl.create 256;
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
    conflict = USet.create ();
    origin = Hashtbl.create 16;
    write_events = USet.create ();
    read_events = USet.create ();
    rlx_write_events = USet.create ();
    rlx_read_events = USet.create ();
    fence_events = USet.create ();
    branch_events = USet.create ();
    malloc_events = USet.create ();
    free_events = USet.create ();
  }

let update_env (env : (string, expr) Hashtbl.t) (register : string) (expr : expr)
    =
  let regexpr : expr = Expr.evaluate expr (Hashtbl.find_opt env) in
  let env' = Hashtbl.copy env in
    Hashtbl.replace env' register regexpr;
    env'

(* TODO handle labels *)
(* TODO check id makes sense here *)

(** Interpretation of programs as lists of statements.

    Implemented in open recursion to allow for a flexible semantics of unbounded
    loops. Loop semantics added below. *)

let add_rmw_edge (structure : symbolic_event_structure) (er : int) (ew : int) =
  {
    structure with
    rmw = USet.add (structure : symbolic_event_structure).rmw (er, ew);
  }

let interpret_statements_open ~recurse ~add_event (nodes : ir_node list) env phi
    events =
  (* note that negative step counters are treated as infinite steps *)
  match nodes with
  | [] ->
      let structure = empty_structure () in
        Lwt.return
          { structure with events = events.events; origin = events.origin }
  | node :: rest ->
      let stmt = Ir.get_stmt node in
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
              let env' =
                update_env env register
                  (Expr.evaluate expr (Hashtbl.find_opt env))
              in
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
              let event' : event = add_event events evt in
                let* cont = recurse rest env phi events in
                  Lwt.return (dot event' cont phi)
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
              let event' : event = add_event events evt in
                let* cont = recurse rest env phi events in
                  Lwt.return (dot event' cont phi)
          | DerefLoad { register; address; load } ->
              let symbol = next_greek () in
              let rval = VSymbol symbol in
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
              let event' : event = add_event events evt in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return (dot event' cont phi)
          | GlobalLoad { register; global; load } ->
              let symbol = next_greek () in
              let rval = VSymbol symbol in
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
              let event' : event = add_event events evt in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return (dot event' cont phi)
          | Fadd { register; address; operand; load_mode; assign_mode } ->
              let symbol = next_greek () in
              let rval = VSymbol symbol in
              let base_evt_load : event = Event.create Read 0 () in
              let evt_load =
                {
                  base_evt_load with
                  loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                  rval = Some rval;
                  rmod = load_mode;
                  volatile = false;
                }
              in
              let event_load' : event = add_event events evt_load in
                Hashtbl.replace events.origin symbol event_load'.label;
                let loaded_expr = Expr.of_value (Option.get event_load'.rval) in
                let result_expr =
                  Expr.evaluate
                    (Expr.binop loaded_expr "+" operand)
                    (Hashtbl.find_opt env)
                in
                let base_evt_store : event = Event.create Write 0 () in
                let evt_store =
                  {
                    base_evt_store with
                    loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                    wval = Some result_expr;
                    wmod = assign_mode;
                    volatile = false;
                  }
                in
                let event_store' : event = add_event events evt_store in
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register result_expr;
                  let* cont = recurse rest env' phi events in
                    Lwt.return
                      (add_rmw_edge
                         (dot event_load' (dot event_store' cont phi) phi)
                         event_load'.label event_store'.label
                      )
          | Cas { register; address; expected; desired; load_mode; assign_mode }
            ->
              let symbol = next_greek () in
              let rval = VSymbol symbol in
              let base_evt_load : event = Event.create Read 0 () in
              let evt_load =
                {
                  base_evt_load with
                  loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                  rval = Some rval;
                  rmod = load_mode;
                  volatile = false;
                }
              in
              let event_load' : event = add_event events evt_load in
                Hashtbl.replace events.origin symbol event_load'.label;
                let loaded_expr = Expr.of_value (Option.get event_load'.rval) in
                let expected_expr =
                  Expr.evaluate expected (Hashtbl.find_opt env)
                in
                let cond_expr = Expr.binop loaded_expr "=" expected_expr in
                let base_evt_store : event = Event.create Write 0 () in
                let evt_store =
                  {
                    base_evt_store with
                    loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                    wval = Some (Expr.evaluate desired (Hashtbl.find_opt env));
                    wmod = assign_mode;
                    volatile = false;
                    cond = Some cond_expr;
                  }
                in
                let event_store' : event = add_event events evt_store in

                let phi_succ = cond_expr :: phi in
                let phi_fail = Expr.unop "!" cond_expr :: phi in
                let env_succ = Hashtbl.copy env in
                let env_fail = Hashtbl.copy env in
                  Hashtbl.replace env_succ register (EBoolean true);
                  Hashtbl.replace env_fail register (EBoolean false);
                  let* cont_succ = recurse rest env_succ phi_succ events in
                    let* cont_fail = recurse rest env_fail phi_fail events in
                      Lwt.return
                        (dot event_load'
                           (plus
                              (add_rmw_edge
                                 (dot event_store' cont_succ phi_succ)
                                 event_load'.label event_store'.label
                              )
                              cont_fail
                           )
                           phi
                        )
          | If { condition; then_body; else_body } -> (
              (* TODO prune semantically impossible branches against phi *)
              let cond_val = Expr.evaluate condition (Hashtbl.find_opt env) in
              let new_then_phi =
                if cond_val = EBoolean true then phi else cond_val :: phi
              in
              let new_else_phi =
                if cond_val = EBoolean false then phi
                else Expr.unop "!" cond_val :: phi
              in

              let then_structure events =
                recurse (then_body @ rest) env new_then_phi events
              in

              match else_body with
              | Some eb -> (
                  let else_structure events =
                    recurse (eb @ rest) env new_else_phi events
                  in

                  match cond_val with
                  | EBoolean true -> then_structure events
                  | EBoolean false -> else_structure events
                  | _ ->
                      let* then_structure = then_structure events in
                        let* else_structure = else_structure events in
                          Lwt.return (plus then_structure else_structure)
                )
              | None -> (
                  match cond_val with
                  | EBoolean false -> recurse rest env phi events
                  | EBoolean true -> then_structure events
                  | _ ->
                      let* then_structure = then_structure events in
                        let* rest_structure =
                          recurse rest env new_else_phi events
                        in
                          Lwt.return (plus then_structure rest_structure)
                )
            )
          | Fence { mode } ->
              let base_evt : event = Event.create Fence 0 () in
              let evt = { base_evt with fmod = mode } in
              let event' : event = add_event events evt in
                let* cont = recurse rest env phi events in
                  Lwt.return (dot event' cont phi)
          | Lock { global } ->
              let base_evt : event = Event.create Lock 0 () in
              let evt =
                match global with
                | Some g -> { base_evt with id = Some (VVar g) }
                | None -> base_evt
              in
              let event' : event = add_event events evt in
                let* cont = recurse rest env phi events in
                  Lwt.return (dot event' cont phi)
          | Unlock { global } ->
              let base_evt : event = Event.create Unlock 0 () in
              let evt =
                match global with
                | Some g -> { base_evt with id = Some (VVar g) }
                | None -> base_evt
              in
              let event' : event = add_event events evt in
                let* cont = recurse rest env phi events in
                  Lwt.return (dot event' cont phi)
          | Malloc { register; size } ->
              let symbol = next_zh () in
              let rval = VSymbol symbol in
              let base_evt : event = Event.create Malloc 0 () in
              let evt = { base_evt with rval = Some rval } in
              let event' : event = add_event events evt in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return (dot event' cont phi)
          | Free { register } ->
              let base_evt : event = Event.create Free 0 () in
              let evt = base_evt in
              let event' : event = add_event events evt in
                let* cont = recurse rest env phi events in
                  Lwt.return (dot event' cont phi)
          | _ ->
              (* Simplified - return empty structure for unhandled cases *)
              Logs.err (fun m ->
                  m "Statement not handled: %s" (ir_node_to_string node)
              );
              Lwt.return (empty_structure ())
        in
          Lwt.return structure

(** No interpretation of while statements *)

let rec interpret_statements stmts env phi events =
  interpret_statements_open ~recurse:interpret_statements ~add_event stmts env
    phi events

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
  let structure' = dot init_event' structure [] in
  let structure'' =
    { structure' with events = events.events; origin = events.origin }
  in

  Lwt.return (structure'', events.events)

(** Default interpretation function **)

let interpret stmts env restrictions constraint_ =
  interpret_generic ~stmt_semantics:interpret_statements stmts env restrictions
    constraint_

(** Pipeline step for interpretation **)
let generic_step_interpret ~stmt_semantics (lwt_ctx : mordor_ctx Lwt.t) :
    mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match (ctx.program_stmts, ctx.litmus_constraints) with
    | Some stmts, Some constraints ->
        let* structure, events =
          interpret_generic ~stmt_semantics stmts [] (Hashtbl.create 16) []
        in
          ctx.structure <- Some structure;
          ctx.events <- Some events;
          Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "No program statements or constraints for interpretation."
        );
        Lwt.return ctx

(** Step-counter semantics of unbounded loops

    The semantics of do- and while-loops is defined in terms of a fixed number
    of unrollings of the loop as nested if-statements. Per-loop step-counter
    leads to fixed number of unrollings per loop, and a global step-counter
    limiting unrollings across all sequential and nestested loops otherwise. The
    per-loop unrolling is applied before interpreting, while the global
    step-counter is applied during the interpretation. *)

module StepCounterSemantics : sig
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t
end = struct
  let make_ir_node stmt : ir_node = Ir.{ annotations = (); stmt }

  (* one-step unrolling *)

  let unrol_while_loop_once body condition =
    [
      make_ir_node
        (If
           {
             condition;
             then_body = body @ [ make_ir_node (While { condition; body }) ];
             else_body = None;
           }
        );
    ]

  let unrol_do_loop_once body condition =
    body
    @ [
        make_ir_node
          (If
             {
               condition;
               then_body = [ make_ir_node (Do { body; condition }) ];
               else_body = None;
             }
          );
      ]

  (* per loop step counter *)

  let rec unrol_while_loop body condition times =
    assert (times >= 0);
    if times = 0 then []
    else
      [
        make_ir_node
          (If
             {
               condition;
               then_body = body @ unrol_while_loop body condition (times - 1);
               else_body = None;
             }
          );
      ]

  let rec unrol_do_loop body condition times =
    assert (times >= 1);
    if times = 1 then body
    else
      body
      @ [
          make_ir_node
            (If
               {
                 condition;
                 then_body = unrol_do_loop body condition (times - 1);
                 else_body = None;
               }
            );
        ]

  let rec interpret_statements_step_counter step_counter per_loop nodes env phi
      events =
    assert (step_counter >= 0);
    if step_counter = 0 then Lwt.return (empty_structure ())
    else
      match nodes with
      | node :: rest -> (
          match get_stmt node with
          | Do { body; condition } ->
              if per_loop then
                let unrolled = unrol_do_loop body condition step_counter in
                  interpret_statements_step_counter step_counter per_loop
                    (unrolled @ rest) env phi events
              else
                let unrolled = unrol_do_loop_once body condition in
                  interpret_statements_step_counter (step_counter - 1) per_loop
                    (unrolled @ rest) env phi events
          | While { condition; body } ->
              if per_loop then
                let unrolled = unrol_while_loop body condition step_counter in
                  interpret_statements_step_counter step_counter per_loop
                    (unrolled @ rest) env phi events
              else
                let unrolled = unrol_while_loop_once body condition in
                  interpret_statements_step_counter (step_counter - 1) per_loop
                    (unrolled @ rest) env phi events
          | _ ->
              interpret_statements_open
                ~recurse:
                  (interpret_statements_step_counter step_counter per_loop)
                ~add_event nodes env phi events
        )
      | _ ->
          interpret_statements_open
            ~recurse:(interpret_statements_step_counter step_counter per_loop)
            ~add_event nodes env phi events

  let step_interpret lwt_ctx =
    let* ctx = lwt_ctx in
    let step_counter = ctx.step_counter in
    let per_loop = ctx.options.use_step_counter_per_loop in
      generic_step_interpret
        ~stmt_semantics:(interpret_statements_step_counter step_counter per_loop)
        lwt_ctx
end

module SymbolicLoopSemantics : sig
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t
end = struct
  let rec interpret_statements_symbolic_loop nodes env phi events =
    match nodes with
    | _ ->
        interpret_statements_open ~recurse:interpret_statements_symbolic_loop
          ~add_event nodes env phi events

  let step_interpret lwt_ctx =
    let* ctx = lwt_ctx in
      generic_step_interpret ~stmt_semantics:interpret_statements_symbolic_loop
        lwt_ctx
end

let step_interpret lwt_ctx =
  let* ctx = lwt_ctx in
    Logs.debug (fun m ->
        m "Interpreting program with %s loop semantics."
          ( if ctx.options.use_finite_step_counter_semantics then
              "finite step counter"
            else "generic"
          )
    );
    if ctx.options.use_finite_step_counter_semantics then
      StepCounterSemantics.step_interpret lwt_ctx
    else generic_step_interpret ~stmt_semantics:interpret_statements lwt_ctx
