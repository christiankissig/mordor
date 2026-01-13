(** Program interpreter *)

open Context
open Events
open Eventstructures
open Expr
open Lwt.Syntax
open Types
open Uset

let ir_node_to_string = Ir.to_string ~ann_to_string:(fun _ -> "")

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

(** Structure tracking events globally.

    This improves efficiency as events and symbols (and thus origins) are
    enumerated from the start of the program, but event structures are
    constructed from the end as continuations. Thus creating the event and
    origin tables at the end requires repeated merging. The last labels are
    anyways defined inductively from the start. *)
type events_t = {
  (* events indexed by label *)
  events : (int, event) Hashtbl.t;
  (* origin mapping for symbols *)
  origin : (string, int) Hashtbl.t;
  (* p tracks the register environment at each event label *)
  env_by_evt : (int, (string, expr) Hashtbl.t) Hashtbl.t;
  (* mapping from event labels to thread indices *)
  thread_index : (int, int) Hashtbl.t;
  (* mapping from event labels to loop indices *)
  loop_indices : (int, int list) Hashtbl.t;
  (* mapping from event labels to source spans *)
  source_spans : (int, source_span) Hashtbl.t;
  mutable label : int;
}

let create_events () =
  {
    events = Hashtbl.create 256;
    origin = Hashtbl.create 256;
    env_by_evt = Hashtbl.create 256;
    source_spans = Hashtbl.create 256;
    thread_index = Hashtbl.create 256;
    loop_indices = Hashtbl.create 256;
    label = 0;
  }

let add_event (events : events_t) event env (annotation : ir_node_ann) =
  let lbl = events.label in
    events.label <- events.label + 1;
    let event' : event = { event with label = lbl } in
      Hashtbl.replace events.events lbl event';
      Hashtbl.replace events.env_by_evt lbl (Hashtbl.copy env);
      ( match annotation.source_span with
      | Some span -> Hashtbl.replace events.source_spans lbl span
      | None -> ()
      );
      ( match annotation.thread_ctx with
      | Some thread_ctx ->
          Hashtbl.replace events.thread_index lbl thread_ctx.tid
      | None -> ()
      );
      ( match annotation.loop_ctx with
      | Some loop_ctx -> Hashtbl.replace events.loop_indices lbl loop_ctx.loops
      | None -> ()
      );
      event'

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

(** Interprets programs as lists of IR nodes depth-first using open recursion.

    The [recurse] argument is the interpretation function to use for recursive
    calls. The [add_event] argument is the function to use to add events to the
    global event table.

    The [env] argument is the current register environment mapping registers to
    expressions. The [phi] argument is the current path condition as a list of
    expressions. The [events] argument is the global events table being built.

    Returns a symbolic event structure representing the interpreted program
    fragment. *)
let interpret_statements_open ~recurse ~final_structure ~add_event
    (nodes : ir_node list) env phi events =
  (* note that negative step counters are treated as infinite steps *)
  match nodes with
  | [] -> final_structure ~add_event env phi events
  | node :: rest ->
      let stmt = Ir.get_stmt node in
      let annotation = node.annotations in
        let* structure =
          match stmt with
          | Threads { threads } ->
              let interpret_threads ts =
                List.fold_left
                  (fun acc t ->
                    let* t_structure = recurse t env phi events in
                      let* acc_structure = acc in
                        Lwt.return
                          (SymbolicEventStructure.cross acc_structure
                             t_structure
                          )
                  )
                  (Lwt.return (SymbolicEventStructure.create ()))
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
          | RegisterRefAssign { register; global } ->
              let env' = update_env env register (EVar global) in
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
              let event' : event = add_event events evt env annotation in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi)
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
              let event' : event = add_event events evt env annotation in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi)
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
              let event' : event = add_event events evt env annotation in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return (SymbolicEventStructure.dot event' cont phi)
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
              let event' : event = add_event events evt env annotation in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | Fadd
              { register; address; operand; rmw_mode; load_mode; assign_mode }
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
              let event_load' : event =
                add_event events evt_load env annotation
              in
                Hashtbl.replace events.origin symbol event_load'.label;
                let loaded_expr = Expr.of_value (Option.get event_load'.rval) in
                let result_expr =
                  Expr.evaluate
                    (Expr.binop loaded_expr "+" operand)
                    (Hashtbl.find_opt env)
                in
                let base_evt_store : event = Event.create Write 0 () in
                (* if the operand evaluates to zero, this is a read-don't
                   modify-write *)
                let is_rdmw =
                  Expr.evaluate operand (Hashtbl.find_opt env) == ENum Z.zero
                in
                let evt_store =
                  {
                    base_evt_store with
                    loc = Some (Expr.evaluate address (Hashtbl.find_opt env));
                    wval = Some result_expr;
                    wmod = assign_mode;
                    volatile = false;
                    is_rdmw;
                  }
                in
                let event_store' : event =
                  add_event events evt_store env annotation
                in
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register result_expr;
                  let* cont = recurse rest env' phi events in
                    Lwt.return
                      (add_rmw_edge
                         (SymbolicEventStructure.dot event_load'
                            (SymbolicEventStructure.dot event_store' cont phi)
                            phi
                         )
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
              let event_load' : event =
                add_event events evt_load env annotation
              in
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
                let event_store' : event =
                  add_event events evt_store env annotation
                in
                let phi_succ = cond_expr :: phi in
                let phi_fail = Expr.unop "!" cond_expr :: phi in
                let env_succ = Hashtbl.copy env in
                let env_fail = Hashtbl.copy env in
                  Hashtbl.replace env_succ register (EBoolean true);
                  Hashtbl.replace env_fail register (EBoolean false);
                  let* cont_succ = recurse rest env_succ phi_succ events in
                    let* cont_fail = recurse rest env_fail phi_fail events in
                      Lwt.return
                        (SymbolicEventStructure.dot event_load'
                           (SymbolicEventStructure.plus
                              (add_rmw_edge
                                 (SymbolicEventStructure.dot event_store'
                                    cont_succ phi_succ
                                 )
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
                          Lwt.return
                            (SymbolicEventStructure.plus then_structure
                               else_structure
                            )
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
                          Lwt.return
                            (SymbolicEventStructure.plus then_structure
                               rest_structure
                            )
                )
            )
          | Fence { mode } ->
              let base_evt : event = Event.create Fence 0 () in
              let evt = { base_evt with fmod = mode } in
              let event' : event = add_event events evt env annotation in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | Lock { global } ->
              let base_evt : event = Event.create Lock 0 () in
              let evt =
                match global with
                | Some g -> { base_evt with id = Some (VVar g) }
                | None -> base_evt
              in
              let event' : event = add_event events evt env annotation in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | Unlock { global } ->
              let base_evt : event = Event.create Unlock 0 () in
              let evt =
                match global with
                | Some g -> { base_evt with id = Some (VVar g) }
                | None -> base_evt
              in
              let event' : event = add_event events evt env annotation in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | RegMalloc { register; size } ->
              let symbol = next_zh () in
              let rval = VSymbol symbol in
              let loc = ESymbol symbol in
              let base_evt : event = Event.create Malloc 0 () in
              let evt = { base_evt with rval = Some rval; loc = Some loc } in
              let event' : event = add_event events evt env annotation in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | GlobalMalloc { global; size } ->
              let symbol = next_zh () in
              let rval = VSymbol symbol in
              let loc = ESymbol symbol in
              let base_evt : event = Event.create Malloc 0 () in
              let evt = { base_evt with rval = Some rval; loc = Some loc } in
              let event' : event = add_event events evt env annotation in
                Hashtbl.replace events.origin symbol event'.label;
                let env' = Hashtbl.copy env in
                  let* cont = recurse rest env' phi events in
                    Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | Free { register } ->
              let base_evt : event = Event.create Free 0 () in
              let loc = Hashtbl.find_opt env register in
              let evt = { base_evt with loc } in
              let event' : event = add_event events evt env annotation in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi)
          | Skip ->
              let* cont = recurse rest env phi events in
                Lwt.return cont
          | _ ->
              (* Simplified - return empty structure for unhandled cases *)
              Logs.err (fun m ->
                  m "Statement not handled: %s" (ir_node_to_string node)
              );
              Lwt.return (SymbolicEventStructure.create ())
        in
          Lwt.return structure

(** Generic terminal structure - creates a single terminal node *)

let make_generic_terminal_structure ~add_event env phi events =
  let structure = SymbolicEventStructure.create () in
  let terminal_evt = Event.create Terminal 0 () in
  let terminal_evt : event =
    add_event events terminal_evt env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
  let cont =
    {
      structure with
      events = events.events;
      origin = events.origin;
      loop_indices = events.loop_indices;
      thread_index = events.thread_index;
      p = events.env_by_evt;
    }
  in
    Lwt.return (SymbolicEventStructure.dot terminal_evt cont phi)

(** No interpretation of while statements *)

let rec interpret_statements stmts env phi events =
  interpret_statements_open ~recurse:interpret_statements
    ~final_structure:make_generic_terminal_structure ~add_event stmts env phi
    events

(** Generic interpretation function **)

let interpret_generic ~stmt_semantics stmts defacto restrictions constraint_ =
  let events = create_events () in
  let env = Hashtbl.create 32 in

  let init_event = Event.create Init 0 () in
  let init_event' =
    add_event events
      { (Event.create Init 4 ()) with label = 0 }
      env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in

  let* structure = stmt_semantics stmts env [] events in
  (* prefix with init event *)
  let structure' = SymbolicEventStructure.dot init_event' structure [] in
  let structure'' =
    {
      structure' with
      events = events.events;
      origin = events.origin;
      p = events.env_by_evt;
    }
  in

  Lwt.return (structure'', events.events, events.source_spans)

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
        let* structure, events, source_spans =
          interpret_generic ~stmt_semantics stmts [] (Hashtbl.create 16) []
        in
          ctx.structure <- Some structure;
          ctx.events <- Some events;
          ctx.source_spans <- Some source_spans;
          Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "No program statements or constraints for interpretation."
        );
        Lwt.return ctx

(** Finite step-counter semantics of unbounded loops

    The semantics of do- and while-loops is defined in terms of a fixed number
    of unrollings of the loop as nested if-statements. Per-loop step-counter
    leads to fixed number of unrollings per loop, and a global step-counter
    limiting unrollings across all sequential and nestested loops otherwise. The
    per-loop unrolling is applied before interpreting, while the global
    step-counter is applied during the interpretation. *)

module StepCounterSemantics : sig
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t

  val interpret :
    step_counter:int ->
    mordor_ctx Lwt.t ->
    (symbolic_event_structure * (int, source_span) Hashtbl.t) Lwt.t
end = struct
  let make_ir_node stmt : ir_node =
    Ir.
      {
        annotations = { source_span = None; thread_ctx = None; loop_ctx = None };
        stmt;
      }

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
    if step_counter = 0 then Lwt.return (SymbolicEventStructure.create ())
    else
      match nodes with
      | node :: rest -> (
          match Ir.get_stmt node with
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
                ~final_structure:make_generic_terminal_structure ~add_event
                nodes env phi events
        )
      | _ ->
          interpret_statements_open
            ~recurse:(interpret_statements_step_counter step_counter per_loop)
            ~final_structure:make_generic_terminal_structure ~add_event nodes
            env phi events

  let step_interpret lwt_ctx =
    let* ctx = lwt_ctx in
    let step_counter = ctx.step_counter in
    let per_loop =
      match ctx.options.loop_semantics with
      | StepCounterPerLoop -> true
      | _ -> false
    in
      generic_step_interpret
        ~stmt_semantics:(interpret_statements_step_counter step_counter per_loop)
        lwt_ctx

  let interpret ~step_counter lwt_ctx =
    let* ctx = lwt_ctx in
    let stmt_semantics = interpret_statements_step_counter step_counter true in

    match (ctx.program_stmts, ctx.litmus_constraints) with
    | Some stmts, Some constraints ->
        let* structure, events, source_spans =
          interpret_generic ~stmt_semantics stmts [] (Hashtbl.create 16) []
        in
          Lwt.return (structure, source_spans)
    | _ -> failwith "No program statements or constraints for interpretation."
end

(** {1 Symbolic loop semantics} *)

(** Symbolic loop semantics for unbounded loops:

    Loop iterations are tracked symbolically: all branches are evaluated.
    Semantics is in general not sound unless all loops are episodic. Semantics
    is sufficient to establish episodicity criteria. *)

module SymbolicLoopSemantics : sig
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t

  val interpret :
    mordor_ctx Lwt.t ->
    (symbolic_event_structure * (int, source_span) Hashtbl.t) Lwt.t
end = struct
  let rec interpret_statements_symbolic_loop ~final_structure ~add_event
      (nodes : ir_node list) env phi events =
    match nodes with
    | node :: rest -> (
        match node.stmt with
        | Do { body; condition } ->
            let after_val =
              Expr.evaluate (Expr.unop "!" condition) (fun v ->
                  Hashtbl.find_opt env v
              )
            in
            let get_after_structure ~add_event env phi _events =
              interpret_statements_open
                ~recurse:
                  (interpret_statements_symbolic_loop ~final_structure
                     ~add_event
                  )
                ~final_structure ~add_event rest env (after_val :: phi) events
            in
            let part_applied_interpret_statements nodes env phi events =
              interpret_statements_symbolic_loop
                ~final_structure:get_after_structure ~add_event nodes env phi
                events
            in
              interpret_statements_open
                ~recurse:part_applied_interpret_statements
                ~final_structure:get_after_structure ~add_event body env phi
                events
        | While { condition; body } ->
            let after_val =
              Expr.evaluate (Expr.unop "!" condition) (fun v ->
                  Hashtbl.find_opt env v
              )
            in
            let after_phi = after_val :: phi in
              let* after_structure =
                interpret_statements_symbolic_loop ~final_structure ~add_event
                  rest env after_phi events
              in
              let get_after_structure ~add_event:_ _env _phi _events =
                Lwt.return after_structure
              in
              let part_applied_interpret_statements nodes env phi events =
                interpret_statements_symbolic_loop
                  ~final_structure:get_after_structure ~add_event nodes env phi
                  events
              in

              let* loop_structure =
                interpret_statements_open
                  ~recurse:part_applied_interpret_statements
                  ~final_structure:get_after_structure ~add_event body env phi
                  events
              in
                Lwt.return
                  (SymbolicEventStructure.plus loop_structure after_structure)
        | _ ->
            let part_applied_interpret_statements nodes env phi events =
              interpret_statements_symbolic_loop ~final_structure ~add_event
                nodes env phi events
            in
              interpret_statements_open
                ~recurse:part_applied_interpret_statements ~final_structure
                ~add_event nodes env phi events
      )
    | [] -> final_structure ~add_event env phi events

  let step_interpret lwt_ctx =
    let* ctx = lwt_ctx in
    let stmt_semantics =
      interpret_statements_symbolic_loop
        ~final_structure:make_generic_terminal_structure ~add_event
    in
      generic_step_interpret ~stmt_semantics lwt_ctx

  let interpret lwt_ctx =
    let* ctx = lwt_ctx in
    let stmt_semantics =
      interpret_statements_symbolic_loop
        ~final_structure:make_generic_terminal_structure ~add_event
    in

    match (ctx.program_stmts, ctx.litmus_constraints) with
    | Some stmts, Some constraints ->
        let* structure, events, source_spans =
          interpret_generic ~stmt_semantics stmts [] (Hashtbl.create 16) []
        in
          Lwt.return (structure, source_spans)
    | _ -> failwith "No program statements or constraints for interpretation."
end

let step_interpret lwt_ctx =
  let* ctx = lwt_ctx in
    Logs.debug (fun m ->
        m "Interpreting program with %s loop semantics."
          ( match ctx.options.loop_semantics with
          | Symbolic -> "symbolic"
          | StepCounterPerLoop -> "step counter per loop"
          | FiniteStepCounter -> "finite step counter"
          | Generic -> "generic"
          )
    );
    greek_counter := 0;
    zh_counter := 0;
    match ctx.options.loop_semantics with
    | FiniteStepCounter | StepCounterPerLoop ->
        StepCounterSemantics.step_interpret lwt_ctx
    | Symbolic -> SymbolicLoopSemantics.step_interpret lwt_ctx
    | Generic ->
        generic_step_interpret ~stmt_semantics:interpret_statements lwt_ctx
