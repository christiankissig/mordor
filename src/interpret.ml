(** Program interpreter for concurrent programs with memory operations.

    This module provides interpretation of intermediate representation (IR)
    programs as symbolic event structures. It supports various loop semantics
    including step-counter based unrolling and symbolic loop handling. *)

open Context
open Events
open Eventstructures
open Expr
open Lwt.Syntax
open Types
open Uset

let ir_node_to_string = Ir.to_string ~ann_to_string:(fun _ -> "")

(** {1 Event and Symbol Generation} *)

(** Event counter for generating unique event identifiers. *)
let event_counter = ref 0

(** Generate the next unique event identifier.
    @return A fresh integer identifier. *)
let next_event_id () =
  incr event_counter;
  !event_counter

(** Counter for Greek letter symbols (α, β, γ, ...). *)
let greek_counter = ref 0

(** Generate the next Greek letter symbol with optional numeric suffix.
    @return
      A string containing a Greek letter, possibly with a numeric suffix (e.g.,
      "α", "β", "α1", "β1", ...). *)
let next_greek () =
  let num_greek_letters = String.length greek_alpha / 2 in
  (* 24 letters *)
  let idx = !greek_counter mod num_greek_letters in
  let suffix = !greek_counter / num_greek_letters in
    incr greek_counter;
    let base = String.sub greek_alpha (idx * 2) 2 in
      if suffix = 0 then base else base ^ string_of_int suffix

(** Counter for Chinese character symbols. *)
let zh_counter = ref 0

(** Generate the next Chinese character symbol with optional numeric suffix.
    @return
      A string containing a Chinese character, possibly with a numeric suffix.
*)
let next_zh () =
  let num_zh_chars = String.length zh_alpha / 3 in
  let idx = !zh_counter mod num_zh_chars in
  let suffix = !zh_counter / num_zh_chars in
    incr zh_counter;
    let base = String.sub zh_alpha (idx * 3) 3 in
      if suffix = 0 then base else base ^ string_of_int suffix

(** {1 Event Structure Tracking} *)

(** Structure tracking events globally during interpretation.

    This improves efficiency as events and symbols (and thus origins) are
    enumerated from the start of the program, but event structures are
    constructed from the end as continuations. Thus creating the event and
    origin tables at the end requires repeated merging. The last labels are
    anyways defined inductively from the start. *)
type events_t = {
  defacto : expr list;  (** Optional de facto constraints from litmus tests. *)
  events : (int, event) Hashtbl.t;  (** Events indexed by label. *)
  origin : (string, int) Hashtbl.t;
      (** Origin mapping for symbols to event labels. *)
  env_by_evt : (int, (string, expr) Hashtbl.t) Hashtbl.t;
      (** Register environment at each event label. *)
  thread_index : (int, int) Hashtbl.t;
      (** Mapping from event labels to thread indices. *)
  loop_indices : (int, int list) Hashtbl.t;
      (** Mapping from event labels to loop indices. *)
  source_spans : (int, source_span) Hashtbl.t;
      (** Mapping from event labels to source code spans. *)
  globals : string USet.t;  (** Set of global variable names. *)
  mutable label : int;  (** Counter for generating unique event labels. *)
}

(** Create a new empty events structure.
    @return A fresh events_t with empty tables and zero label counter. *)
let create_events defacto =
  {
    defacto;
    events = Hashtbl.create 256;
    origin = Hashtbl.create 256;
    env_by_evt = Hashtbl.create 256;
    source_spans = Hashtbl.create 256;
    thread_index = Hashtbl.create 256;
    loop_indices = Hashtbl.create 256;
    globals = USet.create ();
    label = 0;
  }

(** Add an event to the global events structure.

    @param events The global events structure to add to.
    @param event The event to add (label will be overwritten).
    @param env The current register environment.
    @param annotation
      Source annotations including span, thread, and loop context.
    @return The event with its newly assigned label. *)
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

(** Update the register environment with a new binding.

    @param env The current environment.
    @param register The register name to update.
    @param expr The expression to bind to the register (will be evaluated).
    @return A new environment with the updated binding. *)
let update_env (env : (string, expr) Hashtbl.t) (register : string) (expr : expr)
    =
  let regexpr : expr = Expr.evaluate ~env:(Hashtbl.find_opt env) expr in
  let env' = Hashtbl.copy env in
    Hashtbl.replace env' register regexpr;
    env'

(** {1 Event Structure Construction} *)

(** Add a read-modify-write edge to a symbolic event structure.

    @param structure The event structure to modify.
    @param er The label of the read event.
    @param ew The label of the write event.
    @return A new event structure with the RMW edge added. *)
let add_rmw_edge (structure : symbolic_event_structure) (er : int) (cond : expr)
    (ew : int) =
  USet.add structure.rmw (er, cond, ew) |> ignore;
  structure

(** {1 Statement Interpretation} *)

(** Interpret programs as lists of IR nodes depth-first using open recursion.

    The [recurse] argument is the interpretation function to use for recursive
    calls. The [add_event] argument is the function to use to add events to the
    global event table.

    @param recurse The interpretation function for recursive calls.
    @param final_structure
      Function to construct the final structure when nodes are exhausted.
    @param add_event Function to add events to the global table.
    @param nodes The list of IR nodes to interpret.
    @param env
      The current register environment mapping registers to expressions.
    @param phi The current path condition as a list of expressions.
    @param events The global events table being built.
    @return
      A symbolic event structure representing the interpreted program fragment.
*)
let interpret_statements_open ~recurse ~final_structure ~add_event
    (nodes : ir_node list) env phi events =
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
              let expr_value =
                Expr.evaluate ~env:(Hashtbl.find_opt env) expr
                |> Expr.apply_constraints
              in
              let env' = update_env env register expr_value in
                let* cont = recurse rest env' phi events in
                  Lwt.return cont
          | RegisterRefAssign { register; global } ->
              let env' = update_env env register (EVar global) in
                let* cont = recurse rest env' phi events in
                  Lwt.return cont
          | GlobalStore { global; expr; assign } ->
              let wval =
                Expr.evaluate ~env:(Hashtbl.find_opt env) expr
                |> Expr.apply_constraints
              in
              let evt =
                {
                  (Event.create Write 0 ()) with
                  id = Some (VVar global);
                  loc = Some (EVar global);
                  wval = Some wval;
                  wmod = assign.mode;
                  volatile = assign.volatile;
                }
              in
                USet.add events.globals global |> ignore;
                let event' : event = add_event events evt env annotation in
                let defacto =
                  List.map
                    (Expr.evaluate ~env:(Hashtbl.find_opt env))
                    events.defacto
                in
                  let* cont = recurse rest env phi events in
                    Lwt.return
                      (SymbolicEventStructure.dot event' cont phi defacto)
          | DerefStore { address; expr; assign } ->
              let loc = Expr.evaluate ~env:(Hashtbl.find_opt env) address in
              let wval =
                Expr.evaluate ~env:(Hashtbl.find_opt env) expr
                |> Expr.apply_constraints
              in
              let evt =
                {
                  (Event.create Write 0 ()) with
                  loc = Some loc;
                  wval = Some wval;
                  wmod = assign.mode;
                  volatile = assign.volatile;
                }
              in
              let event' : event = add_event events evt env annotation in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
              in
                let* cont = recurse rest env phi events in
                  Lwt.return (SymbolicEventStructure.dot event' cont phi defacto)
          | DerefLoad { register; address; load } ->
              let symbol = next_greek () in
              let rval = VSymbol symbol in
              let evt =
                {
                  (Event.create Read 0 ()) with
                  loc = Some (Expr.evaluate ~env:(Hashtbl.find_opt env) address);
                  rval = Some rval;
                  rmod = load.mode;
                  volatile = load.volatile;
                }
              in
              let event' : event = add_event events evt env annotation in
                Hashtbl.replace events.origin symbol event'.label;
                let defacto =
                  List.map
                    (Expr.evaluate ~env:(Hashtbl.find_opt env))
                    events.defacto
                in
                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return
                      (SymbolicEventStructure.dot event' cont phi defacto)
          | GlobalLoad { register; global; load } ->
              let symbol = next_greek () in
              let rval = VSymbol symbol in
              let evt =
                {
                  (Event.create Read 0 ()) with
                  id = Some (VVar global);
                  loc = Some (EVar global);
                  rval = Some rval;
                  rmod = load.mode;
                  volatile = load.volatile;
                }
              in
                USet.add events.globals global |> ignore;
                let event' : event = add_event events evt env annotation in
                  Hashtbl.replace events.origin symbol event'.label;
                  let defacto =
                    List.map
                      (Expr.evaluate ~env:(Hashtbl.find_opt env))
                      events.defacto
                  in

                  let env' = Hashtbl.copy env in
                    Hashtbl.replace env' register (Expr.of_value rval);
                    let* cont = recurse rest env' phi events in
                      Lwt.return
                        (SymbolicEventStructure.dot event' cont phi defacto)
          | Fadd
              { register; address; operand; rmw_mode; load_mode; assign_mode }
            ->
              let loc = Expr.evaluate ~env:(Hashtbl.find_opt env) address in
              let symbol = next_greek () in
              let rval = VSymbol symbol in
              let base_evt_load : event = Event.create Read 0 () in
              let evt_load =
                {
                  base_evt_load with
                  loc = Some loc;
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
                  Expr.evaluate ~env:(Hashtbl.find_opt env)
                    (Expr.binop loaded_expr "+" operand)
                  |> Expr.apply_constraints
                in
                (* if the operand evaluates to zero, this is a read-don't
                   modify-write *)
                let is_rdmw =
                  Expr.evaluate ~env:(Hashtbl.find_opt env) operand
                  == ENum Z.zero
                in
                let evt_store =
                  {
                    (Event.create Write 0 ()) with
                    loc = Some loc;
                    wval = Some result_expr;
                    wmod = assign_mode;
                    volatile = false;
                    is_rdmw;
                  }
                in
                let event_store' : event =
                  add_event events evt_store env annotation
                in
                let defacto =
                  List.map
                    (Expr.evaluate ~env:(Hashtbl.find_opt env))
                    events.defacto
                in

                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register result_expr;
                  let* cont = recurse rest env' phi events in
                    Lwt.return
                      (add_rmw_edge
                         (SymbolicEventStructure.dot event_load'
                            (SymbolicEventStructure.dot event_store' cont phi
                               defacto
                            )
                            phi defacto
                         )
                         event_load'.label (EBoolean true) event_store'.label
                      )
          | Cas { register; address; expected; desired; load_mode; assign_mode }
            ->
              let loc = Expr.evaluate ~env:(Hashtbl.find_opt env) address in
              let symbol = next_greek () in
              let rval = VSymbol symbol in
              let evt_load =
                {
                  (Event.create Read 0 ()) with
                  loc = Some loc;
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
                  Expr.evaluate ~env:(Hashtbl.find_opt env) expected
                in
                let cond_expr = Expr.binop loaded_expr "=" expected_expr in
                let base_evt_store : event = Event.create Write 0 () in
                let wval =
                  Expr.evaluate ~env:(Hashtbl.find_opt env) desired
                  |> Expr.apply_constraints
                in
                let evt_store =
                  {
                    base_evt_store with
                    loc = Some loc;
                    wval = Some wval;
                    wmod = assign_mode;
                    volatile = false;
                  }
                in
                let event_store' : event =
                  add_event events evt_store env annotation
                in
                let phi_succ = cond_expr :: phi in
                let phi_fail =
                  (Expr.inverse cond_expr |> Expr.evaluate) :: phi
                in
                let defacto =
                  List.map
                    (Expr.evaluate ~env:(Hashtbl.find_opt env))
                    events.defacto
                in

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
                                    cont_succ phi_succ defacto
                                 )
                                 event_load'.label cond_expr event_store'.label
                              )
                              cont_fail
                           )
                           phi defacto
                        )
          | If { condition; then_body; else_body } -> (
              (* TODO prune semantically impossible branches against phi *)
              let cond_val =
                Expr.evaluate ~env:(Hashtbl.find_opt env) condition
                |> Expr.apply_constraints
              in
              let new_then_phi =
                if cond_val = EBoolean true then phi else cond_val :: phi
              in
                let* new_then_phi_sat = Solver.is_sat_cached new_then_phi in
                let new_then_phi =
                  if new_then_phi_sat then new_then_phi else [ EBoolean false ]
                in
                let cond_val =
                  if new_then_phi_sat then cond_val else EBoolean false
                in
                let else_cond_val = Expr.evaluate (Expr.inverse cond_val) in
                let new_else_phi =
                  if cond_val = EBoolean false then phi
                  else else_cond_val :: phi
                in
                  let* new_else_phi_sat = Solver.is_sat_cached new_else_phi in
                  let else_cond_val =
                    if new_else_phi_sat then else_cond_val else EBoolean false
                  in
                  let new_else_phi =
                    if new_else_phi_sat then new_else_phi
                    else [ EBoolean false ]
                  in

                  let then_structure events =
                    recurse (then_body @ rest) env new_then_phi events
                  in

                  let defacto =
                    List.map
                      (Expr.evaluate ~env:(Hashtbl.find_opt env))
                      events.defacto
                  in
                  let branch_event =
                    { (Event.create Branch 0 ()) with cond = Some cond_val }
                  in
                  let branch_event' =
                    add_event events branch_event env annotation
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
                                (SymbolicEventStructure.dot branch_event'
                                   (SymbolicEventStructure.plus then_structure
                                      else_structure
                                   )
                                   phi defacto
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
                                (SymbolicEventStructure.dot branch_event'
                                   (SymbolicEventStructure.plus then_structure
                                      rest_structure
                                   )
                                   phi defacto
                                )
                    )
            )
          | Fence { mode } ->
              let base_evt : event = Event.create Fence 0 () in
              let evt = { base_evt with fmod = mode } in
              let event' : event = add_event events evt env annotation in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
              in

              let* cont = recurse rest env phi events in
                Lwt.return (SymbolicEventStructure.dot event' cont phi defacto)
          | Lock { global } ->
              let base_evt : event = Event.create Lock 0 () in
              let evt =
                match global with
                | Some g ->
                    USet.add events.globals g |> ignore;
                    { base_evt with id = Some (VVar g) }
                | None -> base_evt
              in
              let event' : event = add_event events evt env annotation in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
              in

              let* cont = recurse rest env phi events in
                Lwt.return (SymbolicEventStructure.dot event' cont phi defacto)
          | Unlock { global } ->
              let base_evt : event = Event.create Unlock 0 () in
              let evt =
                match global with
                | Some g ->
                    USet.add events.globals g |> ignore;
                    { base_evt with id = Some (VVar g) }
                | None -> base_evt
              in
              let event' : event = add_event events evt env annotation in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
              in

              let* cont = recurse rest env phi events in
                Lwt.return (SymbolicEventStructure.dot event' cont phi defacto)
          | RegMalloc { register; size } ->
              let symbol = next_zh () in
              let rval = VSymbol symbol in
              let loc = ESymbol symbol in
              let base_evt : event = Event.create Malloc 0 () in
              let evt = { base_evt with rval = Some rval; loc = Some loc } in
              let event' : event = add_event events evt env annotation in
                Hashtbl.replace events.origin symbol event'.label;
                let defacto =
                  List.map
                    (Expr.evaluate ~env:(Hashtbl.find_opt env))
                    events.defacto
                in

                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let* cont = recurse rest env' phi events in
                    Lwt.return
                      (SymbolicEventStructure.dot event' cont phi defacto)
          | GlobalMalloc { global; size } ->
              let symbol = next_zh () in
              let rval = VSymbol symbol in
              let loc = ESymbol symbol in
              let base_evt : event = Event.create Malloc 0 () in
              let evt = { base_evt with rval = Some rval; loc = Some loc } in
              let event' : event = add_event events evt env annotation in
                USet.add events.globals global |> ignore;
                Hashtbl.replace events.origin symbol event'.label;
                let defacto =
                  List.map
                    (Expr.evaluate ~env:(Hashtbl.find_opt env))
                    events.defacto
                in

                let env' = Hashtbl.copy env in
                  let* cont = recurse rest env' phi events in
                    Lwt.return
                      (SymbolicEventStructure.dot event' cont phi defacto)
          | Free { register } ->
              let base_evt : event = Event.create Free 0 () in
              let loc = Hashtbl.find_opt env register in
              let evt = { base_evt with loc } in
              let event' : event = add_event events evt env annotation in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
              in

              let* cont = recurse rest env phi events in
                Lwt.return (SymbolicEventStructure.dot event' cont phi defacto)
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

(** {1 Terminal Structure} *)

(** Create a generic terminal structure with a terminal event.

    Adds a single terminal event and establishes distinctness constraints for
    all global variables.

    @param add_event Function to add events to the global table.
    @param env The current register environment.
    @param phi The current path condition.
    @param events The global events structure.
    @return A symbolic event structure with a terminal event. *)
let make_generic_terminal_structure ~add_event env phi events =
  let structure = SymbolicEventStructure.create () in
  let terminal_evt = Event.create Terminal 0 () in
  let terminal_evt : event =
    add_event events terminal_evt env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
  let constraints =
    URelation.cross events.globals events.globals
    |> (fun rel -> USet.set_minus rel (URelation.identity events.globals))
    |> USet.values
    |> List.map (fun (g1, g2) -> if g1 < g2 then (g1, g2) else (g2, g1))
    |> List.sort_uniq (fun (a1, b1) (a2, b2) ->
        let c = compare a1 a2 in
          if c <> 0 then c else compare b1 b2
    )
    |> List.map (fun (v1, v2) -> Expr.binop (EVar v1) "!=" (EVar v2))
  in
  let cont =
    {
      structure with
      events = events.events;
      origin = events.origin;
      loop_indices = events.loop_indices;
      thread_index = events.thread_index;
      p = events.env_by_evt;
      constraints;
    }
  in
  let defacto =
    List.map (Expr.evaluate ~env:(Hashtbl.find_opt env)) events.defacto
  in

  Lwt.return (SymbolicEventStructure.dot terminal_evt cont phi defacto)

(** {1 Basic Interpretation} *)

(** Interpret statements with no special handling of while loops.

    This is the base interpretation that handles all statements except unbounded
    loops, which are left uninterpreted.

    @param stmts The list of IR nodes to interpret.
    @param env The initial register environment.
    @param phi The initial path condition.
    @param events The global events structure.
    @return A symbolic event structure representing the interpretation. *)
let rec interpret_statements stmts env phi events =
  interpret_statements_open ~recurse:interpret_statements
    ~final_structure:make_generic_terminal_structure ~add_event stmts env phi
    events

(** {1 Generic Interpretation} *)

(** Generic interpretation function with configurable statement semantics.

    @param stmt_semantics The interpretation function for statements.
    @param defacto Optional de facto constraints from litmus tests.
    @param constraints Optional additional constraints from litmus tests.
    @param stmts The program statements to interpret.
    @return
      A tuple of (symbolic event structure, events table, source spans table).
*)
let interpret_generic ~stmt_semantics ~defacto ~constraints stmts =
  (* Events context *)
  let events = create_events defacto in
  (* Register environment *)
  let env = Hashtbl.create 32 in

  (* Initial event. Create first for correct labelling. *)
  let init_event = Event.create Init 0 () in
  let init_event' =
    add_event events
      { (Event.create Init 4 ()) with label = 0 }
      env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in

  (* Interpret program statements *)
  let* structure = stmt_semantics stmts env [] events in

  (* Prefix with initial event *)
  let defacto =
    List.map (Expr.evaluate ~env:(Hashtbl.find_opt env)) events.defacto
  in
  let structure = SymbolicEventStructure.dot init_event' structure [] defacto in

  (* Add data from the events context *)
  let structure =
    {
      structure with
      events = events.events;
      origin = events.origin;
      loop_indices = events.loop_indices;
      thread_index = events.thread_index;
      p = events.env_by_evt;
    }
  in

  Lwt.return (structure, events.source_spans)

(** Default interpretation function with basic statement semantics.

    @param defacto Optional de facto constraints.
    @param constraints Optional additional constraints.
    @param stmts The program statements to interpret.
    @return
      A tuple of (symbolic event structure, events table, source spans table).
*)
let interpret ?(defacto = None) ?(constraints = None) stmts =
  let defacto = defacto |> Option.value ~default:[] in
    interpret_generic ~stmt_semantics:interpret_statements ~defacto ~constraints
      stmts

(** {1 Pipeline Integration} *)

(** Generic pipeline step for program interpretation.

    @param stmt_semantics The interpretation function for statements.
    @param lwt_ctx The current Mordor context as a Lwt promise.
    @return An updated Mordor context with interpretation results. *)
let generic_step_interpret ~stmt_semantics (lwt_ctx : mordor_ctx Lwt.t) :
    mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match ctx.program_stmts with
    | Some stmts ->
        let defacto = ctx.litmus_defacto |> Option.value ~default:[] in
        let constraints = ctx.litmus_constraints |> Option.value ~default:[] in
          let* structure, source_spans =
            interpret_generic ~stmt_semantics ~defacto ~constraints stmts
          in
            Logs.debug (fun m ->
                m
                  "Completed program interpretation with symbolic\n\
                  \        event structure: \n\
                   %s\n\
                   and events\n\
                   %s"
                  (show_symbolic_event_structure structure)
                  (Hashtbl.fold
                     (fun label evt acc ->
                       acc
                       ^ Printf.sprintf "Event %d: %s\n" label
                           (Event.to_string evt)
                     )
                     structure.events ""
                  )
            );
            ctx.structure <- Some structure;
            ctx.source_spans <- Some source_spans;
            Lwt.return ctx
    | _ ->
        Logs.err (fun m -> m "No program statements for interpretation.");
        Lwt.return ctx

(** {1 Step Counter Semantics} *)

(** Finite step-counter semantics of unbounded loops.

    The semantics of do- and while-loops is defined in terms of a fixed number
    of unrollings of the loop as nested if-statements. Per-loop step-counter
    leads to fixed number of unrollings per loop, and a global step-counter
    limiting unrollings across all sequential and nested loops otherwise. The
    per-loop unrolling is applied before interpreting, while the global
    step-counter is applied during the interpretation. *)
module StepCounterSemantics : sig
  (** Pipeline step for interpreting with step counter semantics.

      @param ctx The Mordor context.
      @return Updated context with interpretation results. *)
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t

  (** Interpret a program with a specific step counter.

      @param step_counter The maximum number of loop iterations to unroll.
      @param ctx The Mordor context.
      @return A tuple of (symbolic event structure, source spans table). *)
  val interpret :
    step_counter:int ->
    mordor_ctx Lwt.t ->
    (symbolic_event_structure * (int, source_span) Hashtbl.t) Lwt.t
end = struct
  (** Create an IR node with no annotations.

      @param stmt The statement to wrap.
      @return An IR node with empty annotations. *)
  let make_ir_node stmt : ir_node =
    Ir.
      {
        annotations = { source_span = None; thread_ctx = None; loop_ctx = None };
        stmt;
      }

  (** Unroll a while loop once as an if-statement.

      @param body The loop body.
      @param condition The loop condition.
      @return A list containing the unrolled loop as an if-statement. *)
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

  (** Unroll a do-while loop once as body followed by an if-statement.

      @param body The loop body.
      @param condition The loop condition.
      @return The body followed by an if-statement for continuation. *)
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

  (** Unroll a while loop a specific number of times.

      @param body The loop body.
      @param condition The loop condition.
      @param times The number of unrollings (must be non-negative).
      @return A list of nested if-statements representing the unrolled loop. *)
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

  (** Unroll a do-while loop a specific number of times.

      @param body The loop body.
      @param condition The loop condition.
      @param times The number of unrollings (must be at least 1).
      @return The unrolled loop as nested body and if-statements. *)
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

  (** Interpret statements with step counter loop semantics.

      @param step_counter Maximum loop iterations (must be non-negative).
      @param per_loop If true, apply step counter per loop; otherwise globally.
      @param nodes The IR nodes to interpret.
      @param env The register environment.
      @param phi The path condition.
      @param events The global events structure.
      @return A symbolic event structure. *)
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
      greek_counter := 0;
      zh_counter := 0;
      let stmt_semantics =
        interpret_statements_step_counter step_counter true
      in

      match ctx.program_stmts with
      | Some stmts ->
          let defacto = ctx.litmus_defacto |> Option.value ~default:[] in
          let constraints = ctx.litmus_constraints in
            let* structure, source_spans =
              interpret_generic ~stmt_semantics ~defacto ~constraints stmts
            in
              Lwt.return (structure, source_spans)
      | _ -> failwith "No program statements or constraints for interpretation."
end

(** {1 Symbolic Loop Semantics} *)

(** Symbolic loop semantics for unbounded loops.

    Loop iterations are tracked symbolically: all branches are evaluated.
    Semantics is in general not sound unless all loops are episodic. Semantics
    is sufficient to establish episodicity criteria. *)
module SymbolicLoopSemantics : sig
  (** Pipeline step for interpreting with symbolic loop semantics.

      @param ctx The Mordor context.
      @return Updated context with interpretation results. *)
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t

  (** Interpret a program with symbolic loop semantics.

      @param ctx The Mordor context.
      @return A tuple of (symbolic event structure, source spans table). *)
  val interpret :
    mordor_ctx Lwt.t ->
    (symbolic_event_structure * (int, source_span) Hashtbl.t) Lwt.t
end = struct
  (** Generate program order relations for a symbolic event structure.

      For each loop, generate program order edges between all pairs of events in
      that loop with the meaning that any event in the previous iteration of a
      loop is po-before any event in the current iteration of the loop. This
      approximation makes distinctly sense for symbolic loop semantics, and
      under the assumption that symbols and registers meet episodicity criteria.

      @param structure The symbolic event structure to analyze.
      @return A set of program order edges between events in the same loop. *)
  let generate_po_iter (structure : symbolic_event_structure) =
    Logs.debug (fun m ->
        m "Generating program order relations for symbolic loop semantics."
    );
    Logs.debug (fun m ->
        m "Loop indices by event: %s"
          (Hashtbl.fold
             (fun e loops acc ->
               let loops_str =
                 loops |> List.map string_of_int |> String.concat ", "
               in
                 acc ^ Printf.sprintf "Event %d: Loops [%s]\n" e loops_str
             )
             structure.loop_indices ""
          )
    );
    let po_iter = USet.create () in
    let events_by_loop = Hashtbl.create (USet.size structure.e) in
      Hashtbl.iter
        (fun e loops ->
          List.iter
            (fun l ->
              let events =
                Hashtbl.find_opt events_by_loop l
                |> Option.value ~default:(USet.create ())
              in
                Hashtbl.replace events_by_loop l (USet.add events e)
            )
            loops
        )
        structure.loop_indices;
      Logs.debug (fun m ->
          m "Events by loop: %s"
            (Hashtbl.fold
               (fun l events acc ->
                 let events_str =
                   USet.values events
                   |> List.map string_of_int
                   |> String.concat ", "
                 in
                   acc ^ Printf.sprintf "Loop %d: Events [%s]\n" l events_str
               )
               events_by_loop ""
            )
      );
      Hashtbl.iter
        (fun _ events ->
          URelation.identity events
          |> USet.set_minus (URelation.cross events events)
          |> USet.inplace_union po_iter
          |> ignore
        )
        events_by_loop;
      po_iter

  (** Interpret statements with symbolic loop semantics.

      Evaluates all branches of loops symbolically without unrolling.

      @param final_structure Function to create the final structure.
      @param add_event Function to add events.
      @param nodes The IR nodes to interpret.
      @param env The register environment.
      @param phi The path condition.
      @param events The global events structure.
      @return A symbolic event structure. *)
  let rec interpret_statements_symbolic_loop ~final_structure ~add_event
      (nodes : ir_node list) env phi events =
    match nodes with
    | node :: rest -> (
        match node.stmt with
        | Do { body; condition } ->
            let after_val =
              Expr.evaluate
                ~env:(fun v -> Hashtbl.find_opt env v)
                (Expr.inverse condition)
            in
            let final_structure ~add_event env phi _events =
              interpret_statements_symbolic_loop ~final_structure ~add_event
                rest env (after_val :: phi) events
            in
            let recurse nodes env phi events =
              interpret_statements_symbolic_loop ~final_structure ~add_event
                nodes env phi events
            in
              interpret_statements_open ~recurse ~final_structure ~add_event
                body env phi events
        | While { condition; body } ->
            let after_val =
              Expr.evaluate
                ~env:(fun v -> Hashtbl.find_opt env v)
                (Expr.inverse condition)
            in
              let* after_structure =
                interpret_statements_symbolic_loop ~final_structure ~add_event
                  rest env (after_val :: phi) events
              in
              let final_structure ~add_event:_ _env _phi _events =
                Lwt.return after_structure
              in
              let recurse nodes env phi events =
                interpret_statements_symbolic_loop ~final_structure ~add_event
                  nodes env phi events
              in
                let* loop_structure =
                  interpret_statements_open ~recurse ~final_structure ~add_event
                    body env phi events
                in
                  Lwt.return
                    (SymbolicEventStructure.plus loop_structure after_structure)
        | _ ->
            let recurse nodes env phi events =
              interpret_statements_symbolic_loop ~final_structure ~add_event
                nodes env phi events
            in
              interpret_statements_open ~recurse ~final_structure ~add_event
                nodes env phi events
      )
    | [] -> final_structure ~add_event env phi events

  let step_interpret lwt_ctx =
    Logs.debug (fun m -> m "Interpreting program with symbolic loop semantics.");
    let* ctx = lwt_ctx in
    let stmt_semantics =
      interpret_statements_symbolic_loop
        ~final_structure:make_generic_terminal_structure ~add_event
    in
      let* ctx = generic_step_interpret ~stmt_semantics lwt_ctx in
        ctx.structure <-
          Some
            {
              (Option.get ctx.structure) with
              po_iter = generate_po_iter (Option.get ctx.structure);
            };
        Lwt.return ctx

  let interpret lwt_ctx =
    let* ctx = lwt_ctx in
      greek_counter := 0;
      zh_counter := 0;
      let stmt_semantics =
        interpret_statements_symbolic_loop
          ~final_structure:make_generic_terminal_structure ~add_event
      in

      match ctx.program_stmts with
      | Some stmts ->
          let defacto = ctx.litmus_defacto |> Option.value ~default:[] in
          let constraints = ctx.litmus_constraints in
            let* structure, source_spans =
              interpret_generic ~stmt_semantics ~defacto ~constraints stmts
            in
            let structure =
              { structure with po_iter = generate_po_iter structure }
            in
              Lwt.return (structure, source_spans)
      | _ -> failwith "No program statements or constraints for interpretation."
end

(** {1 Main Pipeline Step} *)

(** Main interpretation pipeline step.

    Selects the appropriate loop semantics based on context options and performs
    program interpretation.

    @param lwt_ctx The Mordor context.
    @return Updated context with interpretation results. *)
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
