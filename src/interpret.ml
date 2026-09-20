(** Program interpreter for concurrent programs with memory operations.

    This module provides interpretation of intermediate representation (IR)
    programs as symbolic event structures. It supports various loop semantics
    including step-counter based unrolling and symbolic loop handling. *)

open Ast
open Context
open Events
open Eventstructures
open Expr
open Lwt.Syntax
open Types
open Uset

let ir_node_to_string = Ir.to_string ~ann_to_string:(fun _ -> "")

(** {1 Event and Symbol Allocation} *)

(** Allocator of event labels and fresh symbols.

    One allocator is made for each interpretation and handed down the recursion
    inside {!events_t}, so labels and symbols are fresh within an interpretation
    and start over with the next one. The three counters used to be module-level
    references that every entry point had to remember to reset, and that two
    interpretations running at once would have shared.

    A thread is interpreted as a fragment, with labels of its own from [0], and
    relabelled into place; see {!interpret_thread}. *)
module Allocator = struct
  type t = { mutable label : int; mutable greek : int; mutable zh : int }

  let create () = { label = 0; greek = 0; zh = 0 }

  (** [next_label t] is the next unused event label, counting from [0]. *)
  let next_label t =
    let label = t.label in
      t.label <- label + 1;
      label

  (* The [n]th symbol over an alphabet of [width]-byte characters: the
     alphabet's letters in turn, then again with a numeric suffix. *)
  let nth_symbol alphabet width n =
    let letters = String.length alphabet / width in
    let base = String.sub alphabet (n mod letters * width) width in
      if n < letters then base else base ^ string_of_int (n / letters)

  (** [next_greek t] is the next Greek letter symbol, with a numeric suffix once
      the alphabet is exhausted (e.g., "α", "β", ..., "α1", "β1", ...). *)
  let next_greek t =
    let n = t.greek in
      t.greek <- n + 1;
      nth_symbol greek_alpha 2 n

  (** [next_zh t] is the next Chinese character symbol, with a numeric suffix
      once the alphabet is exhausted. *)
  let next_zh t =
    let n = t.zh in
      t.zh <- n + 1;
      nth_symbol zh_alpha 3 n

  (* The labels handed out so far. *)
  let labels t = t.label

  (* [fragment t] is an allocator for a fragment interpreted where [t] is: its
     labels are its own, from [0]; its symbols carry on from [t]'s. *)
  let fragment t = { t with label = 0 }

  (* [resume t ~after] carries [t] on past everything [after], an allocator
     made by [fragment t], has handed out. *)
  let resume t ~after =
    t.label <- t.label + after.label;
    t.greek <- after.greek;
    t.zh <- after.zh
end

(** {1 Event Structure Tracking} *)

(** The interpreter's working record of an interpretation: every event it has
    created, in the order it created them.

    Events and symbols are enumerated from the start of the program, while event
    structures are constructed from the end, as continuations, so an event is
    labelled and recorded here before the structure it will be prefixed to
    exists. {!prefix} reads what was recorded for an event when the time comes
    to put it in a structure; the structure's own tables are built there and
    describe the events that made it in, which these tables do not promise. *)
type events_t = {
  defacto : expr list;  (** Optional de facto constraints from litmus tests. *)
  events : (int, event) Hashtbl.t;  (** Events indexed by label. *)
  origin : (string, int) Hashtbl.t;
      (** Origin mapping for symbols to event labels. *)
  env_by_evt : (int, (string, expr) Hashtbl.t) Hashtbl.t;
      (** Register environment at each event label. *)
  thread_index : (int, int) Hashtbl.t;
      (** Mapping from event labels to thread indices. An event is added to
          thread [0], the thread being interpreted: the program's own outside
          every parallel block, or the fragment's inside one, which relabelling
          moves to the thread's index. *)
  mutable threads_allocated : int;
      (** The last thread index handed out, counting from [1] for the first
          thread of the first parallel block interpreted, nested ones included.
      *)
  loop_indices : (int, int list) Hashtbl.t;
      (** Mapping from event labels to loop indices. *)
  loop_conditions : (int, expr list) Hashtbl.t;
      (** Mapping from a loop index to the continuation guards recorded for it,
          one per interpreted occurrence of the loop. Used with symbolic loop
          semantics.

          A loop node is interpreted once per enclosing branch, per copy of an
          unravelled do-loop body, and per thread, and each occurrence reaches
          the end of the body in a different register environment, so each
          contributes its own guard. *)
  source_spans : (int, source_span) Hashtbl.t;
      (** Mapping from event labels to source code spans. *)
  globals : string USet.t;  (** Set of global variable names. *)
  ubopt : bool;
      (** Whether the model exploits undefined behaviour. Gates the rewrite in
          {!apply_ub_constraints}. *)
  alloc : Allocator.t;  (** Source of event labels and fresh symbols. *)
}

(** Create a new empty events structure.
    @return A fresh events_t with empty tables and an allocator of its own. *)
let create_events ?(ubopt = false) defacto =
  {
    defacto;
    ubopt;
    events = Hashtbl.create 256;
    origin = Hashtbl.create 256;
    env_by_evt = Hashtbl.create 256;
    source_spans = Hashtbl.create 256;
    thread_index = Hashtbl.create 256;
    threads_allocated = 0;
    loop_indices = Hashtbl.create 256;
    loop_conditions = Hashtbl.create 256;
    globals = USet.create ();
    alloc = Allocator.create ();
  }

(** [apply_ub_constraints events e] folds [lhs / !r] to [lhs] when the model
    exploits undefined behaviour, and leaves [e] alone otherwise.

    Division by zero is undefined, so under a UB-exploiting model an
    implementation may assume [!r <> 0] -- that is, [r = 0] -- and fold [1 / !r]
    to [1]. The fold is what breaks the dependency of the written value on the
    read, and it is the whole content of the [LB+UB+data] family.

    It used to be applied unconditionally, which made [UB11] and no annotation
    indistinguishable and left [avoidoota/listing27_allow.lit] and
    [listing27_forbid.lit] -- the same program, asserting opposite outcomes
    under different models -- with the same verdict. [options.ubopt] has always
    said which models exploit UB; nothing read it. *)
let apply_ub_constraints events e =
  if events.ubopt then Expr.apply_constraints e else e

(** The prefix under which a UB assumption is recorded in the register
    environment.

    [env] is a name-to-expression table that {!update_env} copies on every
    write, so it is already threaded through the interpretation and already
    local to a path -- which is what a UB assumption needs, since the fold that
    licensed it fired on one branch and not the other. A key carrying this
    prefix is not a register: no register can be named with it, and
    {!Executions} keeps such keys out of an execution's final environment. *)
let ub_fact_prefix = "%ub:"

(** [ub_facts env] is every UB assumption recorded on this path, as facts.

    Each is [sym = 0]: the symbol a [1 / !sym] fold assumed away. They are
    handed to elaboration as de facto constraints on the events that follow, and
    not added to the path predicates -- a UB assumption is a permission to
    rewrite, not a claim that the value really is zero, so the unexploited
    behaviour has to stay. Elaboration already treats de facto constraints that
    way: [ValueAssignElab] solves with them and offers the narrowed write as an
    extra justification, leaving the original in the set. *)
let ub_facts env =
  Hashtbl.fold
    (fun k v acc ->
      if String.starts_with ~prefix:ub_fact_prefix k then v :: acc else acc
    )
    env []

(** [ub_assume events env e] folds [e] as {!apply_ub_constraints} does, and
    returns an environment recording what the fold assumed.

    The fold of [1 / !r] to [1] is sound only because an implementation may
    assume [r = 0]. Dropping the assumption leaves every later use of [r]
    reading its real value, so the transformation is invisible past the
    statement it fired on -- which is what left [symmrd/LB+UB+data+z.lit]'s
    [allow (r1 != rz)] without a witness (github #65).

    The assumption is on the read's *symbol*, not on the register: [r1] keeps
    its real value in the final state, and it is the later *uses* elaboration
    may rewrite. *)
let ub_assume events env e =
  if not events.ubopt then (Expr.evaluate ~env:(Hashtbl.find_opt env) e, env)
  else
    (* [Expr.evaluate] substitutes one level and stops -- a register maps to its
       read's symbol, and the symbol is returned as it is rather than looked up
       again -- so the fold has to be shown the symbol, not the register. *)
    let e = Expr.evaluate ~env:(Hashtbl.find_opt env) e in
    let folded, assumed = Expr.apply_constraints_ub e in
      if assumed = [] then (folded, env)
      else
        let env' = Hashtbl.copy env in
          List.iter
            (fun sym ->
              Hashtbl.replace env' (ub_fact_prefix ^ sym)
                (EBinOp (ESymbol sym, "=", ENum Z.zero))
            )
            assumed;
          (folded, env')

(** Add an event to the global events structure.

    @param events The global events structure to add to.
    @param event The event to add (label will be overwritten).
    @param env The current register environment.
    @param annotation
      Source annotations including span, thread, and loop context.
    @return The event with its newly assigned label. *)
let add_event (events : events_t) event env (annotation : ir_node_ann) =
  let lbl = Allocator.next_label events.alloc in
  let event' : event = { event with label = lbl } in
    Hashtbl.replace events.events lbl event';
    Hashtbl.replace events.env_by_evt lbl (Hashtbl.copy env);
    ( match annotation.source_span with
    | Some span -> Hashtbl.replace events.source_spans lbl span
    | None -> ()
    );
    (* The index is the interpreter's, not the annotation's [tid]. The parser
         annotates a thread body before the enclosing [threads] rule has
         advanced [tid] -- Menhir reduces bottom-up -- so every body carried
         [tid = 0] and every event of every thread shared one index. Memory
         models that ask whether two events are in the same thread had nothing
         to ask. The annotation still says whether the event belongs to the
         program at all: terminal events carry none and stay unindexed. *)
    ( match annotation.thread_ctx with
    | Some _ -> Hashtbl.replace events.thread_index lbl 0
    | None -> ()
    );
    ( match annotation.loop_ctx with
    | Some loop_ctx -> Hashtbl.replace events.loop_indices lbl loop_ctx.loops
    | None -> ()
    );
    event'

(** [prefix events event structure phi defacto] is [structure] prefixed with
    [event], which {!add_event} has added to [events]: the {!EventStructure} of
    the event alone -- with the register environment, loops and thread that were
    recorded for its label -- followed by [structure].

    This is how the structure's own tables get built. The ones in [events] are
    the interpreter's working record of every event it has created; the
    structure's describe the events that are in it. *)
let prefix (events : events_t) (event : event) structure phi defacto =
  let find tbl = Hashtbl.find_opt tbl event.label in
    EventStructure.seq
      (EventStructure.singleton ?env:(find events.env_by_evt)
         ?loops:(find events.loop_indices) ?thread:(find events.thread_index)
         event phi defacto
      )
      structure

(** Record a loop's continuation guard for one occurrence of the loop.

    The guard is what decides whether the iteration just interpreted is followed
    by another, so it must be evaluated at the {e end} of the loop body: it is a
    predicate over the symbols that iteration produced. Guards accumulate rather
    than overwrite, because the same loop is interpreted once per enclosing
    branch, per copy of an unravelled do-loop body, and per thread.

    @param events The global events structure.
    @param loop_index The loop's identifier, if the node carries one.
    @param condition The guard as evaluated at the end of the body.
    @return Unit. *)
let record_loop_condition (events : events_t) loop_index condition =
  Option.iter
    (fun lid ->
      let recorded =
        Hashtbl.find_opt events.loop_conditions lid |> Option.value ~default:[]
      in
        if not (List.exists (Expr.equal condition) recorded) then
          Hashtbl.replace events.loop_conditions lid (recorded @ [ condition ])
    )
    loop_index

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

    [structure] is left as it was: [dot] hands its operand's [rmw] set on to its
    result, so adding to that set in place would also add the edge to every
    structure the operand was ever prefixed into.

    @param structure The event structure to extend.
    @param er The label of the read event.
    @param ew The label of the write event.
    @return A new event structure with the RMW edge added. *)
let add_rmw_edge (structure : symbolic_event_structure) (er : int) (cond : expr)
    (ew : int) =
  {
    structure with
    rmw = USet.union structure.rmw (USet.singleton (er, cond, ew));
  }

(** {1 Threads as Fragments} *)

(** [interpret_thread events interpret env phi] is the structure [interpret]
    builds for one thread of a parallel block, entered in [env] under [phi].

    The thread is interpreted as a fragment: in an [events_t] of its own, whose
    allocator hands out labels from [0] and adds events to thread [0]. The
    fragment is then relabelled into place -- its labels shifted by the number
    [events] has handed out, its thread indices by the number of threads -- and
    its working tables added to [events]. The offset counts what was handed out,
    not what made it into a structure: an elided branch has taken a label too.
    Laid out in program order like this, the relabelled fragment is the
    structure interpreting the thread in place would have built (S1, #14).

    Symbols are not the fragment's own: its allocator carries on from where the
    enclosing one is, and the enclosing one then carries on from where the
    fragment's stopped. A symbol's name is not only a name. [Expr.evaluate]
    orders operands by it, so naming the fragment's symbols from α and renaming
    them afterwards gives [(一 != β)] where interpreting in place gives
    [(β != 一)] (programs/cas-increment-race.lit). Labels appear in no expression
    and can be shifted freely. *)
let interpret_thread (events : events_t) interpret env phi =
  let fragment =
    {
      (create_events ~ubopt:events.ubopt events.defacto) with
      globals = events.globals;
      alloc = Allocator.fragment events.alloc;
    }
  in
  let structure = interpret env phi fragment in
  let off = Allocator.labels events.alloc
  and thread_off = events.threads_allocated + 1 in
  let label l = l + off in
  let into tbl k v =
    Hashtbl.iter (fun x y -> Hashtbl.replace tbl (k x) (v y))
  in
    into events.events label
      (fun (ev : event) -> { ev with label = label ev.label })
      fragment.events;
    into events.origin Fun.id label fragment.origin;
    into events.env_by_evt label Fun.id fragment.env_by_evt;
    into events.thread_index label (( + ) thread_off) fragment.thread_index;
    into events.loop_indices label Fun.id fragment.loop_indices;
    into events.source_spans label Fun.id fragment.source_spans;
    Hashtbl.iter
      (fun lid guards ->
        List.iter (fun g -> record_loop_condition events (Some lid) g) guards
      )
      fragment.loop_conditions;
    Allocator.resume events.alloc ~after:fragment.alloc;
    events.threads_allocated <- thread_off + fragment.threads_allocated;
    EventStructure.relabel ~off ~thread_off structure

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
      let structure =
        match stmt with
        | Threads { threads } ->
            let threads_structure =
              List.fold_left
                (fun acc t ->
                  EventStructure.par acc
                    (interpret_thread events (recurse t) env phi)
                )
                (EventStructure.empty ()) threads
            in
              (* The continuation is the join.  Every other branch here composes
                 with [recurse rest ...]; this one used to return the cross
                 product and stop, so a statement after a parallel block
                 contributed no event, bound no register, and an assertion over
                 one of its registers was decided against a free variable (#81).

                 [seq] orders the whole block before the continuation and records
                 the pairs in [fj], which is what [Assertion]'s rhb and
                 [Elaborations] have always read and nothing has ever written.

                 [env] rather than anything the threads produced: a register
                 assigned inside a thread is thread-local, and [update_env]
                 copies, so the threads cannot have changed this one.  The
                 continuation sees the environment the block was entered with,
                 which is what a join gives it. *)
              if rest = [] then threads_structure
              else
                let cont = recurse rest env phi events in
                  EventStructure.seq ~join:true threads_structure cont
        | RegisterStore { register; expr } ->
            let expr_value, env = ub_assume events env expr in
            let env' = update_env env register expr_value in
            let cont = recurse rest env' phi events in
              cont
        | RegisterRefAssign { register; global } ->
            (* A global whose address is taken is as distinct from the others as
               one named by a load or a store. Only those used to be recorded,
               so a global reached only through a reference could share its
               location with any other, and forwarding and elaboration, which
               read [constraints], treated a write through it as possibly
               overwriting every global. *)
            USet.add events.globals global |> ignore;
            let env' = update_env env register (EVar global) in
            let cont = recurse rest env' phi events in
              cont
        | GlobalStore { global; expr; assign } ->
            let wval, env = ub_assume events env expr in
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
                @ ub_facts env
              in
              let cont = recurse rest env phi events in
                prefix events event' cont phi defacto
        | DerefStore { address; expr; assign } ->
            let loc = Expr.evaluate ~env:(Hashtbl.find_opt env) address in
            let wval, env = ub_assume events env expr in
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
              @ ub_facts env
            in
            let cont = recurse rest env phi events in
              prefix events event' cont phi defacto
        | DerefLoad { register; address; load } ->
            let symbol = Allocator.next_greek events.alloc in
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
                @ ub_facts env
              in
              let env' = Hashtbl.copy env in
                Hashtbl.replace env' register (Expr.of_value rval);
                let cont = recurse rest env' phi events in
                  prefix events event' cont phi defacto
        | GlobalLoad { register; global; load } ->
            let symbol = Allocator.next_greek events.alloc in
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
                  @ ub_facts env
                in

                let env' = Hashtbl.copy env in
                  Hashtbl.replace env' register (Expr.of_value rval);
                  let cont = recurse rest env' phi events in
                    prefix events event' cont phi defacto
        | Fadd { register; address; operand; rmw_mode; load_mode; assign_mode }
          ->
            let loc = Expr.evaluate ~env:(Hashtbl.find_opt env) address in
            let symbol = Allocator.next_greek events.alloc in
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
                |> apply_ub_constraints events
              in
              (* if the operand evaluates to zero, this is a read-don't
                   modify-write *)
              let is_rdmw =
                Expr.evaluate ~env:(Hashtbl.find_opt env) operand = ENum Z.zero
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
                @ ub_facts env
              in

              let env' = Hashtbl.copy env in
                Hashtbl.replace env' register result_expr;
                let cont = recurse rest env' phi events in
                  add_rmw_edge
                    (prefix events event_load'
                       (prefix events event_store' cont phi defacto)
                       phi defacto
                    )
                    event_load'.label (EBoolean true) event_store'.label
        | Cas { register; address; expected; desired; load_mode; assign_mode }
          ->
            let loc = Expr.evaluate ~env:(Hashtbl.find_opt env) address in
            let symbol = Allocator.next_greek events.alloc in
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
              let branch_event =
                { (Event.create Branch 0 ()) with cond = Some cond_expr }
              in
              let branch_event' =
                add_event events branch_event env annotation
              in

              let base_evt_store : event = Event.create Write 0 () in
              let wval =
                Expr.evaluate ~env:(Hashtbl.find_opt env) desired
                |> apply_ub_constraints events
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
              let phi_fail = (Expr.inverse cond_expr |> Expr.evaluate) :: phi in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
                @ ub_facts env
              in

              let env_succ = Hashtbl.copy env in
              let env_fail = Hashtbl.copy env in
                Hashtbl.replace env_succ register (ENum Z.one);
                Hashtbl.replace env_fail register (ENum Z.zero);
                let cont_succ = recurse rest env_succ phi_succ events in
                let cont_fail = recurse rest env_fail phi_fail events in
                  prefix events event_load'
                    (prefix events branch_event'
                       (EventStructure.choice
                          (add_rmw_edge
                             (prefix events event_store' cont_succ phi_succ
                                defacto
                             )
                             event_load'.label cond_expr event_store'.label
                          )
                          cont_fail
                       )
                       phi defacto
                    )
                    phi defacto
        | If { condition; then_body; else_body } -> (
            (* TODO prune semantically impossible branches against phi *)
            let cond_val =
              Expr.evaluate ~env:(Hashtbl.find_opt env) condition
              |> apply_ub_constraints events
            in
            let new_then_phi =
              if cond_val = EBoolean true then phi else cond_val :: phi
            in
            let new_then_phi_sat = Solver.is_sat_cached new_then_phi in
            let new_then_phi =
              if new_then_phi_sat then new_then_phi else [ EBoolean false ]
            in
            let cond_val =
              if new_then_phi_sat then cond_val else EBoolean false
            in
            let else_cond_val = Expr.evaluate (Expr.inverse cond_val) in
            let new_else_phi =
              if cond_val = EBoolean false then phi else else_cond_val :: phi
            in
            let new_else_phi_sat = Solver.is_sat_cached new_else_phi in
            let else_cond_val =
              if new_else_phi_sat then else_cond_val else EBoolean false
            in
            let new_else_phi =
              if new_else_phi_sat then new_else_phi else [ EBoolean false ]
            in

            let then_structure events =
              recurse (then_body @ rest) env new_then_phi events
            in

            let defacto =
              List.map
                (Expr.evaluate ~env:(Hashtbl.find_opt env))
                events.defacto
              @ ub_facts env
            in
            let branch_event =
              { (Event.create Branch 0 ()) with cond = Some cond_val }
            in
            let branch_event' = add_event events branch_event env annotation in

            match else_body with
            | Some eb -> (
                let else_structure events =
                  recurse (eb @ rest) env new_else_phi events
                in

                match cond_val with
                | EBoolean true -> then_structure events
                | EBoolean false -> else_structure events
                | _ ->
                    let then_structure = then_structure events in
                    let else_structure = else_structure events in
                      prefix events branch_event'
                        (EventStructure.choice then_structure else_structure)
                        phi defacto
              )
            | None -> (
                match cond_val with
                | EBoolean false -> recurse rest env phi events
                | EBoolean true -> then_structure events
                | _ ->
                    let then_structure = then_structure events in
                    let rest_structure = recurse rest env new_else_phi events in
                      prefix events branch_event'
                        (EventStructure.choice then_structure rest_structure)
                        phi defacto
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
              @ ub_facts env
            in

            let cont = recurse rest env phi events in
              prefix events event' cont phi defacto
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
              @ ub_facts env
            in

            let cont = recurse rest env phi events in
              prefix events event' cont phi defacto
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
              @ ub_facts env
            in

            let cont = recurse rest env phi events in
              prefix events event' cont phi defacto
        | RegMalloc { register; size } ->
            let symbol = Allocator.next_zh events.alloc in
            let rval = VSymbol symbol in
            let loc = ESymbol symbol in
            let base_evt : event = Event.create Malloc 0 () in
            (* The size expression is recorded in [wval]. It was dropped, so an
               allocation carried no dependency on a size it computed from a
               read; pre-justifications take an allocation's dependencies from
               it. *)
            let size' = Expr.evaluate ~env:(Hashtbl.find_opt env) size in
            let evt =
              {
                base_evt with
                rval = Some rval;
                loc = Some loc;
                wval = Some size';
              }
            in
            let event' : event = add_event events evt env annotation in
              Hashtbl.replace events.origin symbol event'.label;
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
                @ ub_facts env
              in

              let env' = Hashtbl.copy env in
                Hashtbl.replace env' register (Expr.of_value rval);
                let cont = recurse rest env' phi events in

                prefix events event' cont phi defacto
        | GlobalMalloc { global; size } ->
            (* The allocation, then a store of its address to the global: two
               events, as [r := malloc n; x := r] would be. The store used to be
               missing, so the global never held the address and a load from it
               read whatever it held before. *)
            let symbol = Allocator.next_zh events.alloc in
            let rval = VSymbol symbol in
            let loc = ESymbol symbol in
            let base_evt : event = Event.create Malloc 0 () in
            let size' = Expr.evaluate ~env:(Hashtbl.find_opt env) size in
            let evt =
              {
                base_evt with
                rval = Some rval;
                loc = Some loc;
                wval = Some size';
              }
            in
            let event' : event = add_event events evt env annotation in
              USet.add events.globals global |> ignore;
              Hashtbl.replace events.origin symbol event'.label;
              let store =
                {
                  (Event.create Write 0 ()) with
                  id = Some (VVar global);
                  loc = Some (EVar global);
                  wval = Some loc;
                  wmod = Relaxed;
                  volatile = false;
                }
              in
              let store' : event = add_event events store env annotation in
              let defacto =
                List.map
                  (Expr.evaluate ~env:(Hashtbl.find_opt env))
                  events.defacto
                @ ub_facts env
              in

              let cont = recurse rest env phi events in

              prefix events event'
                (prefix events store' cont phi defacto)
                phi defacto
        | Free { register } ->
            let base_evt : event = Event.create Free 0 () in
            let loc = Hashtbl.find_opt env register in
            let evt = { base_evt with loc } in
            let event' : event = add_event events evt env annotation in
            let defacto =
              List.map
                (Expr.evaluate ~env:(Hashtbl.find_opt env))
                events.defacto
              @ ub_facts env
            in

            let cont = recurse rest env phi events in
              prefix events event' cont phi defacto
        | Skip ->
            let cont = recurse rest env phi events in
              cont
        | _ ->
            (* Simplified - return empty structure for unhandled cases *)
            Logs_safe.err (fun m ->
                m "Statement not handled: %s" (ir_node_to_string node)
            );
            EventStructure.empty ()
      in
        structure

(** {1 Terminal Structure} *)

(** Create a generic terminal structure with a terminal event.

    @param add_event Function to add events to the global table.
    @param env The current register environment.
    @param phi The current path condition.
    @param events The global events structure.
    @return A symbolic event structure with a terminal event. *)
let make_generic_terminal_structure ~add_event env phi events =
  let terminal_evt = Event.create Terminal 0 () in
  let terminal_evt : event =
    add_event events terminal_evt env
      { source_span = None; thread_ctx = None; loop_ctx = None }
  in
  let defacto =
    List.map (Expr.evaluate ~env:(Hashtbl.find_opt env)) events.defacto
    @ ub_facts env
  in
    prefix events terminal_evt (EventStructure.empty ()) phi defacto

(** [distinctness globals structure] is what the program says about its
    locations: [globals] are pairwise distinct, and the allocations of
    [structure] are pairwise distinct and distinct from every global.

    It is a property of the whole program and is computed once, from the
    finished structure. It used to be attached to each terminal structure,
    computed from what interpretation had seen by then -- a thread's terminal
    knew nothing of an allocation in the next thread -- and the structure's list
    was the concatenation of them all. The last terminal had seen everything, so
    the union is this list, with duplicates. *)
let distinctness globals (structure : symbolic_event_structure) =
  let global_constraints =
    URelation.cross globals globals
    |> (fun rel -> USet.set_minus rel (URelation.identity globals))
    |> USet.values
    |> List.map (fun (g1, g2) -> if g1 < g2 then (g1, g2) else (g2, g1))
    |> List.sort_uniq (fun (a1, b1) (a2, b2) ->
        let c = compare a1 a2 in
          if c <> 0 then c else compare b1 b2
    )
    |> List.map (fun (v1, v2) -> Expr.binop (EVar v1) "!=" (EVar v2))
  in
  (* Distinct allocations denote distinct locations: a [malloc] never hands back
     the address of another allocation. Without this the solver may equate two
     allocation symbols, and then a write to one allocation reads as a possible
     source for a read of the other. *)
  let allocation_constraints =
    let locations =
      Hashtbl.fold
        (fun _ (event : event) acc ->
          match (event.typ, event.loc) with
          | Malloc, Some loc -> loc :: acc
          | _ -> acc
        )
        structure.events []
      |> List.sort_uniq Expr.compare
    in
    let rec distinct_pairs = function
      | [] -> []
      | loc :: rest ->
          List.map (fun other -> Expr.binop loc "!=" other) rest
          @ distinct_pairs rest
    in
      (* An allocation is also disjoint from every object that already exists:
         C guarantees a fresh region does not overlap them, and the papers'
         LB+alias+data turns on exactly that — the allocation of p is what lets
         *p and x be told apart, and so lets the two accesses be reordered. *)
      List.concat_map
        (fun loc ->
          USet.values globals |> List.map (fun g -> Expr.binop loc "!=" (EVar g))
        )
        locations
      @ distinct_pairs locations
  in
    global_constraints @ allocation_constraints

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
let interpret_generic ?(ubopt = false) ~stmt_semantics ~defacto ~constraints
    stmts =
  (* Events context *)
  let events = create_events ~ubopt defacto in
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
  let structure = stmt_semantics stmts env [] events in

  (* Prefix with initial event *)
  let defacto =
    List.map (Expr.evaluate ~env:(Hashtbl.find_opt env)) events.defacto
    @ ub_facts env
  in
  let structure = prefix events init_event' structure [] defacto in

  (* The per-event tables are the structure's own by now; [dot] built them.
     The loop guards are still handed over whole: they are keyed by loop, not
     by event, and accumulate one per interpreted occurrence. The constraints
     are about the program as a whole. *)
  let structure =
    {
      structure with
      loop_conditions = events.loop_conditions;
      constraints = distinctness events.globals structure;
    }
  in

  (structure, events.source_spans)

(** Default interpretation function with basic statement semantics.

    @param defacto Optional de facto constraints.
    @param constraints Optional additional constraints.
    @param stmts The program statements to interpret.
    @return
      A tuple of (symbolic event structure, events table, source spans table).
*)
let interpret ?(ubopt = false) ?(defacto = None) ?(constraints = None) stmts =
  let defacto = defacto |> Option.value ~default:[] in
    interpret_generic ~ubopt ~stmt_semantics:interpret_statements ~defacto
      ~constraints stmts

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
        let structure, source_spans =
          interpret_generic ~ubopt:ctx.options.ubopt ~stmt_semantics ~defacto
            ~constraints stmts
        in
          Logs_safe.debug (fun m ->
              m "Completed program interpretation: \n%s\nand events\n%s"
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
        Logs_safe.err (fun m -> m "No program statements for interpretation.");
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
    if step_counter = 0 then EventStructure.empty ()
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
end

(** {1 Symbolic Loop Semantics} *)

(** S8 (#20): with [compositional_po_iter] set, each interpreted occurrence of a
    loop adds to its own structure's [po_iter] the pairs of its body's events,
    and interpretation keeps that rather than rebuilding [po_iter] from
    [loop_indices] at the end. Off by default; enabled via
    [MORDOR_S8_COMPOSITIONAL_PO_ITER]. *)
module S8 = struct
  let compositional_po_iter =
    ref (Option.is_some (Sys.getenv_opt "MORDOR_S8_COMPOSITIONAL_PO_ITER"))
end

(** Symbolic loop semantics for unbounded loops.

    Loop iterations are tracked symbolically: all branches are evaluated.
    Semantics is in general not sound unless all loops are episodic. Semantics
    is sufficient to establish episodicity criteria. *)
module SymbolicLoopSemantics : sig
  (** Pipeline step for interpreting with symbolic loop semantics.

      @param ctx The Mordor context.
      @return Updated context with interpretation results. *)
  val step_interpret : mordor_ctx Lwt.t -> mordor_ctx Lwt.t
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
    Logs_safe.debug (fun m ->
        m "Generating program order relations for symbolic loop semantics."
    );
    Logs_safe.debug (fun m ->
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
      Logs_safe.debug (fun m ->
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
          (* [po_iter] is the accumulator: each loop's non-identity pairs
             are folded into it and it is returned below. *)
          USet.inplace_union ~into:po_iter
            (URelation.identity events
            |> USet.set_minus (URelation.cross events events)
            )
          |> ignore
        )
        events_by_loop;
      po_iter

  (** Strip loop membership from the peeled first unravelling of a do-while
      body.

      In [do { body } while (cond)] the first unravelling precedes the residual
      [while (cond) { body }], so — exactly as in the hand-written
      [body; while (cond) { body }] — its events are not iterations of the loop.
      Only the residual loop's copy of [body] is the loop's symbolic iteration,
      which is what [generate_po_iter] and the episodicity checks expect: one
      symbolic iteration per loop.

      The same applies to any loop nested in [body]: its peeled copy would
      otherwise duplicate the nested loop's events. [outer_loops] is therefore
      the enclosing loop path of the do-while itself, applied throughout. The
      [lid] of a nested loop node is preserved so that it still records its
      guard under its own identifier.

      @param outer_loops The enclosing loop path of the do-while node.
      @param node The IR node to strip.
      @return The node with loop membership replaced by [outer_loops]. *)
  let rec peel_loop_membership outer_loops (node : ir_node) : ir_node =
    let peel = peel_loop_membership outer_loops in
    let loop_ctx =
      node.annotations.loop_ctx
      |> Option.map (fun (ctx : loop_ctx) -> { ctx with loops = outer_loops })
    in
    let annotations = { node.annotations with loop_ctx } in
    let stmt : ir_stmt =
      match node.stmt with
      | While { condition; body } ->
          While { condition; body = List.map peel body }
      | Do { body; condition } -> Do { body = List.map peel body; condition }
      | If { condition; then_body; else_body } ->
          If
            {
              condition;
              then_body = List.map peel then_body;
              else_body = Option.map (List.map peel) else_body;
            }
      | Labeled { label; stmt } -> Labeled { label; stmt = peel stmt }
      | stmt -> stmt
    in
      { stmt; annotations }

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
            (* [do { body } while (cond)] is one unravelling of the loop body
               followed by [while (cond) { body }], and is interpreted as
               exactly that: the body, with the residual while loop as its
               continuation.

               The unravelling cannot be done syntactically on the IR, because
               the branch event of the residual while loop has to be evaluated
               in the environment reached at the *end* of the first
               unravelling — that is what makes the loop condition track this
               iteration. Threading the residual loop through the
               [final_structure] of the first unravelling puts it in exactly
               that position. *)
            let residual_while ~add_event env phi events =
              interpret_while_symbolic_loop ~final_structure ~add_event
                ~annotations:node.annotations ~condition ~body ~rest env phi
                events
            in
            let outer_loops =
              node.annotations.loop_ctx
              |> Option.map (fun (ctx : loop_ctx) -> ctx.loops)
              |> Option.value ~default:[]
            in
            let peeled = List.map (peel_loop_membership outer_loops) body in
              interpret_statements_symbolic_loop ~final_structure:residual_while
                ~add_event peeled env phi events
        | While { condition; body } ->
            interpret_while_symbolic_loop ~final_structure ~add_event
              ~annotations:node.annotations ~condition ~body ~rest env phi
              events
        | _ ->
            let recurse nodes env phi events =
              interpret_statements_symbolic_loop ~final_structure ~add_event
                nodes env phi events
            in
              interpret_statements_open ~recurse ~final_structure ~add_event
                nodes env phi events
      )
    | [] -> final_structure ~add_event env phi events

  (** Interpret a while loop with symbolic loop semantics.

      Shared by [While] and by the residual loop of a [Do], which is a while
      loop preceded by one unravelling of its body.

      @param final_structure Function to create the final structure.
      @param add_event Function to add events.
      @param annotations The IR annotations of the loop node.
      @param condition The loop guard.
      @param body The loop body.
      @param rest The continuation after the loop.
      @param env The register environment.
      @param phi The path condition.
      @param events The global events structure.
      @return A symbolic event structure. *)
  and interpret_while_symbolic_loop ~final_structure ~add_event ~annotations
      ~condition ~body ~rest env phi events =
    (* A while loop with a single symbolic unrolling is modelled as a branch,
       mirroring the [If { else_body = None }] encoding: either the guard holds
       and we run the body once before the continuation (iteration order is
       recovered later via po_iter), or the guard fails and we proceed directly
       to the continuation.

       Crucially, the two branches must own DISTINCT continuation events.
       Interpreting [rest] separately in each branch is what keeps the [plus]
       operands disjoint. The previous implementation shared a single
       [after_structure] between the body's continuation and the exit branch,
       so [plus] (which adds an all-pairs conflict between its operands) put
       the shared continuation events in conflict with themselves and with the
       po-preceding body, yielding a malformed structure with no valid
       executions. *)
    let cond_val =
      Expr.evaluate ~env:(fun v -> Hashtbl.find_opt env v) condition
      |> apply_ub_constraints events
    in
    let enter_phi = if cond_val = EBoolean true then phi else cond_val :: phi in
    let enter_phi_sat = Solver.is_sat_cached enter_phi in
    let enter_phi = if enter_phi_sat then enter_phi else [ EBoolean false ] in
    let cond_val = if enter_phi_sat then cond_val else EBoolean false in
    let exit_cond_val = Expr.evaluate (Expr.inverse cond_val) in
    let exit_phi =
      if cond_val = EBoolean false then phi else exit_cond_val :: phi
    in
    let exit_phi_sat = Solver.is_sat_cached exit_phi in
    let exit_phi = if exit_phi_sat then exit_phi else [ EBoolean false ] in
    let loop_index =
      annotations.loop_ctx |> Option.map (fun (ctx : loop_ctx) -> ctx.lid)
    in
    (* S8: this occurrence's iterations, from its own body alone -- the events
       of the entering branch that are in the loop -- rather than from every
       event of the program the loop's index was ever stamped on. *)
    let iterations (s : symbolic_event_structure) =
      match (!S8.compositional_po_iter, loop_index) with
      | true, Some lid ->
          let body =
            USet.filter
              (fun e ->
                Hashtbl.find_opt s.loop_indices e
                |> Option.fold ~none:false ~some:(List.mem lid)
              )
              s.e
          in
            {
              s with
              po_iter =
                USet.union s.po_iter
                  (USet.set_minus
                     (URelation.cross body body)
                     (URelation.identity body)
                  );
            }
      | _ -> s
    in
    let defacto =
      List.map (Expr.evaluate ~env:(Hashtbl.find_opt env)) events.defacto
      @ ub_facts env
    in
    (* Continue branch: run the body once, then the continuation.

         The body is interpreted with the continuation as its own
         [final_structure] so that the loop's guard can be recorded there, in
         the environment reached at the end of the body. That is the guard that
         decides whether the iteration just modelled is followed by another —
         [cond_val] above is the guard of the iteration {e before} it, and says
         nothing about this one. Every path through the body records its own,
         which is also what keeps occurrences of the same loop from overwriting
         one another. *)
    let enter_structure events =
      let continue_after_body ~add_event env phi events =
        let guard =
          Expr.evaluate ~env:(Hashtbl.find_opt env) condition
          |> apply_ub_constraints events
        in
          (* Conjoined with the path condition reached at the end of the body,
             so the guard says "the loop continues after this iteration, along
             this path" rather than "along some path". A write reachable only on
             another path through the body is then inconsistent with it, instead
             of being kept alive by a sibling path's guard. *)
          record_loop_condition events loop_index
            (List.fold_left
               (fun conjunction p -> Expr.binop conjunction "&&" p)
               guard phi
            |> Expr.evaluate
            |> apply_ub_constraints events
            );
          interpret_statements_symbolic_loop ~final_structure ~add_event rest
            env phi events
      in
        interpret_statements_symbolic_loop ~final_structure:continue_after_body
          ~add_event body env enter_phi events
    in
    (* Exit branch: skip the body, go straight to the continuation. *)
    let exit_structure events =
      interpret_statements_symbolic_loop ~final_structure ~add_event rest env
        exit_phi events
    in
      match cond_val with
      | EBoolean true -> iterations (enter_structure events)
      | EBoolean false -> exit_structure events
      | _ ->
          let branch_event =
            { (Event.create Branch 0 ()) with cond = Some cond_val }
          in
          let branch_event' = add_event events branch_event env annotations in
          let enter_structure = iterations (enter_structure events) in
          let exit_structure = exit_structure events in
            prefix events branch_event'
              (EventStructure.choice enter_structure exit_structure)
              phi defacto

  let step_interpret lwt_ctx =
    let* ctx = lwt_ctx in
    let stmt_semantics =
      interpret_statements_symbolic_loop
        ~final_structure:make_generic_terminal_structure ~add_event
    in
    let lwt_ctx = generic_step_interpret ~stmt_semantics lwt_ctx in
      let* ctx = lwt_ctx in
        if not !S8.compositional_po_iter then
          ctx.structure <-
            Some
              {
                (Option.get ctx.structure) with
                po_iter = generate_po_iter (Option.get ctx.structure);
              };
        Lwt.return ctx
end

(** {1 Main Pipeline Step} *)

(** Main interpretation pipeline step.

    Selects the appropriate loop semantics based on context options and performs
    program interpretation.

    @param lwt_ctx The Mordor context.
    @return Updated context with interpretation results. *)
let step_interpret lwt_ctx =
  let* ctx = lwt_ctx in
    Progress.stage ~unit:"" "interpret" @@ fun () ->
    Logs_safe.debug (fun m ->
        m "Interpreting program with %s loop semantics."
          ( match ctx.options.loop_semantics with
          | Symbolic -> "symbolic"
          | StepCounterPerLoop -> "step counter per loop"
          | FiniteStepCounter -> "finite step counter"
          | Generic -> "generic"
          )
    );
    match ctx.options.loop_semantics with
    | FiniteStepCounter | StepCounterPerLoop ->
        StepCounterSemantics.step_interpret lwt_ctx
    | Symbolic -> SymbolicLoopSemantics.step_interpret lwt_ctx
    | Generic ->
        generic_step_interpret ~stmt_semantics:interpret_statements lwt_ctx
