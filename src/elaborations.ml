(** Elaboration algorithms for symbolic event structures.

    This module implements the core elaboration algorithms that transform and
    refine justifications in symbolic event structures. The elaborations include
    value assignment, forwarding, lifting, and weakening operations that
    progressively build up execution models. *)

open Algorithms
open Context
open Expr
open Forwarding
open Justifications
open Lwt.Syntax
open Types
open Uset

(** {1 Foundational Types} *)

(** Elaboration operation for tracing. *)
type op =
  | PreJustification
  | ValueAssignElab of justification
  | Forwarding of justification
  | LiftElab of justification * justification
  | WeakElab of justification

(** Pretty print elaboration operation for tracing. *)
let op_to_string = function
  | PreJustification -> "PreJustification"
  | ValueAssignElab just ->
      Printf.sprintf "ValueAssignElab %s" (Justification.to_string just)
  | Forwarding just ->
      Printf.sprintf "Forwarding %s" (Justification.to_string just)
  | LiftElab (just1, just2) ->
      Printf.sprintf "LiftElab %s and %s"
        (Justification.to_string just1)
        (Justification.to_string just2)
  | WeakElab just -> Printf.sprintf "WeakElab %s" (Justification.to_string just)

module OpTraceTable = Hashtbl.Make (JustificationCacheKey)

(** Thread-safe wrapper around [OpTraceTable].

    Concurrent elaboration passes write to the trace from multiple Lwt threads.
    All mutations are serialised through an [Lwt_mutex] so that interleaving at
    Lwt yield points cannot corrupt the underlying hash table. *)
module OpTrace = struct
  type 'a t = { tbl : 'a OpTraceTable.t; mutex : Mutex.t }

  let create n = { tbl = OpTraceTable.create n; mutex = Mutex.create () }

  (** [add t key value] appends [value] for [key] under the mutex. *)
  let add t key value =
    Mutex.lock t.mutex;
    OpTraceTable.add t.tbl key value;
    Mutex.unlock t.mutex;
    ()

  (** [find_opt t key] looks up [key] under the mutex. *)
  let find_opt t key =
    Mutex.lock t.mutex;
    let result = OpTraceTable.find_opt t.tbl key in
      Mutex.unlock t.mutex;
      result
end

(** Elaboration context containing the symbolic event structure and caches.

    Bundles together all the state needed during elaboration including the event
    structure, fork-join edges, and various caches. *)
type context = {
  structure : symbolic_event_structure;
      (** The symbolic event structure being elaborated. *)
  fwd_es_ctx : Forwarding.event_structure_context;
  fj : (int * int) USet.t;  (** Fork-join edges that constrain forwarding. *)
  op_trace : op OpTrace.t;
      (** Cache of operations performed on justifications to avoid redundancy.
      *)
}

let pred_landmark = Landmark.register "Elaborations.pred"

(** [pred elab_ctx ctx p ?ppo ()] computes the predecessor function.

    Returns a function mapping each event to its set of immediate predecessors
    in the preserved program order relation.

    @param elab_ctx The elaboration context.
    @param ctx Optional forwarding context for computing PPO.
    @param p Optional predicate list for computing PPO.
    @param ppo Optional pre-computed PPO relation to avoid recomputation.
    @return Promise of a function from events to their predecessor sets. *)
let pred (elab_ctx : context) (ctx : ForwardingContext.t option)
    (p : expr list option) ?ppo () =
  Landmark.enter pred_landmark;
  let ppo_result =
    match ppo with
    | Some ppo_val -> ppo_val
    | None -> (
        match (ctx, p) with
        | Some ctx_val, Some p_val -> ForwardingContext.ppo ctx_val p_val
        | _ -> failwith "ctx and p must be provided when ppo is not given"
      )
  in
  let immediate_ppo = URelation.transitive_reduction ppo_result in
  let inversed = URelation.inverse immediate_ppo in
  let tree = URelation.adjacency_map inversed in
    Landmark.exit pred_landmark;
    fun e -> Hashtbl.find_opt tree e |> Option.value ~default:(USet.create ())

(** [pre_justifications structure] computes initial pre-justifications.

    Generates pre-justifications for write, allocation, and free events based on
    value restrictions and symbols used in predicates and values.

    @param structure The symbolic event structure.
    @return Set of pre-justifications with empty forwarding contexts. *)
let pre_justifications structure =
  let events = structure.events in
  let e_set = structure.e in
  let write_events = structure.write_events in
  let alloc_events = structure.malloc_events in
  let free_events = structure.free_events in
  let prejustifiable_events =
    USet.union write_events alloc_events
    |> USet.union free_events
    |> USet.values
  in
    List.map
      (fun w ->
        try
          let event = Hashtbl.find events w in
            {
              p =
                Hashtbl.find_opt structure.restrict event.label
                |> Option.value ~default:[];
              d =
                ( if USet.mem structure.malloc_events w then USet.create ()
                  else
                    USet.flatten
                      (USet.map
                         (fun (e_opt : expr option) : string uset ->
                           match e_opt with
                           | Some e -> USet.of_list (Expr.get_symbols e)
                           | None -> USet.create ()
                         )
                         (USet.of_list
                            [
                              event.loc;
                              Option.map Expr.of_value event.rval;
                              event.wval;
                            ]
                         )
                      )
                );
              fwd = USet.create ();
              we = USet.create ();
              w = event;
            }
        with Not_found -> failwith "Event not found"
      )
      prejustifiable_events
    |> List.filter (fun prejust -> Solver.is_sat_cached prejust.p)

(** {1 Value Assignment Elaboration} *)

module ValueAssignElab = struct
  (** [elab elab_ctx just] performs value assignment elaboration.

      For the given justification, attempts to find a satisfying model and
      assigns concrete values to symbolic write values where possible.

      @param elab_ctx The elaboration context.
      @param just The justification to elaborate.
      @return Promise of justifications with assigned values. *)
  let elab elab_ctx just =
    let structure = elab_ctx.structure in
    let fwd_ctx =
      ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:just.fwd ~we:just.we ()
    in
    let defacto =
      Hashtbl.find_opt elab_ctx.structure.defacto just.w.label
      |> Option.value ~default:[]
    in
    let solver = Solver.create (just.p @ fwd_ctx.psi @ defacto) in
    let model = Solver.solve solver in
      match model with
      | Some bindings ->
          if Option.is_none just.w.wval then
            (* Free or allocation event *)
            []
          else
            let wval =
              Option.get just.w.wval
              |> Expr.evaluate ~env:(fun s ->
                  Solver.concrete_value bindings s |> Option.map Expr.of_value
              )
            in
            let p =
              Expr.evaluate_conjunction
                ~env:(fun s ->
                  Solver.concrete_value bindings s |> Option.map Expr.of_value
                )
                just.p
            in
              if
                Expr.equal (Option.get just.w.wval) wval
                && List.length p = List.length just.p
                && List.equal Expr.equal p just.p
              then []
              else
                (* Reconstruct dependencies from predicate and write value *)
                let new_p_d =
                  List.map Expr.get_symbols p |> List.flatten |> USet.of_list
                in
                let new_w_d = Expr.get_symbols wval |> USet.of_list in
                let d = USet.union new_p_d new_w_d in
                let w = { just.w with wval = Some wval } in
                  [ { just with w; d; p } ]
      | None -> []
end

(** {1 Forwarding Elaboration} *)

module ForwardElab = struct
  (** [fprime elab_ctx pred_fn ppo_loc just e1 e2] checks forwarding condition.

      Tests if events [e1] and [e2] satisfy the forwarding prime condition: they
      are ordered in [ppo_loc], [e1] is a predecessor of [e2], and their
      locations are equal under the current predicate constraints.

      @param elab_ctx The elaboration context.
      @param pred_fn Function mapping events to their predecessors.
      @param ppo_loc Location-based preserved program order.
      @param just The justification providing constraint context.
      @param e1 First event.
      @param e2 Second event.
      @return Promise of [true] if condition holds. *)
  let fprime elab_ctx pred_fn ppo_loc just e1 e2 =
    if USet.mem ppo_loc (e1, e2) && USet.mem (pred_fn e2) e1 then
      (* TODO use of get_loc misses effects of value assignment elaboration *)
      let loc1 = Events.get_loc elab_ctx.structure e1 in
      let loc2 = Events.get_loc elab_ctx.structure e2 in
        match (loc1, loc2) with
        | Some l1, Some l2 -> Solver.exeq ~state:just.p l1 l2
        | _ -> false
    else false

  (** [fwd elab_ctx pred_fn ctx ppo_loc just] computes forward edges.

      Finds all valid forwarding edges between write/read events that satisfy
      the forwarding prime condition.

      @param elab_ctx The elaboration context.
      @param pred_fn Predecessor function.
      @param ctx Forwarding context.
      @param ppo_loc Location-based PPO.
      @param just The justification context.
      @return Promise of the set of forwarding edges. *)
  let fwd elab_ctx pred_fn ctx ppo_loc just =
    let write_events = elab_ctx.structure.write_events in
    let read_events = elab_ctx.structure.read_events in
    let rlx_write_events = elab_ctx.structure.rlx_write_events in
    let rlx_read_events = elab_ctx.structure.rlx_read_events in
    let w_cross_r = URelation.cross write_events rlx_read_events in
    let r_cross_r = URelation.cross read_events read_events in
    let w_cross_w = URelation.cross write_events rlx_write_events in
    let combined = USet.union w_cross_r r_cross_r in
    let combined = USet.union combined w_cross_w in
      USet.filter
        (fun (e1, e2) -> fprime elab_ctx pred_fn ppo_loc just e1 e2)
        combined

  (** [we elab_ctx pred_fn ctx ppo_loc just] computes write-exclusion edges.

      Finds all valid write-exclusion edges between write events.

      @param elab_ctx The elaboration context.
      @param pred_fn Predecessor function.
      @param ctx Forwarding context.
      @param ppo_loc Location-based PPO.
      @param just The justification context.
      @return Promise of the set of write-exclusion edges. *)
  let we elab_ctx pred_fn ctx ppo_loc just =
    let write_events = elab_ctx.structure.write_events in
    let w_cross_w = URelation.cross write_events write_events in
      USet.filter
        (fun (e1, e2) -> fprime elab_ctx pred_fn ppo_loc just e1 e2)
        w_cross_w
      |> URelation.inverse

  (** [elab elab_ctx just] performs forwarding elaboration on a justification.

      For the given justification, computes all valid forwarding and
      write-exclusion edges based on the preserved program order and fork-join
      constraints. Each new edge is validated for consistency before being
      added.

      @param elab_ctx The elaboration context.
      @param just The justification to elaborate.
      @return Promise of justifications with added forwarding edges. *)
  let elab elab_ctx just =
    (* Determine paths to check: if available check P or P with program wide
       guarantees. *)
    let defacto =
      Hashtbl.find_opt elab_ctx.structure.defacto just.w.label
      |> Option.value ~default:[]
    in
    let ps =
      if List.length defacto > 0 then [ just.p; just.p @ defacto ]
      else [ just.p ]
    in
    (* Map over each path *)
    let path_results =
      List.map
        (fun p ->
          let fwd_ctx =
            ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:just.fwd
              ~we:just.we ()
          in
          let ppo = ForwardingContext.ppo fwd_ctx p in
          let ppo_loc = ForwardingContext.ppo_loc fwd_ctx p in
          let _pred = pred elab_ctx None None ~ppo () in

          (* Subtract fj from ppo_loc. NOTE DIFFERS in JS:
                     symmrd.ml defines fj as the union of init_ppo (ordering
                     the initial event before any other event and the
                     fork-join edges from the symbolic event structure.
                     Critically, these edges should not be part of forwarding.
                  *)
          let _ppo_loc = USet.set_minus ppo_loc elab_ctx.fj in

          (* Compute fwd and we edges *)
          let _fwd = fwd elab_ctx _pred fwd_ctx _ppo_loc just in
          let _we = we elab_ctx _pred fwd_ctx _ppo_loc just in

          let _fwd =
            USet.filter
              (fun (e1, e2) ->
                e1 > 0
                (* && e2 <> just.w.label *)
                (* NOTE JS disagrees with freeze definition *)
                (* NOTE e1 and e2 are po before w, pulled forward from
                             freeze *)
                && USet.mem elab_ctx.structure.po (e1, just.w.label)
                && (e2 == just.w.label
                   || USet.mem elab_ctx.structure.po (e2, just.w.label)
                   )
              )
              _fwd
          in
          let _we =
            USet.filter
              (fun (e1, e2) ->
                e2 > 0
                (* && e2 <> just.w.label *)
                (* NOTE JS disagrees with freeze definition *)
                (* NOTE e1 and e2 are po before w, pulled forward from
                             freeze *)
                && USet.mem elab_ctx.structure.po (e2, just.w.label)
                && (e1 == just.w.label
                   || USet.mem elab_ctx.structure.po (e1, just.w.label)
                   )
              )
              _we
          in

          (* Filter edge function *)
          let filtedge (edge, new_fwd, new_we) =
            if
              Forwarding.ContextCache.is_bad elab_ctx.fwd_es_ctx.context_cache
                new_fwd new_we
            then false
            else if
              Forwarding.ContextCache.is_good elab_ctx.fwd_es_ctx.context_cache
                new_fwd new_we
            then true
            else
              let con =
                ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:new_fwd
                  ~we:new_we ()
              in
                ForwardingContext.check con
          in

          (* Create fwd edges with contexts *)
          let fwdedges =
            USet.values _fwd
            |> List.map (fun edge ->
                (edge, USet.union just.fwd (USet.singleton edge), just.we)
            )
          in

          (* Create we edges with contexts *)
          let weedges =
            USet.values _we
            |> List.map (fun edge ->
                (edge, just.fwd, USet.union just.we (USet.singleton edge))
            )
          in

          (* Filter both edge types *)
          let filtered_fwd = List.filter filtedge fwdedges in
          let filtered_we = List.filter filtedge weedges in

          (* Remap justifications *)
          let fwd_justs =
            List.map
              (fun (edge, new_fwd, new_we) ->
                let con =
                  ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:new_fwd
                    ~we:new_we ()
                in
                  ForwardingContext.remap_just con just
              )
              filtered_fwd
          in

          let we_justs =
            List.map
              (fun (edge, new_fwd, new_we) ->
                let con =
                  ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:new_fwd
                    ~we:new_we ()
                in
                  ForwardingContext.remap_just con just
              )
              filtered_we
          in

          fwd_justs @ we_justs
        )
        ps
    in
    let results = List.concat path_results in
      results
end

(** {1 LiftElab Elaboration} *)

(** LiftElab elaboration operations.

    Implements the lifting elaboration that combines pairs of justifications for
    conflicting writes by finding relabelings that make their paths equivalent.
*)
module LiftElab : sig
  (** [elab ctx j1 j2] attempts to lift justifications [j1] and [j2].

      For conflicting writes, finds relabelings that make the justifications
      equivalent and produces new lifted justifications.

      @param ctx The elaboration context.
      @param j1 First justification.
      @param j2 Second justification.
      @return Promise of list of lifted justifications. *)
  val elab : context -> justification -> justification -> justification list

  (** [relabel expr pairs] applies symbol relabeling to an expression.

      @param expr The expression to relabel.
      @param pairs Set of [(from, to)] symbol substitution pairs.
      @return The relabeled expression. *)
  val relabel : expr -> (string * string) USet.t -> expr

  (** [find_distinguishing_predicate p1 p2] finds distinguishing predicate.

      Finds a predicate that is positive in [p1] and negative in [p2], or vice
      versa, along with common predicates.

      @param p1 First predicate list (in CNF).
      @param p2 Second predicate list (in CNF).
      @return [Some (distinguishing, common)] if found, [None] otherwise. *)
  val find_distinguishing_predicate :
    expr list -> expr list -> (expr list * expr list) option

  (** [generate_relabelings ctx j1 j2 ppo1 ppo2 con1 con2] generates
      relabelings.

      Produces all valid symbol relabelings that could make [j1] and [j2]
      equivalent under their respective PPO relations.

      @param ctx The elaboration context.
      @param j1 First justification.
      @param j2 Second justification.
      @param ppo1 PPO relation for [j1].
      @param ppo2 PPO relation for [j2].
      @param con1 Forwarding context for [j1].
      @param con2 Forwarding context for [j2].
      @return Promise of set of candidate relabeling maps. *)
  val generate_relabelings :
    context ->
    justification ->
    justification ->
    (int * int) USet.t ->
    (int * int) USet.t ->
    ForwardingContext.t ->
    ForwardingContext.t ->
    (string, string) Hashtbl.t uset
end = struct
  let relabel expr pairs =
    USet.fold (fun acc (f, t) -> Expr.subst acc f (ESymbol t)) pairs expr

  (** [is_expr_relab_equiv elab_ctx relab p1 expr1 p2 expr2] checks expression
      equivalence.

      Tests if [expr1] and [expr2] are equivalent, possibly after applying the
      relabeling [relab] to [expr1].

      @param elab_ctx The elaboration context.
      @param relab Symbol relabeling map.
      @param p1 Predicate context for [expr1].
      @param expr1 First expression.
      @param p2 Predicate context for [expr2].
      @param expr2 Second expression.
      @return Promise of [true] if equivalent. *)
  let is_expr_relab_equiv elab_ctx relab p1 expr1 p2 expr2 =
    if Expr.equal expr1 expr2 then true
    else Expr.equal (Expr.relabel ~relab:(Hashtbl.find_opt relab) expr1) expr2
  (* TODO expand *)

  (** [is_relab_equiv elab_ctx relab p1 e1 p2 e2] checks event equivalence.

      Tests if events [e1] and [e2] are equivalent under relabeling, checking
      both their types and associated locations/values.

      @param elab_ctx The elaboration context.
      @param relab Symbol relabeling map.
      @param p1 Predicate context for [e1].
      @param e1 First event.
      @param p2 Predicate context for [e2].
      @param e2 Second event.
      @return Promise of [true] if equivalent. *)
  let is_relab_equiv elab_ctx relab p1 e1 p2 e2 =
    let is_trace = false in
      if is_trace then
        Logs_safe.debug (fun m ->
            m "Checking relab equivalence between %d and %d" e1.label e2.label
        );
      if e1.label = e2.label then true
      else if
        USet.mem elab_ctx.structure.fence_events e1.label
        && USet.mem elab_ctx.structure.fence_events e2.label
      then true
      else if
        USet.mem elab_ctx.structure.free_events e1.label
        && USet.mem elab_ctx.structure.free_events e2.label
      then (
        match (e1.loc, e2.loc) with
        | Some loc1, Some loc2 ->
            let loc_eq = is_expr_relab_equiv elab_ctx relab p1 loc1 p2 loc2 in
              if is_trace then
                Logs_safe.debug (fun m ->
                    m "Free events %d and %d location equivalence: %b" e1.label
                      e2.label loc_eq
                );
              loc_eq
        | None, None -> true
        | _ ->
            if is_trace then
              Logs_safe.debug (fun m ->
                  m "Free events %d and %d have mismatched locations." e1.label
                    e2.label
              );
            false
      )
      else if
        USet.mem elab_ctx.structure.read_events e1.label
        && USet.mem elab_ctx.structure.read_events e2.label
        || USet.mem elab_ctx.structure.write_events e1.label
           && USet.mem elab_ctx.structure.write_events e2.label
        || USet.mem elab_ctx.structure.malloc_events e1.label
           && USet.mem elab_ctx.structure.malloc_events e2.label
      then (
        match (e1.loc, e2.loc) with
        | Some loc1, Some loc2 -> (
            let loc_eq = is_expr_relab_equiv elab_ctx relab p1 loc1 p2 loc2 in
              if not loc_eq then (
                if is_trace then
                  Logs_safe.debug (fun m ->
                      m "Events %d and %d location equivalence: %b" e1.label
                        e2.label loc_eq
                  );
                false
              )
              else
                match (e1.rval, e2.rval) with
                | Some v1, Some v2 ->
                    let val_eq =
                      is_expr_relab_equiv elab_ctx relab p1 (Expr.of_value v1)
                        p2 (Expr.of_value v2)
                    in
                      if is_trace then
                        Logs_safe.debug (fun m ->
                            m "Events %d and %d value equivalence: %b" e1.label
                              e2.label val_eq
                        );
                      val_eq
                | None, None -> (
                    match (e1.wval, e2.wval) with
                    | Some v1, Some v2 ->
                        let val_eq =
                          is_expr_relab_equiv elab_ctx relab p1 v1 p2 v2
                        in
                          if is_trace then
                            Logs_safe.debug (fun m ->
                                m "Events %d and %d value equivalence: %b"
                                  e1.label e2.label val_eq
                            );
                          val_eq
                    | None, None -> true
                    | _ ->
                        if is_trace then
                          Logs_safe.debug (fun m ->
                              m "Events %d and %d have mismatched write values."
                                e1.label e2.label
                          );
                        false
                  )
                | _ ->
                    if is_trace then
                      Logs_safe.debug (fun m ->
                          m "Events %d and %d have mismatched values." e1.label
                            e2.label
                      );
                    false
          )
        | None, None -> true
        | _ ->
            if is_trace then
              Logs_safe.debug (fun m ->
                  m "Events %d and %d have mismatched locations." e1.label
                    e2.label
              );
            false
      )
      else (
        if is_trace then
          Logs_safe.debug (fun m ->
              m "Events %d and %d are of different types." e1.label e2.label
          );
        false
      )

  let is_closed_relab_equiv_landmark =
    Landmark.register "Elaborations.is_closed_relab_equiv"

  (** [is_closed_relab_equiv elab_ctx statex relab pred_1 pred_2 p1 e1 p2 e2]
      checks closed relabeling equivalence.

      Recursively checks if events [e1] and [e2] and all their predecessors are
      equivalent under the relabeling.

      @param elab_ctx The elaboration context.
      @param statex Static constraints.
      @param relab Symbol relabeling map.
      @param pred_1 Predecessor function for [e1]'s context.
      @param pred_2 Predecessor function for [e2]'s context.
      @param p1 Predicate context for [e1].
      @param e1 First event.
      @param p2 Predicate context for [e2].
      @param e2 Second event.
      @return Promise of [true] if closed equivalence holds. *)
  let is_closed_relab_equiv elab_ctx statex relab pred_1 pred_2 p1 e1 p2 e2 =
    let is_trace = false in
    let rec aux p1 e1 p2 e2 =
      if is_trace then
        Logs_safe.debug (fun m ->
            m "Checking closed relab equivalence between %d and %d" e1.label
              e2.label
        );
      if e1 = e2 then true
      else
        let ire = is_relab_equiv elab_ctx relab p1 e1 p2 e2 in
          if ire then (
            let pred_e1 = pred_1 e1.label in
            let pred_e2 = pred_2 e2.label in
              if is_trace then (
                Logs_safe.debug (fun m ->
                    m "Predecessors for %d: %s" e1.label
                      (USet.fold
                         (fun acc e' -> Printf.sprintf "%s,%d" acc e')
                         pred_e1 ""
                      )
                );
                Logs_safe.debug (fun m ->
                    m "Predecessors for %d: %s" e2.label
                      (USet.fold
                         (fun acc e' -> Printf.sprintf "%s,%d" acc e')
                         pred_e2 ""
                      )
                )
              );
              if USet.size pred_e1 = 0 then USet.size pred_e2 = 0
              else if USet.size pred_e2 = 0 then false
              else
                let pred_pairs = URelation.cross pred_e1 pred_e2 in
                  USet.for_all
                    (fun (l1, l2) ->
                      (* TODO looking up events by label misses effects of value
                         assignment elaboration *)
                      let e'1 = Hashtbl.find elab_ctx.structure.events l1 in
                      let e'2 = Hashtbl.find elab_ctx.structure.events l2 in
                        aux p1 e'1 p2 e'2
                    )
                    pred_pairs
          )
          else false
    in
      Landmark.enter is_closed_relab_equiv_landmark;
      let result = aux p1 e1 p2 e2 in
        Landmark.exit is_closed_relab_equiv_landmark;
        result

  let find_dist_preds_landmark =
    Landmark.register "Elaborations.find_distinguishing_predicate"

  let find_distinguishing_predicate preds_1 preds_2 =
    Landmark.enter find_dist_preds_landmark;
    let common_preds_1 =
      List.filter
        (fun expr_1 ->
          List.exists (fun expr_2 -> Expr.equal expr_1 expr_2) preds_2
        )
        preds_1
    in
    let common_preds_2 =
      List.filter
        (fun expr_2 ->
          List.exists (fun expr_1 -> Expr.equal expr_1 expr_2) preds_1
        )
        preds_2
    in
    let uncommon_preds_1 =
      List.filter
        (fun expr_1 ->
          not
            (List.exists (fun expr_2 -> Expr.equal expr_1 expr_2) common_preds_2)
        )
        preds_1
    in
    let uncommon_preds_2 =
      List.filter
        (fun expr_2 ->
          not
            (List.exists (fun expr_1 -> Expr.equal expr_1 expr_2) common_preds_1)
        )
        preds_2
    in
    let inverse_preds_1 =
      List.map Expr.inverse uncommon_preds_1
      |> Expr.evaluate_conjunction
      |> List.sort Expr.compare
    in
    let inverse_preds_2 =
      List.map Expr.inverse uncommon_preds_2
      |> Expr.evaluate_conjunction
      |> List.sort Expr.compare
    in
    let rec sorted_contains l1 l2 =
      match (l1, l2) with
      | _, [] -> true
      | [], _ -> false
      | h1 :: t1, h2 :: t2 ->
          let cmp = Expr.compare h1 h2 in
            if cmp = 0 then sorted_contains t1 t2 else sorted_contains t1 l2
    in
      if not (sorted_contains preds_2 inverse_preds_1) then (
        Landmark.exit find_dist_preds_landmark;
        None
      )
      else if not (sorted_contains preds_1 inverse_preds_2) then (
        Landmark.exit find_dist_preds_landmark;
        None
      )
      else
        let rec sorted_list_minus l1 l2 =
          match (l1, l2) with
          | [], _ -> []
          | _, [] -> l1
          | h1 :: t1, h2 :: t2 ->
              let cmp = Expr.compare h1 h2 in
                if cmp = 0 then sorted_list_minus t1 t2
                else h1 :: sorted_list_minus t1 l2
        in

        let distinguishing_predicate =
          uncommon_preds_1 @ inverse_preds_2 |> List.sort_uniq Expr.compare
        in
        let disjunction = common_preds_1 in
          Landmark.exit find_dist_preds_landmark;
          Some (distinguishing_predicate, disjunction)

  let gen_relabs_landmark =
    Landmark.register "Elaborations.generate_relabelings"

  let generate_relabelings elab_ctx (just_1 : justification)
      (just_2 : justification) ppo_1 ppo_2 con_1 con_2 =
    Landmark.enter gen_relabs_landmark;

    let remap_symbol ~con ~ppo (w : int) (s : string) =
      let origin = Eventstructures.origin elab_ctx.structure s |> Option.get in
      let remapped = ForwardingContext.remap con origin in
        (* symbols are not to be mapped over the write event *)
        if USet.mem ppo (w, remapped) then s
        else
          (* TODO use of get_val misses effects of value assignment elaboration
             *)
          match Events.get_val elab_ctx.structure remapped with
          | Some (ESymbol sym) when is_symbol sym -> sym
          | _ -> s
    in

    (* Extract symbols in just_1 and just_2 read in their respective
             branches, relative to the other justification via the conflict
             relation. Relabel equivalences are made from these. *)
    (* Note: this previously looked up events by id in the event structure,
       which gets the original write value, but misses the applied value
       assignment elaboration. *)
    let symbols_1 = Justification.get_symbols just_1 in
    let symbols_2 = Justification.get_symbols just_2 in
    let cs = USet.intersection symbols_1 symbols_2 in

    let symbols_1 =
      USet.filter
        (fun s ->
          USet.mem elab_ctx.structure.conflict
            (Hashtbl.find elab_ctx.structure.origin s, just_2.w.label)
        )
        symbols_1
      |> USet.map (remap_symbol ~con:con_1 ~ppo:ppo_1 just_1.w.label)
    in
    let symbols_2 =
      USet.filter
        (fun s ->
          USet.mem elab_ctx.structure.conflict
            (just_1.w.label, Hashtbl.find elab_ctx.structure.origin s)
        )
        symbols_2
      |> USet.map (remap_symbol ~con:con_2 ~ppo:ppo_2 just_2.w.label)
    in

    (* generate candidate relabeling equivalences *)
    let s1_cross_s2 = URelation.cross symbols_1 symbols_2 in
    let s1_cross_s2_map = URelation.adjacency_map s1_cross_s2 in
    (* ensures that combination is injective by construction *)
    let check_partial combo ?alternatives:_ (f, t) =
      List.for_all (fun (_, t') -> t <> t') combo
    in
    let relabs =
      USetMapCombinationBuilder.build_combinations ~check_partial
        s1_cross_s2_map (USet.values symbols_1) ()
    in
    let relabs =
      relabs
      (* transform to map *)
      |> USet.map (fun combo ->
          let relab = Hashtbl.create (USet.size combo) in
            USet.iter (fun (f, t) -> Hashtbl.replace relab f t) combo;
            relab
      )
      (* filter by condition on just.D : relabel(D_1)=D_2 *)
      |> USet.filter (fun relab ->
          USet.equal
            (USet.map
               (fun s ->
                 match Hashtbl.find_opt relab s with
                 | Some t -> t
                 | None -> s
               )
               just_1.d
            )
            just_2.d
      )
    in
      Landmark.exit gen_relabs_landmark;
      relabs

  let lift_elab_landmark = Landmark.register "Elaborations.LiftElab.elab"

  let elab elab_ctx just_1 just_2 =
    (* only consider justifications of writes in conflict and with non-trivial
       predicates *)
    Landmark.enter lift_elab_landmark;
    let is_trace = false in
      if
        (not
           (USet.mem elab_ctx.structure.conflict
              (just_1.w.label, just_2.w.label)
           )
        )
        || (List.length just_1.p = 0 && List.length just_2.p = 0)
      then (
        Landmark.exit lift_elab_landmark;
        []
      )
      else if not (URelation.is_function (USet.union just_1.we just_2.we)) then (
        Landmark.exit lift_elab_landmark;
        []
      )
      else if not (URelation.is_function (USet.union just_1.fwd just_2.fwd))
      then (
        Landmark.exit lift_elab_landmark;
        []
      )
      else (
        if is_trace then
          Logs_safe.debug (fun m ->
              m "LiftElab justifications:\n\t%s\n\t%s"
                (Justification.to_string just_1)
                (Justification.to_string just_2)
          );
        (* Static constraints from structure *)
        let statex = elab_ctx.structure.constraints in

        (* Create forwarding contexts *)
        let con_1 =
          ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:just_1.fwd
            ~we:just_1.we ()
        in
        let con_2 =
          ForwardingContext.create elab_ctx.fwd_es_ctx ~fwd:just_2.fwd
            ~we:just_2.we ()
        in

        (* Compute ppo for both justifications *)
        let ppo_1 = ForwardingContext.ppo con_1 just_1.p in
        let ppo_2 = ForwardingContext.ppo ~debug:true con_2 just_2.p in
          if is_trace then (
            Logs_safe.debug (fun m ->
                m "PPO in context 1: %s"
                  (USet.fold
                     (fun acc (e1, e2) -> Printf.sprintf "%s,(%d,%d)" acc e1 e2)
                     ppo_1 ""
                  )
            );
            Logs_safe.debug (fun m ->
                m "PPO in context 2: %s"
                  (USet.fold
                     (fun acc (e1, e2) -> Printf.sprintf "%s,(%d,%d)" acc e1 e2)
                     ppo_2 ""
                  )
            )
          );

          (* Get pred function *)
          let pred_1 = pred elab_ctx None None ~ppo:ppo_1 () in
          let pred_2 = pred elab_ctx None None ~ppo:ppo_2 () in

          (* Generate candidate relabelings for the pair of justifications *)
          let relabs =
            generate_relabelings elab_ctx just_1 just_2 ppo_1 ppo_2 con_1 con_2
          in
          let lifted =
            List.map
              (fun relab ->
                let inner_landmark =
                  Landmark.register "LiftElab.elab.process_relabeling"
                in
                  Landmark.enter inner_landmark;
                  let relabeled_just_1_p =
                    List.map
                      (Expr.relabel ~relab:(Hashtbl.find_opt relab))
                      just_1.p
                    |> Expr.evaluate_conjunction
                  in
                  let result =
                    match
                      find_distinguishing_predicate relabeled_just_1_p just_2.p
                    with
                    | None ->
                        if is_trace then
                          Logs_safe.debug (fun m ->
                              m
                                "Relabeling did not yield distinguishing \
                                 predicate.\n\
                                 \tRelabeled P1: [%s]\n\
                                 \tP2: [%s]"
                                (String.concat "; "
                                   (List.map Expr.to_string relabeled_just_1_p)
                                )
                                (String.concat "; "
                                   (List.map Expr.to_string just_2.p)
                                )
                          );
                        None
                    | Some (distinguishing_predicate, disjunction) ->
                        if
                          List.length disjunction = List.length just_2.p
                          && List.equal Expr.equal disjunction just_2.p
                        then (
                          if is_trace then
                            Logs_safe.debug (fun m ->
                                m
                                  "Relabeling did not yield distinguishing \
                                   predicate.\n\
                                   \tRelabeled P1: [%s]\n\
                                   \tP2: [%s]"
                                  (String.concat "; "
                                     (List.map Expr.to_string relabeled_just_1_p)
                                  )
                                  (String.concat "; "
                                     (List.map Expr.to_string just_2.p)
                                  )
                            );
                          None
                        )
                        else
                          let is_closed_relab_equiv_writes =
                            is_closed_relab_equiv elab_ctx statex relab pred_1
                              pred_2 just_1.p just_1.w just_2.p just_2.w
                          in
                            if not is_closed_relab_equiv_writes then (
                              if is_trace then
                                Logs_safe.debug (fun m ->
                                    m
                                      "Relabeling failed writes equivalence.\n\
                                       \tW1: %d\n\
                                       \tW2: %d"
                                      just_1.w.label just_2.w.label
                                );
                              None
                            )
                            else
                              let is_closed_relab_equiv_origins =
                                USet.for_all
                                  (fun s ->
                                    let o1 =
                                      Hashtbl.find elab_ctx.structure.origin s
                                    in
                                      match Hashtbl.find_opt relab s with
                                      | Some s' ->
                                          let o2 =
                                            Hashtbl.find
                                              elab_ctx.structure.origin s'
                                          in
                                          (* TODO looking up events by id
                                                   misses effect of value
                                                   assignment elaboration *)
                                          let e1 =
                                            Hashtbl.find
                                              elab_ctx.structure.events o1
                                          in
                                          let e2 =
                                            Hashtbl.find
                                              elab_ctx.structure.events o2
                                          in
                                            is_closed_relab_equiv elab_ctx
                                              statex relab pred_1 pred_2
                                              just_1.p e1 just_2.p e2
                                      | None -> true
                                  )
                                  just_1.d
                              in
                                if not is_closed_relab_equiv_origins then (
                                  if is_trace then
                                    Logs_safe.debug (fun m ->
                                        m
                                          "Relabeling failed origins \
                                           equivalence.\n\
                                           \tW1: %d\n\
                                           \tW2: %d"
                                          just_1.w.label just_2.w.label
                                    );
                                  None
                                )
                                else
                                  let new_p_d =
                                    List.map Expr.get_symbols disjunction
                                    |> List.flatten
                                    |> USet.of_list
                                  in
                                  let new_w_d =
                                    Option.map Expr.get_symbols just_2.w.wval
                                    |> Option.value ~default:[]
                                    |> USet.of_list
                                  in
                                  let d = USet.union new_p_d new_w_d in

                                  Some
                                    {
                                      p = disjunction;
                                      (* fwd and we need to be of just_2 as
                                         we're checking if delta is on path
                                         while generating executions *)
                                      fwd = USet.clone just_2.fwd;
                                      we = USet.clone just_2.we;
                                      d;
                                      w = just_2.w;
                                    }
                  in
                    Landmark.exit inner_landmark;
                    result
              )
              (USet.values relabs)
          in
          let lifted = List.filter_map Fun.id lifted in

          if is_trace then
            Logs_safe.debug (fun m ->
                m "Lifting produced %d justifications:\n%s" (List.length lifted)
                  (String.concat "\n"
                     (List.map
                        (fun j ->
                          Printf.sprintf "\t%s" (Justification.to_string j)
                        )
                        lifted
                     )
                  )
            );

          Landmark.exit lift_elab_landmark;
          lifted
      )
end

(** {1 WeakElab elaboration operations.} *)

module WeakElab = struct
  (** [elab elab_ctx just] performs weakening elaboration on a justification.
      Removes predicates from [just] that are implied by program-wide guarantees
      (PWG).

      @param elab_ctx The elaboration context.
      @param just The justification to weaken.
      @return Promise of list of weakened justifications. *)
  let elab elab_ctx just =
    (* Filter predicates that are not implied by PWG *)
    let p =
      List.filter
        (fun x ->
          (* NOTE previously PWGs were remapped through the forwarding
                 context. This remapping is inaccurate as forwarding acts on
                 events, rather than symbols etc. *)

          (* Create formula: And(remapped_pwg) ∧ Not(x) *)
          (* If SAT, then x is not implied by pwg, so keep it *)
          let not_x = Expr.inverse x in
          let defacto =
            Hashtbl.find_opt elab_ctx.structure.defacto just.w.label
            |> Option.value ~default:[]
          in
          (* defacto implies x *)
          let formula = not_x :: defacto in
          let solver = Solver.create formula in
            Solver.check solver |> Option.value ~default:true
        )
        just.p
    in

    if List.length just.p = List.length p then [] else [ { just with p } ]
end

(** {1 Chained elaboration operations.} *)

(** [batch_elaborations elab_ctx pre_justs] performs batch elaborations.

    Applies value assignment, forwarding, lifting, and weakening elaborations
    iteratively until a fixed point is reached.

    @param elab_ctx The elaboration context.
    @param pre_justs The initial set of justifications.
    @return Promise of justifications after batch elaborations. *)
let batch_elaborations elab_ctx pre_justs =
  let landmark = Landmark.register "Elaborations.batch_elaborations" in
    Landmark.enter landmark;

    let pool = Lwt_domain.setup_pool 10 in

    List.iter
      (fun just -> OpTrace.add elab_ctx.op_trace just PreJustification |> ignore)
      pre_justs;

    let rec fixed_point (justs : justification list)
        (new_justs : justification list) just_cache =
      Logs_safe.debug (fun m ->
          m "Batch elaborations iteration with %d justifications, %d new."
            (List.length justs) (List.length new_justs)
      );

      let old_justs = justs @ new_justs in

      let filter_justs new_justs justs =
        List.filter
          (fun just ->
            if
              (not (JustificationCache.mem just_cache just))
              && (not
                    (List.exists
                       (fun just' -> Justification.covers just' just)
                       (old_justs @ new_justs)
                    )
                 )
              && not
                   (List.exists
                      (fun just' ->
                        (not (just == just')) && Justification.covers just' just
                      )
                      justs
                   )
            then (
              JustificationCache.add just_cache just ();
              true
            )
            else false
          )
          justs
      in

      let add_elab_results_to_optrace optrace_fn =
        List.iter (fun (just, elaborated) ->
            List.iter
              (fun just' ->
                OpTrace.add elab_ctx.op_trace just' (optrace_fn just) |> ignore
              )
              elaborated
        )
      in

      let filter_elab_results new_justs results =
        List.map (fun (_, elaborated) -> elaborated) results
        |> List.flatten
        |> filter_justs new_justs
      in

      let run_elab elab_fn optrace_fn new_justs justs =
        let results =
          List.map (fun just -> (just, elab_fn elab_ctx just)) justs
        in
          add_elab_results_to_optrace optrace_fn results;
          filter_elab_results new_justs results |> Lwt.return
      in

      let run_elab_parallel elab_fn optrace_fn new_justs justs =
        (* memory barrier - settle context objects *)
        let _ = Atomic.make 0 |> Atomic.get in
        let promises =
          List.map
            (fun just ->
              Lwt_domain.detach pool
                (fun () ->
                  match elab_fn elab_ctx just with
                  | result -> (just, result)
                  | exception exn ->
                      let bt = Printexc.get_raw_backtrace () in
                        Printf.eprintf "Exception in domain for just: %s\n%s%!"
                          (Printexc.to_string exn)
                          (Printexc.raw_backtrace_to_string bt);
                        Printexc.raise_with_backtrace exn bt
                )
                ()
            )
            justs
        in
          let* results = Lwt.all promises in
            add_elab_results_to_optrace optrace_fn results;
            filter_elab_results new_justs results |> Lwt.return
      in

      let acc_justs = [] in
        let* new_va_justs =
          run_elab_parallel ValueAssignElab.elab
            (fun just -> ValueAssignElab just)
            acc_justs new_justs
        in
        let acc_justs = acc_justs @ new_va_justs in
          Logs_safe.debug (fun m ->
              m "Value assignment produced %d new justifications."
                (List.length new_va_justs)
          );

          let* new_fwd_justs =
            run_elab_parallel ForwardElab.elab
              (fun just -> Forwarding just)
              acc_justs new_justs
          in
          let acc_justs = acc_justs @ new_fwd_justs in
            Logs_safe.debug (fun m ->
                m "Forwarding produced %d new justifications."
                  (List.length new_fwd_justs)
            );

            let justs_to_lift =
              List.concat_map
                (fun just -> List.map (fun just' -> (just, just')) new_justs)
                new_justs
              @ List.concat_map
                  (fun just -> List.map (fun just' -> (just, just')) justs)
                  new_justs
              @ List.concat_map
                  (fun just -> List.map (fun just' -> (just, just')) new_justs)
                  justs
            in

            let* new_lift_justs =
              run_elab_parallel
                (fun elab_ctx (j1, j2) -> LiftElab.elab elab_ctx j1 j2)
                (fun (j1, j2) -> LiftElab (j1, j2))
                acc_justs justs_to_lift
            in
              Logs_safe.debug (fun m ->
                  m "Lifting produced %d new justifications."
                    (List.length new_lift_justs)
              );

              let* new_weaken_justs =
                run_elab_parallel WeakElab.elab
                  (fun just -> WeakElab just)
                  acc_justs new_justs
              in
              let acc_justs = acc_justs @ new_weaken_justs in
                Logs_safe.debug (fun m ->
                    m "Weakening produced %d new justifications."
                      (List.length new_weaken_justs)
                );

                let new_justs = acc_justs in
                  Logs_safe.debug (fun m ->
                      m "Total new justifications this iteration: %d"
                        (List.length new_justs)
                  );
                  Logs_safe.debug (fun m ->
                      m "After filtering covered justifications: %d"
                        (List.length new_justs)
                  );

                  if List.length new_justs = 0 then (
                    Logs_safe.debug (fun m ->
                        m
                          "Batch elaborations reached fixed point with %d \
                           justifications."
                          (List.length old_justs)
                    );
                    Lwt.return old_justs
                  )
                  else fixed_point old_justs new_justs just_cache
    in

    let just_cache = JustificationCache.create 1024 in
      let* final_justs = fixed_point [] pre_justs just_cache in
        let* just_str =
          Lwt_list.map_s
            (fun just ->
              let op_trace = OpTrace.find_opt elab_ctx.op_trace just in
              let s =
                Printf.sprintf "\t%s - %s"
                  (Justification.to_string just)
                  (Option.map op_to_string op_trace |> Option.value ~default:"")
              in
                Lwt.return s
            )
            final_justs
        in

        Logs_safe.debug (fun m ->
            m "Batch elaborations completed with %d justifications:\n%s"
              (List.length final_justs)
              (String.concat "\n" just_str)
        );

        Lwt_domain.teardown_pool pool;
        Landmark.exit landmark;
        Lwt.return final_justs

(** [generate_justifications structure init_ppo] generates justifications.

    Generates justifications for the given event structure, starting from
    initial PPO relations.

    @param structure The event structure.
    @param init_ppo Initial PPO relations.
    @return Promise of generated justifications. *)
let generate_justifications structure fwd_es_ctx init_ppo =
  let po = structure.po in
  let events = structure.events in

  (* Initialize justifications for writes *)
  let pre_justs = pre_justifications structure in

  Logs_safe.debug (fun m ->
      m "Pre-justifications for event\n\t%s"
        (String.concat "\n\t" (List.map Justification.to_string pre_justs))
  );

  let fj = USet.union structure.fj init_ppo in

  (* Build context for elaborations *)
  let op_trace = OpTrace.create 0 in
  let elab_ctx : context = { fwd_es_ctx; structure; fj; op_trace } in

  Logs_safe.debug (fun m -> m "Starting elaborations...");

  batch_elaborations elab_ctx pre_justs

(** [step_generate_justifications lwt_ctx] step to generate justifications.

    Retrieves the event structure from the context, initializes the forwarding
    context if necessary, and generates justifications.

    @param lwt_ctx The Lwt promise of the context.
    @return Promise of the context with generated justifications. *)
let step_generate_justifications (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t
    =
  let* ctx = lwt_ctx in
    match ctx.structure with
    | Some structure ->
        let* fwd_es_ctx =
          match ctx.fwd_es_ctx with
          | Some fwd_es_ctx -> Lwt.return fwd_es_ctx
          | None ->
              let fwd_es_ctx =
                Forwarding.EventStructureContext.create structure
              in
                ctx.fwd_es_ctx <- Some fwd_es_ctx;
                let* () = Forwarding.EventStructureContext.init fwd_es_ctx in
                  Lwt.return fwd_es_ctx
        in
        let init_ppo = Eventstructures.init_ppo structure in
          let* final_justs =
            generate_justifications structure fwd_es_ctx init_ppo
          in
            Logs_safe.debug (fun m ->
                m "Generated %d justifications." (List.length final_justs)
            );
            ctx.justifications <- Some final_justs;
            Lwt.return ctx
    | None ->
        Logs_safe.err (fun m -> m "No event structure found in context.");
        Lwt.return ctx
