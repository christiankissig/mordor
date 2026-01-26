(** Elaboration algorithms for symbolic event structures.

    This module implements the core elaboration algorithms that transform and
    refine justifications in symbolic event structures. The elaborations include
    value assignment, forwarding, lifting, and weakening operations that
    progressively build up execution models. *)

open Algorithms
open Expr
open Forwardingcontext
open Lwt.Syntax
open Types
open Uset
open Justifications

(** {1 Foundational Types} *)

(** Elaboration context containing the symbolic event structure and caches.

    Bundles together all the state needed during elaboration including the event
    structure, fork-join edges, and various caches. *)
type context = {
  structure : symbolic_event_structure;
      (** The symbolic event structure being elaborated. *)
  fj : (int * int) USet.t;  (** Fork-join edges that constrain forwarding. *)
  (* Caches to track seen justifications for elaborations *)
  value_assign_seen : unit JustificationCache.t;
  lifted_seen : unit JustificationPairCache.t;
  forwarding_seen : unit JustificationCache.t;
  weaken_seen : unit JustificationCache.t;
  filter_seen : unit JustificationPairCache.t;
}

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
  let landmark = Landmark.register "Elaborations.pred" in
    Landmark.enter landmark;
    let* ppo_result =
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
      Landmark.exit landmark;
      Lwt.return (fun e ->
          Hashtbl.find_opt tree e |> Option.value ~default:(USet.create ())
      )

(** [close_under_elab justs elab] closes justification set under elaboration.

    Applies the elaboration function [elab] to each justification in [justs] in
    parallel, collecting and deduplicating results.

    @param justs The set of justifications to elaborate.
    @param elab
      Function mapping a justification to a list of elaborated justifications.
    @return Promise of the union of original and new justifications. *)
let close_under_elab ?cache justs elab =
  let* elaborated =
    USet.async_map
      (fun just ->
        if
          Option.is_some cache && JustificationCache.mem (Option.get cache) just
        then Lwt.return []
        else (
          Option.iter (fun cache -> JustificationCache.add cache just ()) cache;
          elab just
        )
      )
      justs
  in
  let new_justs = USet.values elaborated |> List.flatten in
    Logs.debug (fun m ->
        m "Elaboration produced %d justifications before filtering.\n%s\n"
          (List.length new_justs)
          (String.concat "\n\t" (List.map Justification.to_string new_justs))
    );
    let new_justs =
      new_justs
      |> deduplicate_justification_list
      |> List.filter (fun just ->
          not (USet.exists (fun j -> Justification.equal j just) justs)
      )
      |> USet.of_list
    in
      Logs.debug (fun m ->
          m "Elaboration produced %d new justifications.\n%s"
            (USet.size new_justs)
            (String.concat "\n\t"
               (List.map Justification.to_string (USet.values new_justs))
            )
      );
      Lwt.return (USet.union justs new_justs)

(** [close_under_elab_2 justs elab] closes under binary elaboration.

    Similar to {!close_under_elab} but for elaborations that take pairs of
    justifications. Applies [elab] to all pairs in the cross product.

    @param justs The set of justifications to elaborate.
    @param elab Function mapping two justifications to a list of results.
    @return Promise of the union of original and new justifications. *)
let close_under_elab_2 ?cache justs elab =
  let pairs = URelation.cross justs justs in
  let landmark = Landmark.register "Elaborations.close_under_elab_2.filter" in
    Landmark.enter landmark;
    let filtered_pairs =
      match cache with
      | None -> pairs
      | Some c ->
          USet.filter
            (fun (j1, j2) -> not (JustificationPairCache.mem c (j1, j2)))
            pairs
    in
      Landmark.exit landmark;
      let landmark = Landmark.register "Elaborations.close_under_elab_2.elab" in
        Landmark.enter landmark;
        let* elaborated =
          USet.async_map
            (fun (j1, j2) ->
              Option.iter
                (fun c -> JustificationPairCache.add c (j1, j2) ())
                cache;
              elab j1 j2
            )
            filtered_pairs
        in
          Landmark.exit landmark;
          let new_justs = USet.values elaborated |> List.flatten in
            Logs.debug (fun m ->
                m
                  "Elaboration produced %d justifications before filtering.\n\
                   %s\n"
                  (List.length new_justs)
                  (String.concat "\n\t"
                     (List.map Justification.to_string new_justs)
                  )
            );
            let new_justs =
              new_justs
              |> deduplicate_justification_list
              |> List.filter (fun just ->
                  not (USet.exists (fun j -> Justification.equal j just) justs)
              )
              |> USet.of_list
            in
              Logs.debug (fun m ->
                  m "Elaboration produced %d new justifications.\n%s"
                    (USet.size new_justs)
                    (String.concat "\n\t"
                       (List.map Justification.to_string (USet.values new_justs))
                    )
              );
              Lwt.return (USet.union justs new_justs)

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
    USet.union write_events alloc_events |> USet.union free_events
  in
    USet.map
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

(** [filter elab_ctx justs] filters and deduplicates justifications.

    Removes duplicate justifications and those covered by others. A
    justification [j1] covers [j2] if [j1] is more general (has fewer
    constraints).

    @param elab_ctx The elaboration context.
    @param justs The set of justifications to filter.
    @return Promise of the filtered justification set. *)
let filter elab_ctx (justs : justification uset) =
  let landmark = Landmark.register "Elaborations.filter" in
    Landmark.enter landmark;
    Logs.debug (fun m ->
        m "Filtering %d justifications...\n%s" (USet.size justs)
          (String.concat "\n\t"
             (List.map Justification.to_string (USet.values justs))
          )
    );

    let deduplicated = deduplicate_justification_list (USet.values justs) in

    (* Sort by predicate length; needed to half filtering by covered
     justifications below. *)
    let sorted =
      List.sort (fun a b -> List.length a.p - List.length b.p) deduplicated
    in

    (* Compute ppo for each justification once *)
    (* TODO make hashtable on write event *)
    let justs_with_ppo = Hashtbl.create (List.length sorted) in

    let* () =
      Lwt_list.iter_s
        (fun just ->
          let con = ForwardingContext.create ~fwd:just.fwd ~we:just.we () in
            let* ppo = ForwardingContext.ppo con just.p in
            let existing =
              Hashtbl.find_opt justs_with_ppo just.w.label
              |> Option.value ~default:[]
            in
              Hashtbl.replace justs_with_ppo just.w.label
                ((just, ppo) :: existing);
              Lwt.return_unit
        )
        sorted
    in

    let writes_with_justs =
      Hashtbl.fold (fun k _ acc -> k :: acc) justs_with_ppo []
    in

    let* filtered =
      Lwt_list.fold_left_s
        (fun (acc : justification list) (w : int) ->
          (* Filter covered justifications *)
          let justs_with_ppo = Hashtbl.find justs_with_ppo w in
          let indexed = List.mapi (fun i jp -> (i, jp)) justs_with_ppo in
            let* (filtered : justification list) =
              Lwt_list.filter_map_s
                (fun (i, (just_x, ppo_x)) ->
                  (* Check if any earlier justification covers this one *)
                  let is_covered =
                    List.exists
                      (fun (j, (just_y, ppo_y)) ->
                        j < i
                        (* Only compare with earlier justifications, makes use of
                        sorting by predicate length earlier *)
                        && Justification.covers just_y ppo_y just_x ppo_x
                      )
                      indexed
                  in
                    if is_covered then Lwt.return_none
                    else Lwt.return_some just_x
                )
                indexed
            in
              Lwt.return (acc @ filtered)
        )
        [] writes_with_justs
    in

    let result = USet.of_list filtered in
      Logs.debug (fun m ->
          m "Filtered down to %d justifications.\n%s" (USet.size result)
            (String.concat "\n\t"
               (List.map Justification.to_string (USet.values result))
            )
      );
      Landmark.exit landmark;
      Lwt.return result

(** {1 Value Assignment Elaboration} *)

module ValueAssignment = struct
  (** [elab elab_ctx just] performs value assignment elaboration.

      For the given justification, attempts to find a satisfying model and
      assigns concrete values to symbolic write values where possible.

      @param elab_ctx The elaboration context.
      @param just The justification to elaborate.
      @return Promise of justifications with assigned values. *)
  let elab elab_ctx just =
    let fwd_ctx = ForwardingContext.create ~fwd:just.fwd ~we:just.we () in
    let solver = Solver.create (just.p @ fwd_ctx.psi) in
      let* model = Solver.solve solver in
        match model with
        | Some bindings ->
            let new_wval =
              match just.w.wval with
              | Some (ESymbol s) -> (
                  match Solver.concrete_value bindings s with
                  | Some value -> Some (Expr.of_value value)
                  | None -> just.w.wval
                )
              | Some (EVar v) -> (
                  match Solver.concrete_value bindings v with
                  | Some value -> Some (Expr.of_value value)
                  | None -> just.w.wval
                )
              | _ -> just.w.wval
            in
            (* TODO this is shady and should instead track symbols
                 symbols through the value assignment. However, this does agree
                 with the paper. *)
            let new_p_d =
              List.map Expr.get_symbols just.p |> List.flatten |> USet.of_list
            in
            let new_w_d =
              Option.map Expr.get_symbols new_wval
              |> Option.value ~default:[]
              |> USet.of_list
            in
            let d = USet.union new_p_d new_w_d in
            let w = { just.w with wval = new_wval } in
              Lwt.return [ { just with w; d } ]
        | None -> Lwt.return [ just ]
end

(** [value_assign elab_ctx justs] performs value assignment elaboration.

    For each justification, attempts to find a satisfying model and assigns
    concrete values to symbolic write values where possible.

    @param elab_ctx The elaboration context.
    @param justs The set of justifications to elaborate.
    @return Promise of justifications with assigned values. *)
let value_assign elab_ctx justs =
  let landmark = Landmark.register "Elaborations.value_assign" in
    Landmark.enter landmark;
    Logs.debug (fun m ->
        m "Performing value assignment on %d justifications..." (USet.size justs)
    );

    let* results =
      close_under_elab ~cache:elab_ctx.value_assign_seen justs
        (ValueAssignment.elab elab_ctx)
    in

    Logs.debug (fun m ->
        m "Completed value assignment on %d justifications." (USet.size results)
    );
    Landmark.exit landmark;
    Lwt.return results

(** {1 Forwarding Elaboration} *)

module Forwarding = struct
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
        | _ -> Lwt.return false
    else Lwt.return false

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
      USet.async_filter
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
      USet.async_filter
        (fun (e1, e2) -> fprime elab_ctx pred_fn ppo_loc just e1 e2)
        w_cross_w

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
    let ps =
      if elab_ctx.structure.pwg <> [] then
        [ just.p; just.p @ elab_ctx.structure.pwg ]
      else [ just.p ]
    in
      (* Map over each path *)
      let* path_results =
        Lwt_list.map_p
          (fun p ->
            let fwd_ctx =
              ForwardingContext.create ~fwd:just.fwd ~we:just.we ()
            in
              let* ppo = ForwardingContext.ppo fwd_ctx p in
                let* ppo_loc = ForwardingContext.ppo_loc fwd_ctx p in
                  let* _pred =
                    pred elab_ctx None None ~ppo:(Lwt.return ppo) ()
                  in

                  (* Subtract fj from ppo_loc. TODO marked as DIFFERS in JS:
                     symmrd.ml defines fj as the union of init_ppo (ordering
                     the initial event before any other event and the
                     fork-join edges from the symbolic event structure.
                     Critically, these edges should not be part of forwarding.
                  *)
                  let _ppo_loc = USet.set_minus ppo_loc elab_ctx.fj in

                  (* Compute fwd and we edges *)
                  let* _fwd = fwd elab_ctx _pred fwd_ctx _ppo_loc just in
                    let* _we = we elab_ctx _pred fwd_ctx _ppo_loc just in

                    let _fwd =
                      USet.filter
                        (fun (e1, e2) ->
                          e1 > 0
                          (* && e2 <> just.w.label *)
                          (* TODO disagrees with paper,
                        freeze definition *)
                          (* e1 and e2 are po before w, pulled forward from freeze
                           *)
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
                          e1 > 0
                          (* && e2 <> just.w.label *)
                          (* NOTE disagrees with paper, freeze definition *)
                          (* e1 and e2 are po before w, pulled forward from freeze
                           *)
                          && USet.mem elab_ctx.structure.po (e1, just.w.label)
                          && (e2 == just.w.label
                             || USet.mem elab_ctx.structure.po (e2, just.w.label)
                             )
                        )
                        _we
                    in

                    (* Filter edge function *)
                    let filtedge (edge, new_fwd, new_we) =
                      if Forwardingcontext.is_bad new_fwd new_we then
                        Lwt.return_false
                      else if Forwardingcontext.is_good new_fwd new_we then
                        Lwt.return_true
                      else
                        let con =
                          ForwardingContext.create ~fwd:new_fwd ~we:new_we ()
                        in
                          ForwardingContext.check con
                    in

                    (* Create fwd edges with contexts *)
                    let fwdedges =
                      USet.values _fwd
                      |> List.map (fun edge ->
                          ( edge,
                            USet.union just.fwd (USet.singleton edge),
                            just.we
                          )
                      )
                    in

                    (* Create we edges with contexts *)
                    let weedges =
                      USet.values _we
                      |> List.map (fun edge ->
                          ( edge,
                            just.fwd,
                            USet.union just.we (USet.singleton edge)
                          )
                      )
                    in

                    (* Filter both edge types *)
                    let* filtered_fwd = Lwt_list.filter_p filtedge fwdedges in
                      let* filtered_we = Lwt_list.filter_p filtedge weedges in

                      (* Remap justifications *)
                      let fwd_justs =
                        List.map
                          (fun (edge, new_fwd, new_we) ->
                            let con =
                              ForwardingContext.create ~fwd:new_fwd ~we:new_we
                                ()
                            in
                              ForwardingContext.remap_just con just
                          )
                          filtered_fwd
                      in

                      let we_justs =
                        List.map
                          (fun (edge, new_fwd, new_we) ->
                            let con =
                              ForwardingContext.create ~fwd:new_fwd ~we:new_we
                                ()
                            in
                              ForwardingContext.remap_just con just
                          )
                          filtered_we
                      in

                      Lwt.return (fwd_justs @ we_justs)
          )
          ps
      in
      let results = List.concat path_results in
        Lwt.return results
end

(** [forward elab_ctx justs] performs forwarding elaboration.

    Extends justifications by adding valid forwarding and write-exclusion edges.
    Each new edge is validated for consistency before being added.

    @param elab_ctx The elaboration context.
    @param justs The set of justifications to forward.
    @return Promise of justifications with added forwarding edges. *)
let forward elab_ctx justs =
  let landmark = Landmark.register "Elaborations.forward" in
    Landmark.enter landmark;
    Logs.debug (fun m ->
        m "Performing forwarding on %d justifications..." (USet.size justs)
    );

    let* out =
      close_under_elab ~cache:elab_ctx.forwarding_seen justs
        (Forwarding.elab elab_ctx)
    in

    Landmark.exit landmark;
    Lwt.return out

(** {1 Lifting Elaboration} *)

(** Lifting elaboration operations.

    Implements the lifting elaboration that combines pairs of justifications for
    conflicting writes by finding relabelings that make their paths equivalent.
*)
module Lifting : sig
  (** [elab ctx j1 j2] attempts to lift justifications [j1] and [j2].

      For conflicting writes, finds relabelings that make the justifications
      equivalent and produces new lifted justifications.

      @param ctx The elaboration context.
      @param j1 First justification.
      @param j2 Second justification.
      @return Promise of list of lifted justifications. *)
  val elab :
    context -> justification -> justification -> justification list Lwt.t

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
    (string, string) Hashtbl.t uset Lwt.t
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
    if Expr.equal expr1 expr2 then Lwt.return_true
    else if
      Expr.equal (Expr.relabel ~relab:(Hashtbl.find_opt relab) expr1) expr2
    then Lwt.return_true
    (* TODO expand *)
      else Lwt.return_false

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
    let is_trace =
      (e1.label = 5 && e2.label = 7) || (e1.label = 7 && e2.label = 5)
    in
      if is_trace then
        Logs.debug (fun m ->
            m "Checking relab equivalence between %d and %d" e1.label e2.label
        );
      if e1.label = e2.label then Lwt.return_true
      else if
        USet.mem elab_ctx.structure.fence_events e1.label
        && USet.mem elab_ctx.structure.fence_events e2.label
      then Lwt.return_true
      else if
        USet.mem elab_ctx.structure.free_events e1.label
        && USet.mem elab_ctx.structure.free_events e2.label
      then (
        match (e1.loc, e2.loc) with
        | Some loc1, Some loc2 ->
            let* loc_eq = is_expr_relab_equiv elab_ctx relab p1 loc1 p2 loc2 in
              if is_trace then
                Logs.debug (fun m ->
                    m "Free events %d and %d location equivalence: %b" e1.label
                      e2.label loc_eq
                );
              Lwt.return loc_eq
        | None, None -> Lwt.return_true
        | _ ->
            if is_trace then
              Logs.debug (fun m ->
                  m "Free events %d and %d have mismatched locations." e1.label
                    e2.label
              );
            Lwt.return_false
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
            let* loc_eq = is_expr_relab_equiv elab_ctx relab p1 loc1 p2 loc2 in
              if not loc_eq then (
                if is_trace then
                  Logs.debug (fun m ->
                      m "Events %d and %d location equivalence: %b" e1.label
                        e2.label loc_eq
                  );
                Lwt.return_false
              )
              else
                match (e1.rval, e2.rval) with
                | Some v1, Some v2 ->
                    let* val_eq =
                      is_expr_relab_equiv elab_ctx relab p1 (Expr.of_value v1)
                        p2 (Expr.of_value v2)
                    in
                      if is_trace then
                        Logs.debug (fun m ->
                            m "Events %d and %d value equivalence: %b" e1.label
                              e2.label val_eq
                        );
                      Lwt.return val_eq
                | None, None -> (
                    match (e1.wval, e2.wval) with
                    | Some v1, Some v2 ->
                        let* val_eq =
                          is_expr_relab_equiv elab_ctx relab p1 v1 p2 v2
                        in
                          if is_trace then
                            Logs.debug (fun m ->
                                m "Events %d and %d value equivalence: %b"
                                  e1.label e2.label val_eq
                            );
                          Lwt.return val_eq
                    | None, None -> Lwt.return_true
                    | _ ->
                        if is_trace then
                          Logs.debug (fun m ->
                              m "Events %d and %d have mismatched write values."
                                e1.label e2.label
                          );
                        Lwt.return_false
                  )
                | _ ->
                    if is_trace then
                      Logs.debug (fun m ->
                          m "Events %d and %d have mismatched values." e1.label
                            e2.label
                      );
                    Lwt.return_false
          )
        | None, None -> Lwt.return_true
        | _ ->
            if is_trace then
              Logs.debug (fun m ->
                  m "Events %d and %d have mismatched locations." e1.label
                    e2.label
              );
            Lwt.return_false
      )
      else (
        if is_trace then
          Logs.debug (fun m ->
              m "Events %d and %d are of different types." e1.label e2.label
          );
        Lwt.return_false
      )

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
    let is_trace =
      (e1.label = 5 && e2.label = 7) || (e1.label = 7 && e2.label = 5)
    in
    let rec aux p1 e1 p2 e2 =
      if is_trace then
        Logs.debug (fun m ->
            m "Checking closed relab equivalence between %d and %d" e1.label
              e2.label
        );
      if e1 = e2 then Lwt.return_true
      else
        let* ire = is_relab_equiv elab_ctx relab p1 e1 p2 e2 in
          if ire then (
            let pred_e1 = pred_1 e1.label in
            let pred_e2 = pred_2 e2.label in
              if is_trace then (
                Logs.debug (fun m ->
                    m "Predecessors for %d: %s" e1.label
                      (USet.fold
                         (fun acc e' -> Printf.sprintf "%s,%d" acc e')
                         pred_e1 ""
                      )
                );
                Logs.debug (fun m ->
                    m "Predecessors for %d: %s" e2.label
                      (USet.fold
                         (fun acc e' -> Printf.sprintf "%s,%d" acc e')
                         pred_e2 ""
                      )
                )
              );
              if USet.size pred_e1 = 0 then Lwt.return (USet.size pred_e2 = 0)
              else if USet.size pred_e2 = 0 then Lwt.return_false
              else
                let pred_pairs = URelation.cross pred_e1 pred_e2 in
                  USet.async_for_all
                    (fun (l1, l2) ->
                      (* TODO looking up events by label misses effects of value
                         assignment elaboration *)
                      let e'1 = Hashtbl.find elab_ctx.structure.events l1 in
                      let e'2 = Hashtbl.find elab_ctx.structure.events l2 in
                        aux p1 e'1 p2 e'2
                    )
                    pred_pairs
          )
          else Lwt.return_false
    in
    let landmark = Landmark.register "Elaborations.is_closed_relab_equiv" in
      Landmark.enter landmark;
      let* res = aux p1 e1 p2 e2 in
        Landmark.exit landmark;
        Lwt.return res

  let find_distinguishing_predicate preds_1 preds_2 =
    let landmark =
      Landmark.register "Elaborations.find_distinguishing_predicate"
    in
      Landmark.enter landmark;
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
              (List.exists
                 (fun expr_2 -> Expr.equal expr_1 expr_2)
                 common_preds_2
              )
          )
          preds_1
      in
      let uncommon_preds_2 =
        List.filter
          (fun expr_2 ->
            not
              (List.exists
                 (fun expr_1 -> Expr.equal expr_1 expr_2)
                 common_preds_1
              )
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
          Landmark.exit landmark;
          None
        )
        else if not (sorted_contains preds_1 inverse_preds_2) then (
          Landmark.exit landmark;
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
            Landmark.exit landmark;
            Some (distinguishing_predicate, disjunction)

  let generate_relabelings elab_ctx (just_1 : justification)
      (just_2 : justification) ppo_1 ppo_2 con_1 con_2 =
    let landmark = Landmark.register "Elaborations.generate_relabelings" in
      Landmark.enter landmark;

      let remap_symbol ~con ~ppo (w : int) (s : string) =
        let origin =
          Eventstructures.origin elab_ctx.structure s |> Option.get
        in
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
        Lwt.return (List.for_all (fun (_, t') -> t <> t') combo)
      in
        let* relabs =
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
          Landmark.exit landmark;
          Lwt.return relabs

  let elab elab_ctx just_1 just_2 =
    (* only consider justifications of writes in conflict and with non-trivial
       predicates *)
    let landmark = Landmark.register "Elaborations.Lifting.elab" in
      Landmark.enter landmark;
      let is_trace =
        (just_1.w.label = 5 && just_2.w.label = 7)
        || (just_1.w.label = 6 && just_2.w.label = 5)
      in
        if
          (not
             (USet.mem elab_ctx.structure.conflict
                (just_1.w.label, just_2.w.label)
             )
          )
          || (List.length just_1.p = 0 && List.length just_2.p = 0)
        then (
          Landmark.exit landmark;
          Lwt.return []
        )
        else if not (URelation.is_function (USet.union just_1.we just_2.we))
        then (
          Landmark.exit landmark;
          Lwt.return []
        )
        else if not (URelation.is_function (USet.union just_1.fwd just_2.fwd))
        then (
          Landmark.exit landmark;
          Lwt.return []
        )
        else (
          if is_trace then
            Logs.debug (fun m ->
                m "Lifting justifications:\n\t%s\n\t%s"
                  (Justification.to_string just_1)
                  (Justification.to_string just_2)
            );
          (* Static constraints from structure *)
          let statex = elab_ctx.structure.constraints in

          (* Create forwarding contexts *)
          let con_1 =
            ForwardingContext.create ~fwd:just_1.fwd ~we:just_1.we ()
          in
          let con_2 =
            ForwardingContext.create ~fwd:just_2.fwd ~we:just_2.we ()
          in

          (* Compute ppo for both justifications *)
          let* ppo_1 = ForwardingContext.ppo con_1 just_1.p in
            let* ppo_2 = ForwardingContext.ppo ~debug:true con_2 just_2.p in
              if is_trace then (
                Logs.debug (fun m ->
                    m "PPO in context 1: %s"
                      (USet.fold
                         (fun acc (e1, e2) ->
                           Printf.sprintf "%s,(%d,%d)" acc e1 e2
                         )
                         ppo_1 ""
                      )
                );
                Logs.debug (fun m ->
                    m "PPO in context 2: %s"
                      (USet.fold
                         (fun acc (e1, e2) ->
                           Printf.sprintf "%s,(%d,%d)" acc e1 e2
                         )
                         ppo_2 ""
                      )
                )
              );

              (* Get pred function *)
              let* pred_1 =
                pred elab_ctx None None ~ppo:(Lwt.return ppo_1) ()
              in
                let* pred_2 =
                  pred elab_ctx None None ~ppo:(Lwt.return ppo_2) ()
                in

                (* Generate candidate relabelings for the pair of justifications *)
                let* relabs =
                  generate_relabelings elab_ctx just_1 just_2 ppo_1 ppo_2 con_1
                    con_2
                in
                  Logs.debug (fun m ->
                      m "Generated %d relabelings for justifications %d vs %d"
                        (USet.size relabs) just_1.w.label just_2.w.label
                  );
                  let* lifted =
                    Lwt_list.map_s
                      (fun relab ->
                        let inner_landmark =
                          Landmark.register "Lifting.elab.process_relabeling"
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
                              find_distinguishing_predicate relabeled_just_1_p
                                just_2.p
                            with
                            | None ->
                                if is_trace then
                                  Logs.debug (fun m ->
                                      m
                                        "Relabeling did not yield \
                                         distinguishing predicate.\n\
                                         \tRelabeled P1: [%s]\n\
                                         \tP2: [%s]"
                                        (String.concat "; "
                                           (List.map Expr.to_string
                                              relabeled_just_1_p
                                           )
                                        )
                                        (String.concat "; "
                                           (List.map Expr.to_string just_2.p)
                                        )
                                  );
                                Lwt.return None
                            | Some (distinguishing_predicate, disjunction) ->
                                let* is_closed_relab_equiv_writes =
                                  is_closed_relab_equiv elab_ctx statex relab
                                    pred_1 pred_2 just_1.p just_1.w just_2.p
                                    just_2.w
                                in
                                  if not is_closed_relab_equiv_writes then (
                                    if is_trace then
                                      Logs.debug (fun m ->
                                          m
                                            "Relabeling failed writes \
                                             equivalence.\n\
                                             \tW1: %d\n\
                                             \tW2: %d"
                                            just_1.w.label just_2.w.label
                                      );
                                    Lwt.return None
                                  )
                                  else
                                    let* is_closed_relab_equiv_origins =
                                      USet.async_for_all
                                        (fun s ->
                                          let o1 =
                                            Hashtbl.find
                                              elab_ctx.structure.origin s
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
                                            | None -> Lwt.return true
                                        )
                                        just_1.d
                                    in
                                      if not is_closed_relab_equiv_origins then (
                                        if is_trace then
                                          Logs.debug (fun m ->
                                              m
                                                "Relabeling failed origins \
                                                 equivalence.\n\
                                                 \tW1: %d\n\
                                                 \tW2: %d"
                                                just_1.w.label just_2.w.label
                                          );
                                        Lwt.return None
                                      )
                                      else
                                        Lwt.return_some
                                          {
                                            p = disjunction;
                                            (* fwd and we need to be of just_2 as
                                         we're checking if delta is on path
                                         while generating executions *)
                                            fwd = just_2.fwd;
                                            we = just_2.we;
                                            d = just_2.d;
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
                    Logs.debug (fun m ->
                        m "Lifting produced %d justifications:\n%s"
                          (List.length lifted)
                          (String.concat "\n"
                             (List.map
                                (fun j ->
                                  Printf.sprintf "\t%s"
                                    (Justification.to_string j)
                                )
                                lifted
                             )
                          )
                    );

                  Landmark.exit landmark;
                  Lwt.return lifted
        )
end

(** [lift elab_ctx justs] performs lifting elaboration on all pairs.

    Applies the lifting elaboration to all pairs of justifications in the cross
    product, combining justifications for conflicting writes.

    @param elab_ctx The elaboration context.
    @param justs The set of justifications to lift.
    @return Promise of justifications including lifted results. *)
let lift elab_ctx justs =
  let landmark = Landmark.register "Elaborations.lift" in
    Landmark.enter landmark;
    Logs.debug (fun m -> m "Lifting %d justifications..." (USet.size justs));

    let* out =
      close_under_elab_2 ~cache:elab_ctx.lifted_seen justs
        (Lifting.elab elab_ctx)
    in
      Logs.debug (fun m ->
          m "Lifting produced %d justifications." (USet.size out)
      );
      Landmark.exit landmark;
      Lwt.return out

(** {1 Weakening elaboration operations.} *)

module Weakening = struct
  (** [elab elab_ctx just] performs weakening elaboration on a justification.
      Removes predicates from [just] that are implied by program-wide guarantees
      (PWG).

      @param elab_ctx The elaboration context.
      @param just The justification to weaken.
      @return Promise of list of weakened justifications. *)
  let elab elab_ctx just =
    let con = ForwardingContext.create ~fwd:just.fwd ~we:just.we () in

    (* Filter predicates that are not implied by PWG *)
    let* filtered_p =
      Lwt_list.filter_p
        (fun x ->
          (* NOTE previously PWGs were remapped through the forwarding
                 context. This remapping is inaccurate as forwarding acts on
                 events, rather than symbols etc. *)

          (* Create formula: And(remapped_pwg) ∧ Not(x) *)
          (* If SAT, then x is not implied by pwg, so keep it *)
          let not_x = Expr.inverse x in
          let formula = not_x :: elab_ctx.structure.pwg in
          let solver = Solver.create formula in
            let* result = Solver.check solver in
              match result with
              | Some true ->
                  Lwt.return_true (* SAT: x not implied by pwg, keep it *)
              | Some false ->
                  Lwt.return_false (* UNSAT: x implied by pwg, remove it *)
              | None -> Lwt.return_true
          (* Unknown: keep predicate to be safe *)
        )
        just.p
    in

    Lwt.return [ { just with p = filtered_p } ]
end

(** [weaken elab_ctx justs] performs weakening elaboration.

    Removes predicates from justifications that are implied by program-wide
    guarantees (PWG), producing more general justifications.

    @param elab_ctx The elaboration context.
    @param justs The set of justifications to weaken.
    @return Promise of weakened justifications. *)
let weaken elab_ctx (justs : justification uset) : justification uset Lwt.t =
  Logs.debug (fun m -> m "Starting weakening on justifications...");
  if elab_ctx.structure.pwg = [] then (
    Logs.debug (fun m -> m "No PWG predicates; skipping weakening.");
    Lwt.return justs
  )
  else
    let landmark = Landmark.register "Elaborations.weaken" in
      Landmark.enter landmark;

      (* TODO replace justifications instead of accumulating new ones *)
      let* out =
        close_under_elab ~cache:elab_ctx.weaken_seen justs
          (Weakening.elab elab_ctx)
      in
        Landmark.exit landmark;
        Lwt.return out

(** {1 Chained elaboration operations.} *)

(** [chain_elaborations elab_ctx pre_justs] performs chained elaborations.
    Applies a sequence of elaboration operations (value assignment, lifting,
    weakening, forwarding, and filtering) in a fixed-point manner until no new
    justifications are produced. Each step closes the set of justifications
    under the respective elaboration operation. A justification cache is used to
    deduplicate the application of elaborations across iterations.

    @param elab_ctx The elaboration context.
    @param pre_justs The initial set of justifications to elaborate.
    @return Promise of the final set of elaborated justifications. *)
let chain_elaborations elab_ctx pre_justs =
  Logs.debug (fun m -> m "Starting elaborations...");

  let justification_set_equal s1 s2 =
    USet.size s1 = USet.size s2
    && USet.for_all
         (fun j1 -> USet.exists (fun j2 -> Justification.equal j1 j2) s2)
         s1
  in

  let* final_justs =
    let rec fixed_point (justs : justification uset) =
      Logs.debug (fun m ->
          m "Fixed-point iteration with %d justifications:\n%s\n"
            (USet.size justs)
            (String.concat "\n\t"
               (USet.values (USet.map Justification.to_string justs))
            )
      );
      let* va = value_assign elab_ctx justs in
        let* lift = lift elab_ctx va in
          let* weak = weaken elab_ctx lift in
            let* fwd = forward elab_ctx weak in
              let* filtered = filter elab_ctx fwd in

              let justs_str =
                String.concat "\n\t"
                  (List.map Justification.to_string (USet.values filtered))
              in
                if justification_set_equal filtered justs then (
                  Logs.debug (fun m ->
                      m "Fixed-point reached with %d justifications:\n\t%s"
                        (USet.size filtered) justs_str
                  );
                  Lwt.return filtered
                )
                else (
                  Logs.debug (fun m ->
                      m "Continue elaborating with %d justifications:\n\t%s"
                        (USet.size filtered) justs_str
                  );
                  fixed_point filtered
                )
    in

    let* filtered_init = filter elab_ctx pre_justs in
      fixed_point filtered_init
  in
    Logs.debug (fun m ->
        m "Elaborations complete. Final justifications count: %d"
          (USet.size final_justs)
    );
    Lwt.return final_justs
