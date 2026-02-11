(** Forwarding context for symbolic execution.

    This module manages forwarding and write-exclusion contexts in symbolic
    event structures. It tracks how events can be reordered through forwarding
    (allowing reads to observe writes out of program order) and write-exclusion
    (ensuring certain writes don't interfere). The module computes preserved
    program order (PPO) relations under various memory model constraints. *)

open Algorithms
open Eventstructures
open Expr
open Lwt.Syntax
open Types
open Uset

(** {1 Event Structure Context} *)

(** Cache key for PPO computation.

    Combines the forwarding context (fwd, we) with predicate constraints to
    uniquely identify a PPO computation request. *)
type ppo_cache_key = {
  con : (int * int) uset * (int * int) uset;
      (** The context pair: (forwarding edges, write-exclusion edges). *)
  predicates : expr list;  (** Additional predicate constraints. *)
}

(** Cached PPO computation result.

    Stores both standard PPO and location-based PPO. Either or both may be
    [None] if not yet computed for this cache entry. *)
type ppo_cache_value = {
  ppo : (int * int) uset option;  (** Standard PPO relation. *)
  ppo_loc : (int * int) uset option;  (** Location-based PPO relation. *)
}

(** PPO computation cache.

    Caches preserved program order (PPO) computations to avoid redundant solver
    queries. Provides both exact-match and subset-based lookups. *)
module PpoCache : sig
  (** Cache type. *)
  type t

  (** [create ()] creates a new empty cache. *)
  val create : unit -> t

  (** [clear cache] clears all cached entries.

      Should be called when the underlying program order changes. *)
  val clear : t -> unit

  (** [get cache con predicates] retrieves exact cache match.

      @param cache The PPO cache.
      @param con The forwarding context (fwd, we).
      @param predicates The predicate list.
      @return Cached value or empty value if not found. *)
  val get :
    t -> (int * int) uset * (int * int) uset -> expr list -> ppo_cache_value

  (** [get_subset cache con predicates] finds cached entry with subset
      predicates.

      Searches for cached entries where the cached predicates are a subset of
      the query predicates. Returns the entry with the largest PPO.

      @param cache The PPO cache.
      @param con The forwarding context.
      @param predicates The predicate list.
      @return [Some value] if matching entry found, [None] otherwise. *)
  val get_subset :
    t ->
    (int * int) uset * (int * int) uset ->
    expr list ->
    ppo_cache_value option

  (** [set_ppo cache con predicates value] stores PPO in cache.

      Updates the cache with a computed PPO relation for the given context and
      predicates.

      @param cache The PPO cache.
      @param con The forwarding context.
      @param predicates The predicate list.
      @param value The computed PPO relation.
      @return The value that was stored. *)
  val set_ppo :
    t ->
    (int * int) uset * (int * int) uset ->
    expr list ->
    (int * int) uset ->
    (int * int) uset

  (** [set_ppo_loc cache con predicates value] stores location-based PPO in
      cache.

      Updates the cache with a computed location-based PPO relation.

      @param cache The PPO cache.
      @param con The forwarding context.
      @param predicates The predicate list.
      @param value The computed location-based PPO relation.
      @return The value that was stored. *)
  val set_ppo_loc :
    t ->
    (int * int) uset * (int * int) uset ->
    expr list ->
    (int * int) uset ->
    (int * int) uset

  (** [size cache] returns the number of cached entries.

      @param cache The PPO cache.
      @return Number of entries in the exact-match cache. *)
  val size : t -> int
end = struct
  type t = {
    exact : (ppo_cache_key, ppo_cache_value) Hashtbl.t;
        (** Exact-match cache mapping keys to computed values. *)
    by_context :
      ( (int * int) uset * (int * int) uset,
        (expr list * ppo_cache_value) list
      )
      Hashtbl.t;
        (** Context-indexed cache for subset lookups.

            Groups cache entries by context, allowing lookup of entries whose
            predicates are subsets of a query. *)
  }

  let create () =
    { exact = Hashtbl.create 256; by_context = Hashtbl.create 256 }

  let clear cache =
    Hashtbl.clear cache.exact;
    Hashtbl.clear cache.by_context

  let get cache con predicates =
    let key = { con; predicates } in
      match Hashtbl.find_opt cache.exact key with
      | Some v -> v
      | None -> { ppo = None; ppo_loc = None }

  let get_subset cache con predicates =
    match Hashtbl.find_opt cache.by_context con with
    | None -> None
    | Some entries -> (
        let pred_set = USet.of_list predicates in
        let matching =
          List.filter
            (fun (preds, _) -> USet.subset (USet.of_list preds) pred_set)
            entries
        in
          match matching with
          | [] -> None
          | _ ->
              let sorted =
                List.sort
                  (fun (_, v1) (_, v2) ->
                    let size1 =
                      match v1.ppo with
                      | Some s -> USet.size s
                      | None -> 0
                    in
                    let size2 =
                      match v2.ppo with
                      | Some s -> USet.size s
                      | None -> 0
                    in
                      compare size2 size1
                  )
                  matching
              in
              let v = snd (List.hd sorted) in
                Some v
      )

  (** [set_field cache con predicates field value] internal helper for updating
      cache fields.

      Updates either the ppo or ppo_loc field in the cache entry.

      @param cache The PPO cache.
      @param con The forwarding context.
      @param predicates The predicate list.
      @param field Function to update the desired field.
      @param value The new value.
      @return The value that was stored. *)
  let set_field cache con predicates field value =
    let key = { con; predicates } in
    let current =
      match Hashtbl.find_opt cache.exact key with
      | Some v -> v
      | None -> { ppo = None; ppo_loc = None }
    in
    let updated = field current value in
      Hashtbl.replace cache.exact key updated;

      (* Update by_context index *)
      let entries =
        match Hashtbl.find_opt cache.by_context con with
        | Some e -> e
        | None -> []
      in
      let filtered = List.filter (fun (p, _) -> p <> predicates) entries in
        Hashtbl.replace cache.by_context con ((predicates, updated) :: filtered);
        value

  let set_ppo cache con predicates value =
    set_field cache con predicates
      (fun v ppo -> { v with ppo = Some ppo })
      value

  let set_ppo_loc cache con predicates value =
    set_field cache con predicates
      (fun v ppo_loc -> { v with ppo_loc = Some ppo_loc })
      value

  let size cache = Hashtbl.length cache.exact
end

(** Context caching.

    Tracks which (fwd, we) contexts have been proven satisfiable (good) or
    unsatisfiable (bad) to avoid redundant solver queries. *)
module ContextCache : sig
  (** Cache type. *)
  type t

  (** [create ()] creates a new empty context cache. *)
  val create : unit -> t

  (** [clear cache] clears all cached context validity results.

      @param cache The context cache. *)
  val clear : t -> unit

  (** [is_good cache fwd we] checks if context is known satisfiable.

      @param cache The context cache.
      @param fwd The forwarding edges.
      @param we The write-exclusion edges.
      @return [true] if previously proven satisfiable. *)
  val is_good : t -> (int * int) uset -> (int * int) uset -> bool

  (** [is_bad cache fwd we] checks if context is known unsatisfiable.

      @param cache The context cache.
      @param fwd The forwarding edges.
      @param we The write-exclusion edges.
      @return [true] if previously proven unsatisfiable. *)
  val is_bad : t -> (int * int) uset -> (int * int) uset -> bool

  (** [mark_good cache fwd we] records that context is satisfiable.

      @param cache The context cache.
      @param fwd The forwarding edges.
      @param we The write-exclusion edges. *)
  val mark_good : t -> (int * int) uset -> (int * int) uset -> unit

  (** [mark_bad cache fwd we] records that context is unsatisfiable.

      @param cache The context cache.
      @param fwd The forwarding edges.
      @param we The write-exclusion edges. *)
  val mark_bad : t -> (int * int) uset -> (int * int) uset -> unit
end = struct
  type t = {
    good : ((int * int) uset * (int * int) uset) uset;
        (** Set of satisfiable contexts. *)
    bad : ((int * int) uset * (int * int) uset) uset;
        (** Set of unsatisfiable contexts. *)
  }

  let create () = { good = USet.create (); bad = USet.create () }

  let clear cache =
    USet.clear cache.good |> ignore;
    USet.clear cache.bad |> ignore

  let is_good cache fwd we = USet.mem cache.good (fwd, we)
  let is_bad cache fwd we = USet.mem cache.bad (fwd, we)
  let mark_good cache fwd we = USet.add cache.good (fwd, we) |> ignore
  let mark_bad cache fwd we = USet.add cache.bad (fwd, we) |> ignore
end

(** Precomputed PPO relations.

    These are templates computed once for the event structure and used as
    starting points for context-specific PPO computation. They represent various
    aspects of preserved program order under different memory models. *)
type ppo_relations = {
  ppo_init : (int * int) uset;
      (** Initial PPO relation.

          Relates all initial and terminal events to other events along program
          order edges. *)
  ppo_loc_base : (int * int) uset;
      (** Base location-based preserved program order.

          Includes orderings required for correct location-based semantics. *)
  ppo_base : (int * int) uset;
      (** Base preserved program order.

          Core orderings that must be preserved regardless of memory model. *)
  ppo_sync : (int * int) uset;
      (** Synchronization preserved program order.

          Orderings from acquire-release, SC fences, and volatile accesses. *)
  ppo_loc_baseA : (int * int) uset;
      (** Location-based PPO template (before PO intersection).

          Used as starting point for location-based PPO computation. *)
  ppo_loc_eqA : (int * int) uset;
      (** Location equality PPO component.

          Orderings between events that may access the same location. *)
  ppo_syncA : (int * int) uset;
      (** Synchronization PPO template (before PO intersection).

          Template for synchronization orderings before filtering. *)
  ppo_iter_loc_base : (int * int) uset;
      (** Base location-based preserved program order between iterations.

          Includes orderings required for correct location-based semantics. *)
  ppo_iter_base : (int * int) uset;
      (** Base preserved program order between iterations.

          Core orderings that must be preserved regardless of memory model. *)
  ppo_iter_sync : (int * int) uset;
      (** Synchronization preserved program order between iterations.

          Orderings from acquire-release, SC fences, and volatile accesses. *)
  ppo_iter_loc_baseA : (int * int) uset;
      (** Location-based PPO template (before PO intersection) between
          iterations.

          Used as starting point for location-based PPO computation. *)
  ppo_iter_loc_eqA : (int * int) uset;
      (** Location equality PPO component between iterations.

          Orderings between events that may access the same location. *)
  ppo_iter_syncA : (int * int) uset;
      (** Synchronization PPO template (before PO intersection) between
          iterations.

          Template for synchronization orderings before filtering. *)
}

(** Event structure context.

    Contains all data associated with a specific event structure. This is
    created once per event structure and shared across all forwarding contexts
    for that structure. Provides precomputed relations and caches. *)
type event_structure_context = {
  structure : symbolic_event_structure;
      (** The underlying symbolic event structure. *)
  e : int uset;  (** Set of all event IDs in the structure. *)
  val_fn : int -> expr option;
      (** Value function mapping event IDs to their symbolic values. *)
  ppo : ppo_relations;  (** Precomputed PPO relations. *)
  ppo_cache : PpoCache.t;  (** Cache for PPO computations. *)
  context_cache : ContextCache.t;  (** Cache for context validity checks. *)
}

(** Module for working with event structure contexts. *)
module EventStructureContext = struct
  (** Type alias for event structure context. *)
  type t = event_structure_context

  (** [create structure] creates a new event structure context.

      The PPO relations are initialized to empty and must be computed via
      {!init} before use.

      @param structure The symbolic event structure.
      @return A new event structure context with empty PPO relations. *)
  let create structure =
    {
      structure;
      e = structure.e;
      val_fn = Events.get_val structure;
      ppo =
        {
          ppo_init = USet.create ();
          ppo_loc_base = USet.create ();
          ppo_base = USet.create ();
          ppo_sync = USet.create ();
          ppo_loc_baseA = USet.create ();
          ppo_loc_eqA = USet.create ();
          ppo_syncA = USet.create ();
          (* PPO relations between events in successive iterations of the same loop. *)
          ppo_iter_loc_base = USet.create ();
          ppo_iter_base = USet.create ();
          ppo_iter_sync = USet.create ();
          ppo_iter_loc_baseA = USet.create ();
          ppo_iter_loc_eqA = USet.create ();
          ppo_iter_syncA = USet.create ();
        };
      ppo_cache = PpoCache.create ();
      context_cache = ContextCache.create ();
    }

  (* Helper to filter events by memory ordering mode *)
  let filter_order structure events mode =
    USet.filter
      (fun e ->
        let ev = Hashtbl.find structure.events e in
          match ev.typ with
          | Read -> ev.rmod = mode
          | Write -> ev.wmod = mode
          | Fence -> ev.fmod = mode
          | _ -> false
      )
      events

  let compute_ppo_init (structure : symbolic_event_structure) =
    let initial_events =
      if
        USet.mem structure.e 0
        &&
          try (Hashtbl.find structure.events 0).typ = Init
          with Not_found -> false
      then USet.singleton 0
      else USet.create ()
    in
      USet.filter
        (fun (f, t) ->
          USet.mem initial_events f || USet.mem structure.terminal_events t
        )
        structure.po

  (** [compute_ppo_syncA structure e po] computes the synchronization-based PPO
      template.

      This includes orderings from release/acquire modes and SC fences, as well
      as volatile accesses. The resulting relation is not yet intersected with
      program order and serves as a template for synchronization PPO.

      @param structure The symbolic event structure.
      @param e The set of events to consider.
      @param po The program order relation.
      @return The computed synchronization PPO template. *)
  let compute_ppo_syncA structure e po =
    let e_squared = URelation.cross e e in
    let r = USet.intersection structure.read_events e in
    let w = USet.intersection structure.write_events e in
    let f = USet.intersection structure.fence_events e in

    let w_rel =
      USet.union (filter_order structure w Release) (filter_order structure w SC)
    in
    let r_acq =
      USet.union (filter_order structure r Acquire) (filter_order structure r SC)
    in
    let f_rel = filter_order structure f Release in
    let f_acq = filter_order structure f Acquire in
    let f_sc = filter_order structure f SC in

    (* Synchronization ppo *)
    let w_rel_sq = URelation.cross w_rel w_rel in
    let r_acq_sq = URelation.cross r_acq r_acq in
    let f_sc_sq = URelation.cross f_sc f_sc in
    let f_rel_sq = URelation.cross f_rel f_rel in
    let f_acq_sq = URelation.cross f_acq f_acq in
    let e_minus_r = USet.set_minus e r in
    let e_minus_w = USet.set_minus e w in

    URelation.compose [ e_squared; w_rel_sq ]
    |> USet.inplace_union (URelation.compose [ r_acq_sq; e_squared ])
    |> USet.inplace_union (URelation.compose [ e_squared; f_sc_sq; e_squared ])
    |> USet.inplace_union
         (URelation.compose
            [ e_squared; f_rel_sq; URelation.cross e_minus_r e_minus_r ]
         )
    |> USet.inplace_union
         (URelation.compose
            [ URelation.cross e_minus_w e_minus_w; f_acq_sq; e_squared ]
         )
    |> USet.intersection po

  (** [compute_ppo_loc_eqA structure e po] computes the location equality PPO
      component.

      This relation includes pairs of events that may access the same location
      and thus require ordering to preserve location-based semantics. It is
      computed by filtering program order with a solver check for location
      equality under the given predicates.

      TODO computing this relative to the event structure, and not the
      predicates of an execution / value constraints of second event is too
      strong, as it would miss semantic equivalence of memory locations relative
      to execution constraints.

      @param structure The symbolic event structure.
      @param e The set of events to consider.
      @param po The program order relation.
      @return The computed location equality PPO component. *)
  let compute_ppo_loc_eqA ?(iter = false) structure e po =
    USet.async_filter
      (fun (e1, e2) ->
        let loc1 = Events.get_loc structure e1 in
        let loc2 =
          if iter then
            (* if iter, then adjust symbols read in the loop as potentially read
               in the previous iteration

               TODO this should factor in symbols read ppo-before this
               location, i.e. not possibly read in a previous iteration
               *)
            let symbols = symbols_in_loop structure e2 in
              Events.get_loc structure e2
              |> Option.map
                   (Expr.evaluate ~env:(fun s ->
                        if USet.mem symbols s then Some (ESymbol (s ^ "_next"))
                        else None
                    )
                   )
          else Events.get_loc structure e2
        in
          match (loc1, loc2) with
          | Some l1, Some l2 -> Solver.exeq ~state:[] l1 l2
          | _ -> Lwt.return false
      )
      po

  (** [clear_caches es_ctx] clears all caches in the context.

      Clears both the PPO computation cache and context validity cache.

      @param es_ctx The event structure context. *)
  let clear_caches es_ctx =
    ContextCache.clear es_ctx.context_cache;
    PpoCache.clear es_ctx.ppo_cache

  (** [init es_ctx] initializes PPO relations.

      Computes the base PPO relations that will be used as templates for all
      forwarding contexts. Must be called before creating forwarding contexts.

      This function:
      - Computes synchronization-based PPO from acquire/release and fences
      - Computes volatile-based PPO for volatile accesses
      - Performs semantic alias analysis for location-based PPO
      - Updates all PPO templates

      @param es_ctx The event structure context.
      @return Promise that resolves when initialization is complete. *)
  let init es_ctx =
    let landmark = Landmark.register "ForwardingContext.init" in
      Landmark.enter landmark;
      let rmw = es_ctx.structure.rmw in

      let structure = es_ctx.structure in
      let e = es_ctx.e in
      let po = es_ctx.structure.po in
      (* po_iter is the program order between events in successive iterations of
         the same loop. *)
      let po_iter = es_ctx.structure.po_iter in

      (* Program order without fences *)
      (* TODO 1) why this? 2) how about initial and terminal events? *)
      let po_nf =
        USet.filter
          (fun (f, t) ->
            (not (USet.mem es_ctx.structure.fence_events f))
            && not (USet.mem es_ctx.structure.fence_events t)
          )
          po
      in
      let po_iter_nf =
        USet.filter
          (fun (f, t) ->
            (not (USet.mem es_ctx.structure.fence_events f))
            && not (USet.mem es_ctx.structure.fence_events t)
          )
          po_iter
      in

      (* PPO from initial events and to terminal events *)
      USet.clear es_ctx.ppo.ppo_init |> ignore;
      USet.inplace_union es_ctx.ppo.ppo_init (compute_ppo_init structure)
      |> ignore;

      (* PPO based on memory order *)
      USet.clear es_ctx.ppo.ppo_syncA |> ignore;
      USet.inplace_union es_ctx.ppo.ppo_syncA
        (compute_ppo_syncA es_ctx.structure e po_nf)
      |> ignore;

      USet.clear es_ctx.ppo.ppo_iter_syncA |> ignore;
      USet.inplace_union es_ctx.ppo.ppo_iter_syncA
        (compute_ppo_syncA es_ctx.structure e po_iter_nf)
      |> ignore;

      (* Filter for location equality with semantic equality *)
      let* ppo_loc_eqA = compute_ppo_loc_eqA structure e po_nf in
        USet.clear es_ctx.ppo.ppo_loc_eqA |> ignore;
        USet.inplace_union es_ctx.ppo.ppo_loc_eqA ppo_loc_eqA |> ignore;

        (* PPO based on memory location *)
        (* TODO it is counter-intuitive that ppo_loc would be the complement of
         ppo_loc_eq *)
        USet.clear es_ctx.ppo.ppo_loc_baseA |> ignore;
        USet.set_minus po_nf ppo_loc_eqA
        |> USet.inplace_union es_ctx.ppo.ppo_loc_baseA
        |> ignore;

        let* ppo_iter_loc_eqA =
          compute_ppo_loc_eqA ~iter:true structure e po_iter_nf
        in
          USet.clear es_ctx.ppo.ppo_iter_loc_eqA |> ignore;
          USet.inplace_union es_ctx.ppo.ppo_iter_loc_eqA ppo_iter_loc_eqA
          |> ignore;

          USet.clear es_ctx.ppo.ppo_loc_baseA |> ignore;
          USet.set_minus po_nf ppo_loc_eqA
          |> USet.inplace_union es_ctx.ppo.ppo_loc_baseA
          |> ignore;

          (* TODO all of the relations above are already filtered on po_nf, which
  in turn is a subset of po, so this intersection should be redundant. *)
          USet.clear es_ctx.ppo.ppo_loc_base |> ignore;
          USet.intersection es_ctx.ppo.ppo_loc_baseA po
          |> USet.inplace_union es_ctx.ppo.ppo_loc_base
          |> ignore;

          USet.clear es_ctx.ppo.ppo_iter_loc_base |> ignore;
          USet.intersection es_ctx.ppo.ppo_iter_loc_baseA po
          |> USet.inplace_union es_ctx.ppo.ppo_iter_loc_base
          |> ignore;

          USet.clear es_ctx.ppo.ppo_sync |> ignore;
          USet.intersection es_ctx.ppo.ppo_syncA po
          |> USet.inplace_union es_ctx.ppo.ppo_sync
          |> ignore;

          USet.clear es_ctx.ppo.ppo_iter_sync |> ignore;
          USet.intersection es_ctx.ppo.ppo_iter_syncA po
          |> USet.inplace_union es_ctx.ppo.ppo_iter_sync
          |> ignore;

          USet.clear es_ctx.ppo.ppo_base |> ignore;
          USet.union es_ctx.ppo.ppo_syncA es_ctx.ppo.ppo_loc_eqA
          |> USet.intersection po
          |> USet.inplace_union es_ctx.ppo.ppo_base
          |> ignore;

          USet.clear es_ctx.ppo.ppo_iter_base |> ignore;
          USet.union es_ctx.ppo.ppo_iter_syncA es_ctx.ppo.ppo_iter_loc_eqA
          |> USet.intersection po
          |> USet.inplace_union es_ctx.ppo.ppo_base
          |> ignore;

          clear_caches es_ctx;

          Landmark.exit landmark;
          Lwt.return_unit
end

(** Forwarding context.

    Represents a specific forwarding and write-exclusion configuration for an
    event structure. Contains the edges being added and the resulting
    satisfiability constraints. *)
type forwarding_context = {
  es_ctx : event_structure_context;  (** The event structure context. *)
  fwd : (int * int) uset;  (** Forwarding edges (read observes write). *)
  we : (int * int) uset;  (** Write-exclusion edges (writes don't interfere). *)
  fwdwe : (int * int) uset;
      (** Combined forwarding and write-exclusion edges. *)
  remap_map : (int, int) Hashtbl.t;
      (** Remapping table for following forwarding chains. *)
  psi : expr list;  (** Path condition (satisfiability constraints). *)
}

(** Module for working with forwarding contexts. *)
module ForwardingContext = struct
  type t = forwarding_context

  (** [create es_ctx ?fwd ?we] creates a new forwarding context.

      Computes the remapping table and path condition for the given forwarding
      and write-exclusion edges.

      @param es_ctx The event structure context.
      @param fwd Forwarding edges to add.
      @param we Write-exclusion edges to add.
      @return The created forwarding context. *)
  let create es_ctx ?(fwd = USet.create ()) ?(we = USet.create ()) () =
    let landmark = Landmark.register "ForwardingContext.create" in
      Landmark.enter landmark;
      let fwdwe = USet.union fwd we in

      (* valmap is filtered by non-None values *)
      let valmap =
        USet.values fwd
        |> List.filter_map (fun (e1, e2) ->
            match (es_ctx.val_fn e1, es_ctx.val_fn e2) with
            | Some v1, Some v2 -> Some (v1, v2)
            | _ -> None
        )
      in

      (* Build path condition from forwarding *)
      let psi =
        List.filter_map
          (fun (e1, e2) ->
            let expr = Expr.evaluate (EBinOp (e1, "=", e2)) in
              match expr with
              | EBoolean true -> None
              | _ -> Some expr
          )
          valmap
      in

      (* Build remap map *)
      let remap_map =
        URelation.inverse fwdwe |> URelation.to_map |> map_transitive_closure
      in

      let ctx = { es_ctx; fwd; we; fwdwe; remap_map; psi } in
        Landmark.exit landmark;
        ctx

  (** {1 Remapping Operations} *)

  (** [remap ctx e] remaps a single event through the context.

      Follows forwarding chains and write-exclusion to find the canonical event
      that [e] maps to in this context.

      @param ctx The forwarding context.
      @param e The event ID to remap.
      @return The canonical event ID. *)
  let remap ctx e = try Hashtbl.find ctx.remap_map e with Not_found -> e

  (** [remap_rel ctx rel] remaps a relation through the context.

      Applies event remapping to both components of each pair in the relation,
      removing self-edges that result from remapping.

      @param ctx The forwarding context.
      @param rel The relation to remap.
      @return The remapped relation. *)
  let remap_rel ctx rel =
    USet.map
      (fun (from, to_) ->
        let from' = remap ctx from in
        let to_' = remap ctx to_ in
          (from', to_')
      )
      rel
    |> USet.filter (fun (from, to_) -> from <> to_)

  (** [remap_just ctx just] remaps a justification through the context.

      Updates the justification's forwarding and write-exclusion sets by
      combining them with the context's edges.

      @param ctx The forwarding context.
      @param just The justification to remap.
      @return The remapped justification. *)
  let remap_just ctx (just : justification) =
    let fwd = USet.union ctx.fwd just.fwd in
    let we = USet.union ctx.we just.we in
      { just with fwd; we }

  (** {1 Cache Access} *)

  (** [cache_get ctx predicates] retrieves exact cache match.

      @param ctx The forwarding context.
      @param predicates The predicate list.
      @return Cached value or empty value if not found. *)
  let cache_get ctx predicates =
    PpoCache.get ctx.es_ctx.ppo_cache (ctx.fwd, ctx.we) predicates

  (** [cache_get_subset ctx predicates] retrieves subset cache match.

      @param ctx The forwarding context.
      @param predicates The predicate list.
      @return [Some value] if matching entry found, [None] otherwise. *)
  let cache_get_subset ctx predicates =
    PpoCache.get_subset ctx.es_ctx.ppo_cache (ctx.fwd, ctx.we) predicates

  (** [cache_set_ppo ctx predicates value] stores PPO in cache.

      @param ctx The forwarding context.
      @param predicates The predicate list.
      @param value The computed PPO relation.
      @return The value that was stored. *)
  let cache_set_ppo ctx predicates value =
    PpoCache.set_ppo ctx.es_ctx.ppo_cache (ctx.fwd, ctx.we) predicates value

  (** [cache_set_ppo_loc ctx predicates value] stores location-based PPO in
      cache.

      @param ctx The forwarding context.
      @param predicates The predicate list.
      @param value The computed location-based PPO relation.
      @return The value that was stored. *)
  let cache_set_ppo_loc ctx predicates value =
    PpoCache.set_ppo_loc ctx.es_ctx.ppo_cache (ctx.fwd, ctx.we) predicates value

  (** [compute_ppo_rmw es_ctx] computes RMW-related PPO orderings.

      Computes additional PPO orderings induced by read-modify-write (RMW)
      pairs. This includes orderings from the read to the write and from the
      write to the read, filtered by semantic alias analysis to ensure they only
      include pairs that may access the same location.

      @param es_ctx The event structure context.
      @return The computed RMW-induced PPO orderings. *)
  let compute_ppo_rmw es_ctx predicates =
    let* rmw_filtered =
      USet.async_filter
        (fun (er, expr, ew) ->
          Solver.exeq ~state:predicates expr (EBoolean true)
        )
        es_ctx.structure.rmw
    in
    let rmw_inv = USet.map (fun (er, _, ew) -> (ew, er)) rmw_filtered in
    let rmw_ppo =
      USet.union
        (URelation.compose [ es_ctx.ppo.ppo_sync; rmw_inv ])
        (URelation.compose [ rmw_inv; es_ctx.ppo.ppo_sync ])
    in
      Lwt.return rmw_ppo

  (** {1 PPO Computation} *)

  (** [ppo ?debug ctx predicates] computes preserved program order.

      Computes the PPO relation by filtering base orderings through semantic
      alias analysis. Uses caching to avoid redundant solver queries.

      @param debug Optional flag to enable debug output (default: false).
      @param ctx The forwarding context.
      @param predicates Additional predicate constraints.
      @return Promise of the PPO relation. *)
  let ppo ?(debug = false) ctx predicates =
    let landmark = Landmark.register "ForwardingContext.ppo" in
      Landmark.enter landmark;
      let es_ctx = ctx.es_ctx in
      let p = predicates @ ctx.psi in
      let cached = cache_get ctx p in
        match cached.ppo with
        | Some v ->
            Landmark.exit landmark;
            Lwt.return v
        | _ ->
            let* result =
              let sub = cache_get_subset ctx p in
              let base =
                match sub with
                | Some s -> (
                    match s.ppo with
                    | Some ppo -> ppo
                    | None -> es_ctx.ppo.ppo_loc_base
                  )
                | None -> es_ctx.ppo.ppo_loc_base
              in
                (* Filter with alias analysis using solver - check if locations are
                   equal given predicates and psi of forwarding context *)
                USet.async_filter
                  (fun (e1, e2) ->
                    let loc1 = Events.get_loc es_ctx.structure e1 in
                    let loc2 = Events.get_loc es_ctx.structure e2 in
                      match (loc1, loc2) with
                      | Some l1, Some l2 -> Solver.exeq ~state:p l1 l2
                      | _ -> Lwt.return false
                  )
                  base
            in

            (* RMW ppo - add read-modify-write orderings *)
            let* rmw_ppo = compute_ppo_rmw es_ctx predicates in
            let result = USet.inplace_union result rmw_ppo in
            let result = USet.inplace_union result es_ctx.ppo.ppo_base in

            let remapped = remap_rel ctx result in
              cache_set_ppo ctx p remapped |> ignore;
              Landmark.exit landmark;
              Lwt.return remapped

  (** [ppo_loc ctx predicates] computes location-based PPO.

      Computes PPO restricted to events accessing the same concrete location.
      More precise than standard PPO as it requires exact location equality
      under the given predicates.

      @param ctx The forwarding context.
      @param predicates The predicate constraints.
      @return Promise of the location-based PPO relation. *)
  let ppo_loc ctx predicates =
    let landmark = Landmark.register "ForwardingContext.ppo_loc" in
      Landmark.enter landmark;
      let es_ctx = ctx.es_ctx in
      let p =
        predicates @ ctx.psi
        |> USet.of_list
        |> USet.values
        |> List.sort Expr.compare
      in
      let cached = cache_get ctx p in
        match cached.ppo_loc with
        | Some v ->
            Landmark.exit landmark;
            Lwt.return v
        | None ->
            (* Get base ppo_alias from cache or compute it *)
            let* ppo_alias =
              let sub = cache_get_subset ctx p in
                match sub with
                | Some s -> (
                    match (s.ppo_loc, s.ppo) with
                    | Some ppo_loc, _ -> Lwt.return ppo_loc
                    | None, Some ppo -> Lwt.return ppo
                    | None, None -> ppo ctx predicates
                  )
                | None -> ppo ctx predicates
            in
              (* Filter for exact location equality using the predicates P *)
              let* filtered =
                USet.async_filter
                  (fun (e1, e2) ->
                    let loc1 = Events.get_loc es_ctx.structure e1 in
                    let loc2 = Events.get_loc es_ctx.structure e2 in
                      match (loc1, loc2) with
                      | Some l1, Some l2 -> Solver.exeq ~state:p l1 l2
                      | _ -> Lwt.return false
                  )
                  ppo_alias
              in
              let remapped = remap_rel ctx filtered in
                cache_set_ppo_loc ctx p remapped |> ignore;
                Landmark.exit landmark;
                Lwt.return remapped

  (** [ppo_sync ctx] computes synchronization PPO.

      Returns the synchronization-based preserved program order, which includes
      orderings from acquire-release, SC fences, and volatile accesses.

      @param ctx The forwarding context.
      @return The synchronization PPO relation. *)
  let ppo_sync ctx = remap_rel ctx ctx.es_ctx.ppo.ppo_sync

  (** {1 Context Validation} *)

  (** [check ctx] validates context satisfiability.

      Uses an SMT solver to check if the constraints implied by the forwarding
      context are satisfiable. Caches the result in good/bad context sets.

      @param ctx The forwarding context to validate.
      @return Promise of [true] if satisfiable, [false] otherwise. *)
  let check ctx =
    let* result = Solver.quick_check_cached ctx.psi in
      match result with
      | Some true ->
          ContextCache.mark_good ctx.es_ctx.context_cache ctx.fwd ctx.we;
          Lwt.return_true
      | _ ->
          ContextCache.mark_bad ctx.es_ctx.context_cache ctx.fwd ctx.we;
          Lwt.return_false

  (** {1 Utilities} *)

  (** [to_string fwd_ctx] converts context to string representation.

      @param fwd_ctx The forwarding context.
      @return String showing forwarding and write-exclusion edges. *)
  let to_string fwd_ctx =
    Printf.sprintf "(%s, %s)"
      (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) fwd_ctx.fwd)
      (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) fwd_ctx.we)
end
