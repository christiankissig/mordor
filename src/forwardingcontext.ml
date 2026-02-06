(** Forwarding context for symbolic execution.

    This module manages forwarding and write-exclusion contexts in symbolic
    event structures. It tracks how events can be reordered through forwarding
    (allowing reads to observe writes out of program order) and write-exclusion
    (ensuring certain writes don't interfere). The module computes preserved
    program order (PPO) relations under various memory model constraints. *)

open Algorithms
open Expr
open Lwt.Syntax
open Types
open Uset

(** {1 Event Structure Context} *)
type ppo_cache_key = {
  con : (int * int) uset * (int * int) uset;
  predicates : expr list;
}

type ppo_cache_value = {
  ppo : (int * int) uset option;
  ppo_loc : (int * int) uset option;
}

(** PPO computation cache. *)
module PpoCache : sig
  type t

  val create : unit -> t
  val clear : t -> unit

  val get :
    t -> (int * int) uset * (int * int) uset -> expr list -> ppo_cache_value

  val get_subset :
    t ->
    (int * int) uset * (int * int) uset ->
    expr list ->
    ppo_cache_value option

  val set_ppo :
    t ->
    (int * int) uset * (int * int) uset ->
    expr list ->
    (int * int) uset ->
    (int * int) uset

  val set_ppo_loc :
    t ->
    (int * int) uset * (int * int) uset ->
    expr list ->
    (int * int) uset ->
    (int * int) uset

  val size : t -> int
end = struct
  type t = {
    exact : (ppo_cache_key, ppo_cache_value) Hashtbl.t;
        (** Exact-match cache mapping keys to computed values. was cache *)
    by_context :
      ( (int * int) uset * (int * int) uset,
        (expr list * ppo_cache_value) list
      )
      Hashtbl.t;
        (** Context-indexed cache for subset lookups.

            Groups cache entries by context, allowing lookup of entries whose
            predicates are subsets of a query. was cache_con *)
  }

  let create () =
    { exact = Hashtbl.create 256; by_context = Hashtbl.create 256 }

  (** [clear ()] clears both caches.

      Should be called when the underlying program order changes.

      TODO redundant? *)
  let clear cache =
    Hashtbl.clear cache.exact;
    Hashtbl.clear cache.by_context

  (** [get con predicates] retrieves cached value for exact match.

      @param con The forwarding context (fwd, we).
      @param predicates The predicate list.
      @return Cached value or empty value if not found. *)
  let get cache con predicates =
    let key = { con; predicates } in
      match Hashtbl.find_opt cache.exact key with
      | Some v -> v
      | None -> { ppo = None; ppo_loc = None }

  (** [get_subset con predicates] finds cached entry with subset predicates.

      Searches for cached entries where the cached predicates are a subset of
      the query predicates. Returns the entry with the largest PPO.

      @param con The forwarding context.
      @param predicates The predicate list.
      @return [Some value] if matching entry found, [None] otherwise. *)
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
  type t

  val create : unit -> t
  val clear : t -> unit
  val is_good : t -> (int * int) uset -> (int * int) uset -> bool
  val is_bad : t -> (int * int) uset -> (int * int) uset -> bool
  val mark_good : t -> (int * int) uset -> (int * int) uset -> unit
  val mark_bad : t -> (int * int) uset -> (int * int) uset -> unit
end = struct
  type t = {
    good : ((int * int) uset * (int * int) uset) uset;
    bad : ((int * int) uset * (int * int) uset) uset;
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
    starting points for context-specific PPO computation. *)
type ppo_relations = {
  ppo_loc_base : (int * int) uset;
      (** Base location-based preserved program order. *)
  ppo_base : (int * int) uset;  (** Base preserved program order. *)
  ppo_sync : (int * int) uset;  (** Synchronization preserved program order. *)
  ppo_loc_baseA : (int * int) uset;
      (** Location-based PPO template (before PO intersection). *)
  ppo_loc_eqA : (int * int) uset;  (** Location equality PPO component. *)
  ppo_syncA : (int * int) uset;
      (** Synchronization PPO template (before PO intersection). *)
  ppo_volA : (int * int) uset;  (** Volatile PPO component. *)
}

(** Event structure context.

    Contains all es_ctx associated with a specific event structure. This is
    created once per event structure and shared across all forwarding contexts
    for that structure. *)
type event_structure_context = {
  structure : symbolic_event_structure;
  e : int uset;
  val_fn : int -> expr option;
  ppo : ppo_relations;
  ppo_cache : PpoCache.t;
  context_cache : ContextCache.t;
}

(** Module for working with event structure contexts. *)
module EventStructureContext = struct
  type t = event_structure_context

  (** Create a new event structure context.

      The PPO relations are initialized to empty and must be computed via
      {!init} before use. *)
  let create structure =
    {
      structure;
      e = structure.e;
      val_fn = Events.get_val structure;
      ppo =
        {
          ppo_loc_base = USet.create ();
          ppo_base = USet.create ();
          ppo_sync = USet.create ();
          ppo_loc_baseA = USet.create ();
          ppo_loc_eqA = USet.create ();
          ppo_syncA = USet.create ();
          ppo_volA = USet.create ();
        };
      ppo_cache = PpoCache.create ();
      context_cache = ContextCache.create ();
    }

  (** Clear all caches. *)
  let clear_caches es_ctx =
    ContextCache.clear es_ctx.context_cache;
    PpoCache.clear es_ctx.ppo_cache

  (** [update_po po] updates PPO relations for new program order.

      Recomputes all PPO relations by intersecting templates with the given
      program order. Clears the forwarding cache since all cached results are
      now invalid.

      @param po The new program order relation. *)
  let update_po es_ctx po =
    USet.clear es_ctx.ppo.ppo_loc_base |> ignore;
    USet.intersection es_ctx.ppo.ppo_loc_baseA po
    |> USet.inplace_union es_ctx.ppo.ppo_loc_base
    |> ignore;

    USet.clear es_ctx.ppo.ppo_sync |> ignore;
    USet.intersection es_ctx.ppo.ppo_syncA po
    |> USet.inplace_union es_ctx.ppo.ppo_sync
    |> ignore;

    USet.clear es_ctx.ppo.ppo_base |> ignore;
    USet.union es_ctx.ppo.ppo_volA es_ctx.ppo.ppo_syncA
    |> USet.union es_ctx.ppo.ppo_loc_eqA
    |> USet.intersection po
    |> USet.inplace_union es_ctx.ppo.ppo_base
    |> ignore;

    clear_caches es_ctx

  (** Initialize PPO relations.

      Computes the base PPO relations that will be used as templates for all
      forwarding contexts. Must be called before creating forwarding contexts.
  *)
  let init es_ctx =
    let landmark = Landmark.register "ForwardingContext.init" in
      Landmark.enter landmark;
      let rmw = es_ctx.structure.rmw in

      clear_caches es_ctx;

      let po = es_ctx.structure.po in

      let e = es_ctx.e in
      let r = USet.intersection es_ctx.structure.read_events e in
      let w = USet.intersection es_ctx.structure.write_events e in
      let f = USet.intersection es_ctx.structure.fence_events e in

      let e_vol =
        USet.filter
          (fun e ->
            try (Hashtbl.find es_ctx.structure.events e).volatile
            with Not_found -> false
          )
          es_ctx.e
      in

      let po_nf =
        USet.filter
          (fun (f, t) ->
            (not (USet.mem es_ctx.structure.fence_events f))
            && not (USet.mem es_ctx.structure.fence_events t)
          )
          po
      in

      (* Mode filters *)
      (* TODO pregenerate in interpret *)
      let filter_order events mode =
        USet.filter
          (fun e ->
            let ev = Hashtbl.find es_ctx.structure.events e in
              match ev.typ with
              | Read -> ev.rmod = mode
              | Write -> ev.wmod = mode
              | Fence -> ev.fmod = mode
              | _ -> false
          )
          events
      in

      let w_rel = USet.union (filter_order w Release) (filter_order w SC) in
      let r_acq = USet.union (filter_order r Acquire) (filter_order r SC) in
      let f_rel = filter_order f Release in
      let f_acq = filter_order f Acquire in
      let f_sc = filter_order f SC in

      (* Volatile ppo *)
      URelation.cross e_vol e_vol
      |> USet.intersection po_nf
      |> USet.inplace_union es_ctx.ppo.ppo_volA
      |> ignore;

      (* Synchronization ppo *)
      let e_squared = URelation.cross es_ctx.e es_ctx.e in
      let semicolon r1 r2 = URelation.compose [ r1; r2 ] in

      let w_rel_sq = URelation.cross w_rel w_rel in
      let r_acq_sq = URelation.cross r_acq r_acq in
      let f_sc_sq = URelation.cross f_sc f_sc in
      let f_rel_sq = URelation.cross f_rel f_rel in
      let f_acq_sq = URelation.cross f_acq f_acq in
      let e_minus_r = USet.set_minus es_ctx.e r in
      let e_minus_w = USet.set_minus es_ctx.e w in

      USet.clear es_ctx.ppo.ppo_syncA |> ignore;
      semicolon e_squared w_rel_sq
      |> USet.inplace_union (semicolon r_acq_sq e_squared)
      |> USet.inplace_union (semicolon e_squared (semicolon f_sc_sq e_squared))
      |> USet.inplace_union
           (semicolon e_squared
              (semicolon f_rel_sq (URelation.cross e_minus_r e_minus_r))
           )
      |> USet.inplace_union
           (semicolon
              (URelation.cross e_minus_w e_minus_w)
              (semicolon f_acq_sq e_squared)
           )
      |> USet.intersection po_nf
      |> USet.inplace_union es_ctx.ppo.ppo_syncA
      |> ignore;

      (* Async filtering with semantic equality *)
      let* eqA =
        USet.async_filter
          (fun (e1, e2) ->
            let loc1 = Events.get_loc es_ctx.structure e1 in
            let loc2 = Events.get_loc es_ctx.structure e2 in
              match (loc1, loc2) with
              | Some l1, Some l2 -> Solver.exeq ~state:[] l1 l2
              | _ -> Lwt.return false
          )
          po_nf
      in
        USet.clear es_ctx.ppo.ppo_loc_eqA |> ignore;
        USet.inplace_union es_ctx.ppo.ppo_loc_eqA eqA |> ignore;
        (* Location-based ppo; TODO filter by if in events hash table? *)
        USet.clear es_ctx.ppo.ppo_loc_baseA |> ignore;
        USet.set_minus po_nf eqA
        |> USet.inplace_union es_ctx.ppo.ppo_loc_baseA
        |> ignore;

        Logs.debug (fun m ->
            m "ForwardingContext initialized with %d events" (USet.size es_ctx.e)
        );

        update_po es_ctx po;
        Landmark.exit landmark;
        Lwt.return_unit
end

(** {1 Forwarding Context}

    This section defines specific forwarding contexts for (fwd, we) pairs. *)

(** Forwarding context.

    Represents a specific forwarding context with fwd and we edges, predicates,
    and event remapping. *)
type forwarding_context = {
  es_ctx : event_structure_context;
  fwd : (int * int) uset;
  we : (int * int) uset;
  psi : expr list;
  fwdwe : (int * int) uset;
  remap_map : (int, int) Hashtbl.t;
}

module ForwardingContext : sig
  (** Forwarding context representing event reorderings.

      Encapsulates a set of forwarding edges (reads seeing later writes) and
      write-exclusion edges (writes being elided by later writes), along with
      derived information like value equalities and remapping tables. *)
  type t = forwarding_context

  (** [create ~structure ?fwd ?we ()] creates a new forwarding context.

      Builds derived information including value equalities, constraints, and
      the event remapping table.

      @param structure The symbolic event structure.
      @param fwd Optional forwarding edge set (default: empty).
      @param we Optional write-exclusion edge set (default: empty).
      @return A new forwarding context. *)
  val create :
    event_structure_context ->
    ?fwd:(int * int) uset ->
    ?we:(int * int) uset ->
    unit ->
    t

  (** [remap ctx e] remaps a single event through the context.

      Follows forwarding chains and write-exclusion to find the canonical event
      that [e] maps to in this context.

      @param ctx The forwarding context.
      @param e The event ID to remap.
      @return The canonical event ID. *)
  val remap : t -> int -> int

  (** [remap_rel ctx rel] remaps a relation through the context.

      Applies event remapping to both components of each pair in the relation,
      removing self-edges that result from remapping.

      @param ctx The forwarding context.
      @param rel The relation to remap.
      @return The remapped relation. *)
  val remap_rel : t -> (int * int) uset -> (int * int) uset

  (** [remap_just ctx just op] remaps a justification through the context.

      Updates the justification's forwarding and write-exclusion sets by
      combining them with the context's edges.

      @param ctx The forwarding context.
      @param just The justification to remap.
      @param op Optional operation descriptor (currently unused).
      @return The remapped justification. *)
  val remap_just : t -> justification -> justification

  (** [ppo ?debug ctx predicates] computes preserved program order.

      Computes the PPO relation by filtering base orderings through semantic
      alias analysis. Uses caching to avoid redundant solver queries.

      @param debug Optional flag to enable debug output (default: false).
      @param ctx The forwarding context.
      @param predicates Additional predicate constraints.
      @return Promise of the PPO relation. *)
  val ppo : ?debug:bool -> t -> expr list -> (int * int) uset Lwt.t

  (** [ppo_loc ctx predicates] computes location-based PPO.

      Computes PPO restricted to events accessing the same concrete location.
      More precise than standard PPO as it requires exact location equality
      under the given predicates.

      @param ctx The forwarding context.
      @param predicates The predicate constraints.
      @return Promise of the location-based PPO relation. *)
  val ppo_loc : t -> expr list -> (int * int) uset Lwt.t

  (** [ppo_sync ctx] computes synchronization PPO.

      Returns the synchronization-based preserved program order, which includes
      orderings from acquire-release, SC fences, and volatile accesses.

      @param ctx The forwarding context.
      @return The synchronization PPO relation. *)
  val ppo_sync : t -> (int * int) uset

  (** [check ctx] validates context satisfiability.

      Uses an SMT solver to check if the constraints implied by the forwarding
      context are satisfiable. Caches the result in good/bad context sets.

      @param ctx The forwarding context to validate.
      @return Promise of [true] if satisfiable *)
  val check : t -> bool Lwt.t

  val cache_set_ppo : t -> expr list -> (int * int) uset -> (int * int) uset
  val cache_set_ppo_loc : t -> expr list -> (int * int) uset -> (int * int) uset

  (** [cache_get ctx predicates] retrieves exact cache match.

      @param ctx The forwarding context.
      @param predicates The predicate list.
      @return Cached value or empty value if not found. *)
  val cache_get : t -> expr list -> ppo_cache_value

  (** [cache_get_subset ctx predicates] retrieves subset cache match.

      @param ctx The forwarding context.
      @param predicates The predicate list.
      @return [Some value] if matching entry found, [None] otherwise. *)
  val cache_get_subset : t -> expr list -> ppo_cache_value option

  (** [to_string ctx] converts context to human-readable string.

      Format: [{valmap} | {fwd} | {we}]

      @param ctx The forwarding context.
      @return String representation showing all components. *)
  val to_string : t -> string
end = struct
  (** Forwarding context representing event reorderings.

      Encapsulates a set of forwarding edges (reads seeing later writes) and
      write-exclusion edges (writes being elided by later writes), along with
      derived information like value equalities and remapping tables. *)
  type t = forwarding_context

  (** [create ?fwd ?we ()] creates a new forwarding context.

      Builds derived information including value equalities, constraints, and
      the event remapping table.

      @param fwd Optional forwarding edge set (default: empty).
      @param we Optional write-exclusion edge set (default: empty).
      @return A new forwarding context. *)
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

      let ctx = { es_ctx; fwd; we; psi; fwdwe; remap_map } in
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

  (** [remap_just ctx just op] remaps a justification through the context.

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

  let cache_set_ppo ctx predicates value =
    PpoCache.set_ppo ctx.es_ctx.ppo_cache (ctx.fwd, ctx.we) predicates value

  let cache_set_ppo_loc ctx predicates value =
    PpoCache.set_ppo_loc ctx.es_ctx.ppo_cache (ctx.fwd, ctx.we) predicates value

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

            (* RMW ppo *)
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
