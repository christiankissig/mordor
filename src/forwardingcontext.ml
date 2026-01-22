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

(** {1 Global State} *)

(** Global mutable state for forwarding context.

    Stores the current event structure and precomputed relations needed for
    efficient PPO computation. State is initialized via {!init} and shared
    across all forwarding contexts. *)
module State = struct
  (** Set of all events in the current execution. *)
  let e : int uset ref = ref (USet.create ())

  (** The symbolic event structure being analyzed. *)
  let structure : symbolic_event_structure ref =
    ref (SymbolicEventStructure.create ())

  (** Function mapping event IDs to their values. *)
  let val_fn : (int -> expr option) ref = ref (fun _ -> None)

  (** Base location-based preserved program order. *)
  let ppo_loc_base : (int * int) uset ref = ref (USet.create ())

  (** Base preserved program order. *)
  let ppo_base : (int * int) uset ref = ref (USet.create ())

  (** Synchronization preserved program order. *)
  let ppo_sync : (int * int) uset ref = ref (USet.create ())

  (** Location-based PPO template (before PO intersection). *)
  let ppo_loc_baseA : (int * int) uset ref = ref (USet.create ())

  (** Location equality PPO component. *)
  let ppo_loc_eqA : (int * int) uset ref = ref (USet.create ())

  (** Synchronization PPO template (before PO intersection). *)
  let ppo_syncA : (int * int) uset ref = ref (USet.create ())

  (** Volatile PPO component. *)
  let ppo_volA : (int * int) uset ref = ref (USet.create ())

  (** Read-modify-write PPO component. *)
  let ppo_rmwA : (int * int) uset ref = ref (USet.create ())
end

(** {1 Context Classification} *)

(** Set of known-good forwarding contexts.

    Contexts proven to be satisfiable are cached here to avoid redundant solver
    queries. *)
let goodcon : ((int * int) uset * (int * int) uset) uset = USet.create ()

(** Set of known-bad forwarding contexts.

    Contexts proven to be unsatisfiable are cached here to quickly reject
    invalid configurations. *)
let badcon : ((int * int) uset * (int * int) uset) uset = USet.create ()

(** {1 Caching} *)

(** Cache key combining context and predicates.

    Used to look up previously computed PPO relations for a given forwarding
    context and predicate set. *)
type cache_key = {
  con : (int * int) uset * (int * int) uset;
      (** The forwarding context (fwd edges, we edges). *)
  predicates : expr list;  (** The predicate constraints. *)
}

(** Cache value storing computed PPO relations.

    Stores both standard PPO and location-specific PPO to avoid recomputation.
*)
type cache_value = {
  ppo : (int * int) uset option;  (** Preserved program order relation. *)
  ppo_loc : (int * int) uset option;
      (** Location-based preserved program order. *)
}

(** Cache for forwarding computations.

    Maintains two caches: an exact-match cache keyed by full context and
    predicates, and a subset cache that can return partial results when
    predicates are a superset of cached entries. *)
module FwdCache = struct
  (** Exact-match cache mapping keys to computed values. *)
  let cache : (cache_key, cache_value) Hashtbl.t = Hashtbl.create 256

  (** Context-indexed cache for subset lookups.

      Groups cache entries by context, allowing lookup of entries whose
      predicates are subsets of a query. *)
  let cache_con :
      ( (int * int) uset * (int * int) uset,
        (expr list * cache_value) list
      )
      Hashtbl.t =
    Hashtbl.create 256

  (** [clear ()] clears both caches.

      Should be called when the underlying program order changes. *)
  let clear () =
    Hashtbl.clear cache;
    Hashtbl.clear cache_con

  (** [get con predicates] retrieves cached value for exact match.

      @param con The forwarding context (fwd, we).
      @param predicates The predicate list.
      @return Cached value or empty value if not found. *)
  let get con predicates =
    let key = { con; predicates } in
      try Hashtbl.find cache key
      with Not_found -> { ppo = None; ppo_loc = None }

  (** [get_subset con predicates] finds cached entry with subset predicates.

      Searches for cached entries where the cached predicates are a subset of
      the query predicates. Returns the entry with the largest PPO.

      @param con The forwarding context.
      @param predicates The predicate list.
      @return [Some value] if matching entry found, [None] otherwise. *)
  let get_subset con predicates =
    try
      let pred_set = USet.of_list predicates in
      let entries = Hashtbl.find cache_con con in
      let matching =
        List.filter
          (fun (preds, _) -> USet.subset (USet.of_list preds) pred_set)
          entries
      in
        match matching with
        | [] -> None
        | _ ->
            (* Find entry with largest ppo *)
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
              Some (snd (List.hd sorted))
    with Not_found -> None

  (** [set con key predicates value] stores computed value in cache.

      Updates both the exact-match cache and the context-indexed cache.

      @param con The forwarding context.
      @param key Either ["ppo"] or ["ppo_loc"] to specify which field to update.
      @param predicates The predicate list.
      @param value The computed relation to store.
      @return The stored value. *)
  let set con key predicates value =
    let cache_key = { con; predicates } in
    let current = get con predicates in
    let updated =
      match key with
      | "ppo" -> { current with ppo = Some value }
      | "ppo_loc" -> { current with ppo_loc = Some value }
      | _ -> current
    in
      Hashtbl.replace cache cache_key updated;

      (* Update con cache *)
      let pred_list = predicates in
      let entries = try Hashtbl.find cache_con con with Not_found -> [] in
      let filtered = List.filter (fun (p, _) -> p <> pred_list) entries in
        Hashtbl.replace cache_con con ((pred_list, updated) :: filtered);

        value

  (** [size ()] returns the number of entries in the exact-match cache. *)
  let size () = Hashtbl.length cache
end

(** {1 Context Classification Queries} *)

(** [is_good fwd we] checks if context is known to be satisfiable.

    @param fwd The forwarding edge set.
    @param we The write-exclusion edge set.
    @return [true] if context is cached as good. *)
let is_good fwd we = USet.mem goodcon (fwd, we)

(** [is_bad fwd we] checks if context is known to be unsatisfiable.

    @param fwd The forwarding edge set.
    @param we The write-exclusion edge set.
    @return [true] if context is cached as bad. *)
let is_bad fwd we = USet.mem badcon (fwd, we)

(** {1 State Management} *)

(** [update_po po] updates PPO relations for new program order.

    Recomputes all PPO relations by intersecting templates with the given
    program order. Clears the forwarding cache since all cached results are now
    invalid.

    @param po The new program order relation. *)
let update_po po =
  State.ppo_loc_base := USet.intersection !State.ppo_loc_baseA po;
  State.ppo_sync := USet.intersection !State.ppo_syncA po;
  State.ppo_base := USet.union !State.ppo_volA !State.ppo_syncA;
  State.ppo_base := USet.inplace_union !State.ppo_base !State.ppo_rmwA;
  State.ppo_base := USet.inplace_union !State.ppo_base !State.ppo_loc_eqA;
  State.ppo_base := USet.intersection !State.ppo_base po;
  FwdCache.clear ()

(** Initialization parameters for forwarding context.

    Contains the event structure and value function needed to initialize the
    global state. *)
type init_params = {
  init_structure : symbolic_event_structure;
      (** The event structure to analyze. *)
  init_val : int -> expr option;
      (** Function mapping event IDs to their values. *)
}

(** [init params] initializes the forwarding context global state.

    Sets up all PPO templates according to the C11 memory model, including
    volatile, synchronization, and RMW orderings. Must be called before creating
    any forwarding contexts.

    Example usage:
    {[
      let* () = Forwardingcontext.init {
        init_structure = structure;
        init_val = val_function;
      } in
      ...
    ]}

    @param params Initialization parameters.
    @return Promise that completes when initialization is done. *)
let init params =
  let* _ = Lwt.return_unit in

  State.e := params.init_structure.e;
  let rmw = params.init_structure.rmw in
    State.structure := params.init_structure;
    State.val_fn := params.init_val;

    ignore (USet.clear goodcon);
    ignore (USet.clear badcon);

    let po = params.init_structure.po in

    (* Filter events by mode *)
    let filter_by_mode events mode_fn =
      USet.filter
        (fun e ->
          try
            let ev = Hashtbl.find !State.structure.events e in
              mode_fn ev
          with Not_found ->
            (* Event ID in E but not in events hashtable - skip it *)
            false
        )
        events
    in

    (* Event type filters *)
    let is_read ev = ev.typ = Read in
    let is_write ev = ev.typ = Write in
    let is_fence ev = ev.typ = Fence in
    let is_malloc ev = ev.typ = Malloc in
    let is_free ev = ev.typ = Free in

    let r = filter_by_mode !State.e is_read in
    let w = filter_by_mode !State.e is_write in
    let f = filter_by_mode !State.e is_fence in

    let e_vol =
      USet.filter
        (fun e ->
          try (Hashtbl.find !State.structure.events e).volatile
          with Not_found -> false
        )
        !State.e
    in

    let po_nf =
      USet.filter
        (fun (from, to_) ->
          try
            let from_ev = Hashtbl.find !State.structure.events from in
            let to_ev = Hashtbl.find !State.structure.events to_ in
              from_ev.typ <> Fence && to_ev.typ <> Fence
          with Not_found -> false
        )
        po
    in

    (* Mode filters *)
    let filter_order events mode =
      USet.filter
        (fun e ->
          let ev = Hashtbl.find !State.structure.events e in
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
    State.ppo_volA := USet.intersection (URelation.cross e_vol e_vol) po_nf;

    (* Synchronization ppo *)
    let e_squared = URelation.cross !State.e !State.e in
    let semicolon r1 r2 =
      let result =
        USet.create ()
        (*16*)
      in
        USet.iter
          (fun (a, b) ->
            USet.iter
              (fun (c, d) -> if b = c then USet.add result (a, d) |> ignore)
              r2
          )
          r1;
        result
    in

    let w_rel_sq = URelation.cross w_rel w_rel in
    let r_acq_sq = URelation.cross r_acq r_acq in
    let f_sc_sq = URelation.cross f_sc f_sc in
    let f_rel_sq = URelation.cross f_rel f_rel in
    let f_acq_sq = URelation.cross f_acq f_acq in
    let e_minus_r = USet.set_minus !State.e r in
    let e_minus_w = USet.set_minus !State.e w in

    State.ppo_syncA := semicolon e_squared w_rel_sq;
    State.ppo_syncA :=
      USet.inplace_union !State.ppo_syncA (semicolon r_acq_sq e_squared);
    State.ppo_syncA :=
      USet.inplace_union !State.ppo_syncA
        (semicolon e_squared (semicolon f_sc_sq e_squared));
    State.ppo_syncA :=
      USet.inplace_union !State.ppo_syncA
        (semicolon e_squared
           (semicolon f_rel_sq (URelation.cross e_minus_r e_minus_r))
        );
    State.ppo_syncA :=
      USet.inplace_union !State.ppo_syncA
        (semicolon
           (URelation.cross e_minus_w e_minus_w)
           (semicolon f_acq_sq e_squared)
        );
    State.ppo_syncA := USet.intersection !State.ppo_syncA po_nf;

    (* RMW ppo *)
    (* TODO fix RMW *)
    let rmw_inv = URelation.inverse rmw in
      State.ppo_rmwA :=
        USet.union
          (semicolon !State.ppo_syncA rmw_inv)
          (semicolon rmw_inv !State.ppo_syncA);

      (* Location-based ppo; TODO filter by if in events hash table? *)
      State.ppo_loc_baseA := USet.clone po_nf;

      (* Async filtering with semantic equality *)
      let* eqA =
        USet.async_filter
          (fun (e1, e2) ->
            let loc1 = Events.get_loc !State.structure e1 in
            let loc2 = Events.get_loc !State.structure e2 in
              match (loc1, loc2) with
              | Some l1, Some l2 -> Solver.exeq ~state:[] l1 l2
              | _ -> Lwt.return false
          )
          !State.ppo_loc_baseA
      in
        State.ppo_loc_eqA := eqA;
        State.ppo_loc_baseA :=
          USet.set_minus !State.ppo_loc_baseA !State.ppo_loc_eqA;

        Logs.debug (fun m ->
            m "ForwardingContext initialized with %d events" (USet.size !State.e)
        );

        update_po po;
        Lwt.return_unit

(** {1 Forwarding Context Type} *)

(** Forwarding context representing event reorderings.

    Encapsulates a set of forwarding edges (reads seeing later writes) and
    write-exclusion edges (writes being elided by later writes), along with
    derived information like value equalities and remapping tables. *)
type t = {
  fwd : (int * int) uset;
      (** Forwarding edges: [(e1, e2)] means [e2] reads from [e1]. *)
  we : (int * int) uset;
      (** Write-exclusion edges: [(e1, e2)] means [e1] is overwritten by [e2].
      *)
  valmap : (expr * expr) list;
      (** Value equalities implied by forwarding edges. *)
  psi : expr list;
      (** Constraints from value equalities (tautologies removed). *)
  fwdwe : (int * int) uset;
      (** Union of forwarding and write-exclusion edges. *)
  remap_map : (int, int) Hashtbl.t;
      (** Event remapping table after applying context. *)
}

(** [create ?fwd ?we ()] creates a new forwarding context.

    Builds derived information including value equalities, constraints, and the
    event remapping table.

    @param fwd Optional forwarding edge set (default: empty).
    @param we Optional write-exclusion edge set (default: empty).
    @return A new forwarding context. *)
let create ?(fwd = USet.create ()) ?(we = USet.create ()) () =
  let landmark = Landmark.register "ForwardingContext.create" in
    Landmark.enter landmark;
    let fwdwe = USet.union fwd we in

    (* valmap is filtered by non-None values *)
    let valmap =
      USet.values fwd
      |> List.filter_map (fun (e1, e2) ->
          match (!State.val_fn e1, !State.val_fn e2) with
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

    Landmark.exit landmark;
    { fwd; we; valmap; psi; fwdwe; remap_map }

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

    Updates the justification's forwarding and write-exclusion sets by combining
    them with the context's edges.

    @param ctx The forwarding context.
    @param just The justification to remap.
    @param op Optional operation descriptor (currently unused).
    @return The remapped justification. *)
let remap_just ctx (just : justification) op =
  let fwd = USet.union ctx.fwd just.fwd in
  let we = USet.union ctx.we just.we in
    { just with fwd; we }

(** {1 Cache Access} *)

(** [cache_get ctx predicates] retrieves exact cache match.

    @param ctx The forwarding context.
    @param predicates The predicate list.
    @return Cached value or empty value if not found. *)
let cache_get ctx predicates = FwdCache.get (ctx.fwd, ctx.we) predicates

(** [cache_get_subset ctx predicates] retrieves subset cache match.

    @param ctx The forwarding context.
    @param predicates The predicate list.
    @return [Some value] if matching entry found, [None] otherwise. *)
let cache_get_subset ctx predicates =
  FwdCache.get_subset (ctx.fwd, ctx.we) predicates

(** [cache_set ctx key predicates value] stores value in cache.

    @param ctx The forwarding context.
    @param key Either ["ppo"] or ["ppo_loc"].
    @param predicates The predicate list.
    @param value The computed relation.
    @return The stored value. *)
let cache_set ctx key predicates value =
  FwdCache.set (ctx.fwd, ctx.we) key predicates value

(** {1 PPO Computation} *)

(** [ppo ?debug ctx predicates] computes preserved program order.

    Computes the PPO relation by filtering base orderings through semantic alias
    analysis. Uses caching to avoid redundant solver queries.

    @param debug Optional flag to enable debug output (default: false).
    @param ctx The forwarding context.
    @param predicates Additional predicate constraints.
    @return Promise of the PPO relation. *)
let ppo ?(debug = false) ctx predicates =
  let landmark = Landmark.register "ForwardingContext.ppo" in
    Landmark.enter landmark;
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
                  | None -> !State.ppo_loc_base
                )
              | None -> !State.ppo_loc_base
            in
              (* Filter with alias analysis using solver - check if locations are
               equal given predicates and psi of forwarding context *)
              USet.async_filter
                (fun (e1, e2) ->
                  let loc1 = Events.get_loc !State.structure e1 in
                  let loc2 = Events.get_loc !State.structure e2 in
                    match (loc1, loc2) with
                    | Some l1, Some l2 -> Solver.exeq ~state:p l1 l2
                    | _ -> Lwt.return false
                )
                base
          in
          let u = USet.union !State.ppo_base result in
          let remapped = remap_rel ctx u in
            Landmark.exit landmark;
            Lwt.return (cache_set ctx "ppo" p remapped)

(** [ppo_loc ctx predicates] computes location-based PPO.

    Computes PPO restricted to events accessing the same concrete location. More
    precise than standard PPO as it requires exact location equality under the
    given predicates.

    @param ctx The forwarding context.
    @param predicates The predicate constraints.
    @return Promise of the location-based PPO relation. *)
let ppo_loc ctx predicates =
  let landmark = Landmark.register "ForwardingContext.ppo_loc" in
    Landmark.enter landmark;
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
                  let loc1 = Events.get_loc !State.structure e1 in
                  let loc2 = Events.get_loc !State.structure e2 in
                    match (loc1, loc2) with
                    | Some l1, Some l2 -> Solver.exeq ~state:p l1 l2
                    | _ -> Lwt.return false
                )
                ppo_alias
            in
            let remapped = remap_rel ctx filtered in
              Landmark.exit landmark;
              Lwt.return (cache_set ctx "ppo_loc" p remapped)

(** [ppo_sync ctx] computes synchronization PPO.

    Returns the synchronization-based preserved program order, which includes
    orderings from acquire-release, SC fences, and volatile accesses.

    @param ctx The forwarding context.
    @return The synchronization PPO relation. *)
let ppo_sync ctx = remap_rel ctx !State.ppo_sync

(** {1 Context Validation} *)

(** [check ctx] validates context satisfiability.

    Uses an SMT solver to check if the constraints implied by the forwarding
    context are satisfiable. Caches the result in good/bad context sets.

    @param ctx The forwarding context to validate.
    @return Promise of [true] if satisfiable, [false] otherwise. *)
let check ctx =
  let* result = Solver.check (Solver.create ctx.psi) in
    match result with
    | Some true ->
        USet.add goodcon (ctx.fwd, ctx.we) |> ignore;
        Lwt.return_true
    | _ ->
        USet.add badcon (ctx.fwd, ctx.we) |> ignore;
        Lwt.return_false

(** {1 Utilities} *)

(** [to_string ctx] converts context to string representation.

    @param ctx The forwarding context.
    @return String showing forwarding and write-exclusion edges. *)
let to_string ctx =
  Printf.sprintf "(%s, %s)"
    (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) ctx.fwd)
    (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) ctx.we)
