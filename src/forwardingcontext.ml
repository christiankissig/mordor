(** Forwarding Context for symbolic execution *)

open Types
open Justifications
open Lwt.Syntax

(** Global state - mutable references *)
module State = struct
  let e : int uset ref = ref (Hashtbl.create 0)
  let events : (int, event) Hashtbl.t ref = ref (Hashtbl.create 0)
  let val_fn : (int -> value_type option) ref = ref (fun _ -> None)
  let ppo_loc_base : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_base : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_sync : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_loc_baseA : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_loc_eqA : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_syncA : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_volA : (int * int) uset ref = ref (Hashtbl.create 0)
  let ppo_rmwA : (int * int) uset ref = ref (Hashtbl.create 0)
end

(** Good and bad contexts tracking *)
let goodcon : ((int * int) uset * (int * int) uset) uset = Hashtbl.create 16

let badcon : ((int * int) uset * (int * int) uset) uset = Hashtbl.create 16

(** Cache key type *)
type cache_key = {
  con : (int * int) uset * (int * int) uset;
  predicates : expr list;
}

(** Cache value type *)
type cache_value = {
  ppo : (int * int) uset option;
  ppo_loc : (int * int) uset option;
}

(** Forwarding cache *)
module FwdCache = struct
  let cache : (cache_key, cache_value) Hashtbl.t = Hashtbl.create 256

  let cache_con :
      ( (int * int) uset * (int * int) uset,
        (expr list * cache_value) list
      )
      Hashtbl.t =
    Hashtbl.create 256

  let clear () =
    Hashtbl.clear cache;
    Hashtbl.clear cache_con

  let get con predicates =
    let key = { con; predicates } in
      try Hashtbl.find cache key
      with Not_found -> { ppo = None; ppo_loc = None }

  let get_subset con predicates =
    try
      let pred_set = Uset.of_list predicates in
      let entries = Hashtbl.find cache_con con in
      let matching =
        List.filter
          (fun (preds, _) -> Uset.subset (Uset.of_list preds) pred_set)
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
                    | Some s -> Uset.size s
                    | None -> 0
                  in
                  let size2 =
                    match v2.ppo with
                    | Some s -> Uset.size s
                    | None -> 0
                  in
                    compare size2 size1
                )
                matching
            in
              Some (snd (List.hd sorted))
    with Not_found -> None

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

  let size () = Hashtbl.length cache
end

(** Check if context is good *)
let is_good fwd we = Uset.mem goodcon (fwd, we)

(** Check if context is bad *)
let is_bad fwd we = Uset.mem badcon (fwd, we)

(** Initialization parameters type *)
type init_params = {
  init_e : int uset;
  init_po : (int * int) uset;
  init_events : (int, event) Hashtbl.t;
  init_val : int -> value_type option;
  init_rmw : (int * int) uset;
}

(** Initialize forwarding context state Usage:
    {[
      let* () = ForwardingContext.init {
        init_e = structure.e;
        init_po = structure.po;
        init_events = events;
        init_val = val_function;
        init_rmw = structure.rmw;
      } in
      ...
    ]} *)
let init params =
  let* _ = Lwt.return_unit in

  State.e := params.init_e;
  let rmw = params.init_rmw in
    State.events := params.init_events;
    State.val_fn := params.init_val;

    ignore (Uset.clear goodcon);
    ignore (Uset.clear badcon);

    let po = params.init_po in

    (* Filter events by mode *)
    let filter_by_mode events mode_fn =
      Uset.filter
        (fun e ->
          try
            let ev = Hashtbl.find !State.events e in
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
    let is_branch ev = ev.typ = Branch in
    let is_malloc ev = ev.typ = Malloc in
    let is_free ev = ev.typ = Free in

    let r = filter_by_mode !State.e is_read in
    let w = filter_by_mode !State.e is_write in
    let f = filter_by_mode !State.e is_fence in
    let b = filter_by_mode !State.e is_branch in

    let e_vol =
      Uset.filter
        (fun e ->
          try (Hashtbl.find !State.events e).volatile with Not_found -> false
        )
        !State.e
    in

    let po_nf =
      Uset.filter
        (fun (from, to_) ->
          try
            let from_ev = Hashtbl.find !State.events from in
            let to_ev = Hashtbl.find !State.events to_ in
              from_ev.typ <> Fence
              && to_ev.typ <> Fence
              && from_ev.typ <> Branch
              && to_ev.typ <> Branch
          with Not_found -> false
        )
        po
    in

    (* Mode filters *)
    let filter_order events mode =
      Uset.filter
        (fun e ->
          let ev = Hashtbl.find !State.events e in
            match ev.typ with
            | Read -> ev.rmod = mode
            | Write -> ev.wmod = mode
            | Fence -> ev.fmod = mode
            | _ -> false
        )
        events
    in

    let w_rel = Uset.union (filter_order w Release) (filter_order w SC) in
    let r_acq = Uset.union (filter_order r Acquire) (filter_order r SC) in
    let f_rel = filter_order f Release in
    let f_acq = filter_order f Acquire in
    let f_sc = filter_order f SC in

    (* Volatile ppo *)
    State.ppo_volA := Uset.intersection (Uset.cross e_vol e_vol) po_nf;

    (* Synchronization ppo *)
    let e_squared = Uset.cross !State.e !State.e in
    let semicolon r1 r2 =
      let result = Hashtbl.create 16 in
        Uset.iter
          (fun (a, b) ->
            Uset.iter
              (fun (c, d) -> if b = c then Uset.add result (a, d) |> ignore)
              r2
          )
          r1;
        result
    in

    let w_rel_sq = Uset.cross w_rel w_rel in
    let r_acq_sq = Uset.cross r_acq r_acq in
    let f_sc_sq = Uset.cross f_sc f_sc in
    let f_rel_sq = Uset.cross f_rel f_rel in
    let f_acq_sq = Uset.cross f_acq f_acq in
    let e_minus_r = Uset.set_minus !State.e r in
    let e_minus_w = Uset.set_minus !State.e w in

    State.ppo_syncA := semicolon e_squared w_rel_sq;
    State.ppo_syncA :=
      Uset.inplace_union !State.ppo_syncA (semicolon r_acq_sq e_squared);
    State.ppo_syncA :=
      Uset.inplace_union !State.ppo_syncA
        (semicolon e_squared (semicolon f_sc_sq e_squared));
    State.ppo_syncA :=
      Uset.inplace_union !State.ppo_syncA
        (semicolon e_squared
           (semicolon f_rel_sq (Uset.cross e_minus_r e_minus_r))
        );
    State.ppo_syncA :=
      Uset.inplace_union !State.ppo_syncA
        (semicolon
           (Uset.cross e_minus_w e_minus_w)
           (semicolon f_acq_sq e_squared)
        );
    State.ppo_syncA := Uset.intersection !State.ppo_syncA po_nf;

    (* RMW ppo *)
    let rmw_inv = Uset.inverse_relation rmw in
      State.ppo_rmwA :=
        Uset.union
          (semicolon !State.ppo_syncA rmw_inv)
          (semicolon rmw_inv !State.ppo_syncA);

      (* Location-based ppo *)
      State.ppo_loc_baseA :=
        Uset.filter
          (fun (from, to_) ->
            try
              let from_ev = Hashtbl.find !State.events from in
              let to_ev = Hashtbl.find !State.events to_ in
                from_ev.id <> None && to_ev.id <> None
            with Not_found -> false
          )
          po_nf;

      (* Async filtering with semantic equality - simplified for now *)
      (* In real implementation, would use Solver.semeq *)
      State.ppo_loc_eqA := Uset.clone !State.ppo_loc_baseA;
      State.ppo_loc_baseA :=
        Uset.set_minus !State.ppo_loc_baseA !State.ppo_loc_eqA;

      Lwt.return_unit

(** Update with new program order *)
let update_po po =
  State.ppo_loc_base := Uset.intersection !State.ppo_loc_baseA po;
  State.ppo_sync := Uset.intersection !State.ppo_syncA po;
  State.ppo_base := Uset.union !State.ppo_volA !State.ppo_syncA;
  State.ppo_base := Uset.inplace_union !State.ppo_base !State.ppo_rmwA;
  State.ppo_base := Uset.inplace_union !State.ppo_base !State.ppo_loc_eqA;
  State.ppo_base := Uset.intersection !State.ppo_base po;
  FwdCache.clear ()

(** Forwarding context type *)
type t = {
  fwd : (int * int) uset;
  we : (int * int) uset;
  valmap : (value_type * value_type) list;
  psi : expr list;
  fwdwe : (int * int) uset;
  remap_map : (int, int) Hashtbl.t;
}

(** Create forwarding context *)
let create ?(fwd = Hashtbl.create 0) ?(we = Hashtbl.create 0) () =
  let fwdwe = Uset.union fwd we in

  (* valmap is filtered by non-None values *)
  let valmap =
    Uset.values fwd
    |> List.filter_map (fun (e1, e2) ->
           match (!State.val_fn e1, !State.val_fn e2) with
           | Some v1, Some v2 -> Some (v1, v2)
           | _ -> None
       )
  in

  let psi =
    List.filter_map (fun (v1, v2) -> Some (EBinOp (v1, "=", v2))) valmap
  in

  (* Build remap map *)
  let remap_map = Hashtbl.create 16 in
  let rec find_root e =
    match Uset.find (fun (e1, e2) -> e2 = e) fwdwe with
    | Some (e1, _) -> find_root e1
    | None -> e
  in
    Uset.iter (fun e -> Hashtbl.add remap_map e (find_root e)) !State.e;

    { fwd; we; valmap; psi; fwdwe; remap_map }

(** Remap single event *)
let remap ctx e = try Hashtbl.find ctx.remap_map e with Not_found -> e

(** Remap relation *)
let remap_rel ctx rel =
  Uset.map
    (fun (from, to_) ->
      let from' = remap ctx from in
      let to_' = remap ctx to_ in
        (from', to_')
    )
    rel
  |> Uset.filter (fun (from, to_) -> from <> to_)

(** Remap expression - simplified *)
let remap_expr ctx expr =
  (* In full implementation, would substitute values using valmap *)
  expr

(** Remap justification *)
let remap_just ctx (just : justification) op =
  let w =
    {
      just.w with
      wval = remap_expr ctx just.w.wval;
      id = Option.map (remap_expr ctx) just.w.id;
    }
  in
  let p = List.map (remap_expr ctx) just.p in
  let fwd = Uset.union ctx.fwd just.fwd in
  let we = Uset.union ctx.we just.we in
    {
      just with
      p;
      fwd;
      we;
      w;
      op =
        ( match op with
        | Some o -> o
        | None -> just.op
        );
    }

(** Get from cache *)
let cache_get ctx predicates = FwdCache.get (ctx.fwd, ctx.we) predicates

(** Get subset from cache *)
let cache_get_subset ctx predicates =
  FwdCache.get_subset (ctx.fwd, ctx.we) predicates

(** Set in cache *)
let cache_set ctx key predicates value =
  FwdCache.set (ctx.fwd, ctx.we) key predicates value

(** Compute preserved program order *)
let ppo ctx predicates =
  let p = predicates @ ctx.psi in
  let cached = cache_get ctx p in
    match cached.ppo with
    | Some v -> Lwt.return v
    | None ->
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
            (* In full implementation: filter with alias analysis using solver *)
            Lwt.return base
        in
        let remapped = remap_rel ctx (Uset.union !State.ppo_base result) in
          Lwt.return (cache_set ctx "ppo" p remapped)

(** Compute location-based preserved program order *)
let ppo_loc ctx predicates =
  let p = predicates @ ctx.psi in
  let cached = cache_get ctx p in
    match cached.ppo_loc with
    | Some v -> Lwt.return v
    | None ->
        let* ppo_result = ppo ctx predicates in
        (* In full implementation: additional filtering for exact location equality *)
        let remapped = remap_rel ctx ppo_result in
          Lwt.return (cache_set ctx "ppo_loc" p remapped)

(** Compute synchronization preserved program order *)
let ppo_sync ctx = remap_rel ctx !State.ppo_sync

(** Check context satisfiability *)
let check ctx =
  let* result = Solver.check (Solver.create ctx.psi) in
    match result with
    | Some true ->
        Uset.add goodcon (ctx.fwd, ctx.we) |> ignore;
        Lwt.return_true
    | _ ->
        Uset.add badcon (ctx.fwd, ctx.we) |> ignore;
        Lwt.return_false

(** Convert to string *)
let to_string ctx =
  Printf.sprintf "(%s, %s)" (Uset.to_string ctx.fwd) (Uset.to_string ctx.we)
