(** Coherence checking for memory models *)

open Algorithms
open Expr
open Types
open Uset

(** {1 Core Abstractions} *)

module type MEMORY_MODEL = sig
  type cache
  type config

  val name : string
  val default_config : config

  val build_cache :
    symbolic_execution ->
    symbolic_event_structure ->
    (int, event) Hashtbl.t ->
    ((int * int) uset -> (int * int) uset) ->
    cache

  val check_coherence : (int * int) uset -> cache -> bool
  val check_thin_air : symbolic_execution -> cache -> bool

  val compute_dependencies :
    symbolic_execution ->
    (int, event) Hashtbl.t ->
    (int * int) uset ->
    int uset ->
    (int, expr list) Hashtbl.t ->
    (int * int) uset
end

(** {1 Shared logic} *)

(** Shared utilities module *)
module ModelUtils = struct
  (** Event matching - shared across all models *)
  let match_events (events : (int, event) Hashtbl.t) (e : int uset)
      (typ : event_type) (mode_opt : mode option) (op_opt : string option)
      (second_mode_opt : mode option) : (int * int) uset =
    let landmark = Landmark.register "ModelUtils.match_events" in
      Landmark.enter landmark;
      let result = USet.create () in
        USet.iter
          (fun ev_id ->
            try
              let event = Hashtbl.find events ev_id in
              let type_match = event.typ = typ in
              let mode_match =
                match mode_opt with
                | None -> true
                | Some m -> event.rmod = m || event.wmod = m || event.fmod = m
              in
              let second_mode_match =
                match second_mode_opt with
                | None -> true
                | Some m -> (
                    match event.strong with
                    | Some sm -> sm = m
                    | None -> false
                  )
              in
                if type_match && mode_match && second_mode_match then
                  USet.add result ev_id |> ignore
            with Not_found -> ()
          )
          e;
        let result = URelation.identity result in
          Landmark.exit landmark;
          result

  (** Thread-local restriction *)
  let thread_internal po x = USet.intersection x po

  let thread_external po x = USet.set_minus x po

  (** Common relation builders *)
  (* let build_release_sequence events e po rf rmw loc_restrict = ... *)

  (* let build_synchronizes_with events e po rf release loc_restrict = ... *)
end

(** {1 Memory Model Implementations} *)

module IMM : MEMORY_MODEL = struct
  (** Cache type *)
  type cache = {
    hb : (int * int) uset;
    rf : (int * int) uset;
    rfi : (int * int) uset;
    ar_ : (int * int) uset;
    po : (int * int) uset;
    psc_a : (int * int) uset;
    psc_b : (int * int) uset;
    rmw : (int * int) uset;
  }

  (** Config type *)
  type config = unit

  let name = "imm"
  let default_config = ()

  (** IMM coherence cache builder *)
  let build_cache (execution : symbolic_execution)
      (structure : symbolic_event_structure) (events : (int, event) Hashtbl.t)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    let landmark = Landmark.register "IMM.build_cache" in
      Landmark.enter landmark;

      let ({ e; rf; ex_rmw; _ } : symbolic_execution) = execution in
      let ({ po; restrict; _ } : symbolic_event_structure) = structure in
      let _E = e in

      let rf = USet.clone rf in
      let po = USet.clone po in
      let rmw = USet.clone ex_rmw in

      let thread_internal_restriction x = USet.intersection x po in
      let thread_external_restriction x = USet.set_minus x po in

      let w = ModelUtils.match_events events _E Write None None None in

      (* rs = [W];(po ∩ loc);[W] ∪ [W];([po ∩ loc]?;rf;rmw)⁺? *)
      let rs =
        let part1 = URelation.compose [ w; loc_restrict po; w ] in
        let inner =
          URelation.compose
            [ URelation.reflexive_closure _E (loc_restrict po); rf; rmw ]
        in
        let part2 =
          URelation.compose
            [
              w;
              URelation.reflexive_closure _E (URelation.transitive_closure inner);
            ]
        in
          USet.inplace_union part1 part2
      in

      (* release = ([W_rel] ∪ [F_rel];po);rs *)
      let release =
        let w_rel =
          ModelUtils.match_events events _E Write (Some Release) None None
        in
        let f_rel_po =
          URelation.compose
            [
              ModelUtils.match_events events _E Fence (Some Release) (Some ">")
                None;
              po;
            ]
        in
          URelation.compose [ USet.inplace_union w_rel f_rel_po; rs ]
      in

      (* sw = release;(rf ∩ ¬po ∪ [po ∩ loc]?;(rf \ po));([R_acq] ∪ po;[F_acq]) *)
      let sw =
        let rfi = thread_internal_restriction rf in
        let rfe = thread_external_restriction rf in
        let middle =
          URelation.compose
            [ URelation.reflexive_closure _E (loc_restrict po); rfe ]
          |> USet.union rfi
        in
        let r_acq =
          ModelUtils.match_events events _E Read (Some Acquire) None None
        in
        let po_f_acq =
          URelation.compose
            [
              po;
              ModelUtils.match_events events _E Fence (Some Acquire) (Some ">")
                None;
            ]
        in
          URelation.compose [ release; middle; USet.union r_acq po_f_acq ]
      in

      (* hb = (sw ∪ po)⁺ *)
      let hb = USet.union sw po |> URelation.transitive_closure in

      (* bob (bounded ordered-before) *)
      let bob =
        let p1 =
          URelation.compose
            [
              po;
              ModelUtils.match_events events _E Write (Some Release) None None;
            ]
        in
        let p2 =
          URelation.compose
            [
              ModelUtils.match_events events _E Read (Some Acquire) None None;
              po;
            ]
        in
        let p3 =
          URelation.compose
            [ po; ModelUtils.match_events events _E Fence None None None ]
        in
        let p4 =
          URelation.compose
            [ ModelUtils.match_events events _E Fence None None None; po ]
        in
        let p5 =
          URelation.compose
            [
              ModelUtils.match_events events _E Write (Some Release) None None;
              loc_restrict po;
              ModelUtils.match_events events _E Write None None None;
            ]
        in
          USet.union p1 p2
          |> USet.inplace_union p3
          |> USet.inplace_union p4
          |> USet.inplace_union p5
      in

      let deps = execution.dp in

      (* ppo = [R];(rf ∩ ¬po ∪ deps)⁺;[W] *)
      let ppo =
        let r = ModelUtils.match_events events _E Read None None None in
        let w = ModelUtils.match_events events _E Write None None None in
        let middle =
          URelation.transitive_closure
            (USet.inplace_union (thread_internal_restriction rf) deps)
        in
          URelation.compose [ r; middle; w ]
      in

      (* strong_ = [W_strong];po;[W] *)
      let strong_ =
        URelation.compose
          [
            ModelUtils.match_events events _E Write None None (Some Strong);
            po;
            ModelUtils.match_events events _E Write None None None;
          ]
      in

      (* ar_ = (rf \ po) ∪ bob ∪ ppo ∪ strong_ *)
      let ar_ =
        thread_external_restriction rf
        |> USet.inplace_union bob
        |> USet.inplace_union ppo
        |> USet.inplace_union strong_
      in

      (* psc_a = [F_sc];hb *)
      let psc_a =
        URelation.compose
          [ ModelUtils.match_events events _E Fence (Some SC) None None; hb ]
      in

      (* psc_b = hb;[F_sc] *)
      let psc_b =
        URelation.compose
          [ hb; ModelUtils.match_events events _E Fence (Some SC) None None ]
      in

      Landmark.exit landmark;
      { hb; rf; rfi = URelation.inverse rf; ar_; po; psc_a; psc_b; rmw }

  (** IMM coherence checker *)
  let check_coherence (co : (int * int) uset) (cache : cache) : bool =
    let { hb; rfi; po; rf; ar_; psc_a; psc_b; rmw; _ } = cache in

    let landmark = Landmark.register "IMM.check_coherence" in
      Landmark.enter landmark;

      let result =
        let ( let*? ) (condition, msg) f = if condition then f () else false in

        let thread_external_restriction x = USet.set_minus x po in

        let dummy_adj_map = Hashtbl.create 0 in

        let co_adj_map = URelation.adjacency_map co in
        let rf_adj_map = URelation.adjacency_map rf in

        (* fr = rf⁻¹;co *)
        let fr = URelation.compose [ rfi; co ] in
        let fre = thread_external_restriction fr in

        (* eco = rf ∪ co;rf ∪ co ∪ fr;rf ∪ fr *)
        let eco =
          URelation.compose_adj_map [ (co, dummy_adj_map); (rf, rf_adj_map) ]
          |> USet.inplace_union rf
          |> USet.inplace_union co
          |> USet.inplace_union
               (URelation.compose_adj_map
                  [ (fr, dummy_adj_map); (rf, rf_adj_map) ]
               )
          |> USet.inplace_union fr
        in

        let eco_adj_map = URelation.adjacency_map eco in
        let hb_adj_map = URelation.adjacency_map hb in

        (* Coherence: hb;eco ∪ hb is irreflexive *)
        let hb_eco_hb =
          USet.inplace_union
            (URelation.compose_adj_map [ (hb, hb_adj_map); (eco, eco_adj_map) ])
            hb
        in
        let hb_eco_hb_irreflexive = URelation.is_irreflexive hb_eco_hb in
          let*? () = (hb_eco_hb_irreflexive, "hb;eco ∪ hb is irreflexive") in

          (* Thin-air *)
          let coe = thread_external_restriction co in
          let coe_adj_map = URelation.adjacency_map coe in
          let rfe = thread_external_restriction rf in
          let rfe_adj_map = URelation.adjacency_map rfe in
          let detour =
            URelation.compose_adj_map [ (coe, coe_adj_map); (rfe, rfe_adj_map) ]
            |> USet.intersection po
          in
          let psc_b_adj_map = URelation.adjacency_map psc_b in
          let psc =
            URelation.compose_adj_map
              [
                (psc_a, dummy_adj_map);
                (eco, eco_adj_map);
                (psc_b, psc_b_adj_map);
              ]
          in
          let ar = USet.union ar_ psc |> USet.inplace_union detour in

          let*? () = (URelation.acyclic ar, "ar is acyclic") in

          if
            (* Atomicity *)
            USet.size rmw = 0
          then true
          else
            let rmw_fre_coe_empty =
              USet.size
                (URelation.compose_adj_map
                   [ (fre, dummy_adj_map); (coe, coe_adj_map) ]
                |> USet.intersection rmw
                )
              = 0
            in
              let*? () = (rmw_fre_coe_empty, "rmw ∩ (fre;coe) = ∅") in
                true
      in
        Landmark.exit landmark;
        result

  let check_thin_air execution cache = true

  (** IMM dependency calculation *)
  let compute_dependencies (execution : symbolic_execution)
      (events : (int, event) Hashtbl.t) (po : (int * int) uset) (e : int uset)
      (restrict : (int, expr list) Hashtbl.t) : (int * int) uset =
    let landmark = Landmark.register "IMM.compute_dependencies" in
      Landmark.enter landmark;

      (* data = [R];po;[W] where wval references rval *)
      let data =
        let r_w =
          URelation.compose
            [
              ModelUtils.match_events events e Read None None None;
              po;
              ModelUtils.match_events events e Write None None None;
            ]
        in
          USet.filter
            (fun (from_id, to_id) ->
              try
                let from_ev = Hashtbl.find events from_id in
                let to_ev = Hashtbl.find events to_id in
                  match (from_ev.rval, to_ev.wval) with
                  | Some rv, Some wv ->
                      (* Simple structural equality or symbol dependency check *)
                      USet.value_equality (Expr.of_value rv) wv
                  | _ -> false
              with Not_found -> false
            )
            r_w
      in

      (* ctrl = [R];po where restrict differs *)
      let ctrl =
        let r_po =
          URelation.compose
            [ ModelUtils.match_events events e Read None None None; po ]
        in
          USet.filter
            (fun (from_id, to_id) ->
              try
                let from_restrict = Hashtbl.find restrict from_id in
                let to_restrict = Hashtbl.find restrict to_id in
                  from_restrict <> to_restrict
              with Not_found -> false
            )
            r_po
      in

      let addr = USet.create () in
      let casdep = USet.create () in
      let rex = USet.create () in

      (* data ∪ ctrl ∪ addr;po? ∪ addr ∪ casdep ∪ [Rex];po *)
      let result =
        data
        |> USet.inplace_union ctrl
        |> USet.inplace_union (URelation.compose [ addr; po ])
        |> USet.inplace_union addr
        |> USet.inplace_union casdep
        |> USet.inplace_union (URelation.compose [ rex; po ])
      in

      Landmark.exit landmark;
      result
end

(** RC11 with configurable consume support *)
module RC11Config = struct
  type t = { with_consume : bool }

  let default = { with_consume = false }
  let with_consume = { with_consume = true }
end

module RC11 (Config : sig
  val config : RC11Config.t
end) : MEMORY_MODEL = struct
  (** Cache type *)
  type cache = {
    sb : (int * int) uset;
    hb : (int * int) uset;
    rfi : (int * int) uset;
    rf : (int * int) uset;
    e : int uset;
    events : (int, event) Hashtbl.t;
    rmw : (int * int) uset;
    loc_restrict : (int * int) uset -> (int * int) uset;
  }

  (** Config type *)
  type config = RC11Config.t

  let name = if Config.config.with_consume then "rc11c" else "rc11"
  let default_config = Config.config

  (** RC11 coherence cache builder *)
  let build_cache (execution : symbolic_execution)
      (structure : symbolic_event_structure) (events : (int, event) Hashtbl.t)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    let landmark = Landmark.register "RC11.build_cache" in
      Landmark.enter landmark;

      let ({ e; rf; ex_rmw; _ } : symbolic_execution) = execution in
      let ({ po; _ } : symbolic_event_structure) = structure in
      let _E = e in

      let rf = USet.clone rf in
      let rmw = USet.clone ex_rmw in
      let sb = USet.clone po in

      (* rs = [W];[po ∩ loc]?;[W_rlx⁺];(rf;rmw)⁺? *)
      let rs =
        let w = ModelUtils.match_events events _E Write None None None in
        let w_rlx =
          ModelUtils.match_events events _E Write (Some Relaxed) (Some ">") None
        in
        let inner =
          URelation.transitive_closure (URelation.compose [ rf; rmw ])
        in
          URelation.compose
            [
              w;
              URelation.reflexive_closure _E (loc_restrict sb);
              w_rlx;
              URelation.reflexive_closure _E inner;
            ]
      in

      (* TODO check against spec *)
      (* sw = [R_rel⁺ ∪ W_rel⁺ ∪ F_rel⁺];([F];sb)?;rs;rf;[R_rlx⁺];(sb;[F])?;[R_acq⁺ ∪ W_acq⁺ ∪ F_acq⁺] *)
      let sw =
        let rel =
          USet.union
            (ModelUtils.match_events events _E Read (Some Release) (Some ">")
               None
            )
            (ModelUtils.match_events events _E Write (Some Release) (Some ">")
               None
            )
          |> USet.inplace_union
               (ModelUtils.match_events events _E Fence (Some Release)
                  (Some ">") None
               )
        in
        let fence_sb =
          URelation.reflexive_closure _E
            (URelation.compose
               [ ModelUtils.match_events events _E Fence None None None; sb ]
            )
        in
        let r_rlx =
          ModelUtils.match_events events _E Read (Some Relaxed) (Some ">") None
        in
        let sb_fence =
          URelation.reflexive_closure _E
            (URelation.compose
               [ sb; ModelUtils.match_events events _E Fence None None None ]
            )
        in
        let acq =
          USet.union
            (ModelUtils.match_events events _E Read (Some Acquire) (Some ">")
               None
            )
            (ModelUtils.match_events events _E Write (Some Acquire) (Some ">")
               None
            )
          |> USet.inplace_union
               (ModelUtils.match_events events _E Fence (Some Acquire)
                  (Some ">") None
               )
        in
          URelation.compose [ rel; fence_sb; rs; rf; r_rlx; sb_fence; acq ]
      in

      (* hb = (sw ∪ sb)⁺ *)
      let hb = URelation.transitive_closure (USet.inplace_union sw sb) in

      Landmark.exit landmark;
      { sb; hb; rfi = URelation.inverse rf; rf; e; events; rmw; loc_restrict }

  (** Check coherence *)
  let check_coherence (co : (int * int) uset) (cache : cache) : bool =
    let landmark = Landmark.register "RC11.check_coherence" in
      Landmark.enter landmark;

      let { sb; hb; rfi; rf; e; events; rmw; loc_restrict } = cache in
      let _E = e in

      (* rb = rf⁻¹;co *)
      let rb = URelation.compose [ rfi; co ] in

      (* eco = (rf ∪ co ∪ rb)⁺ *)
      let eco =
        URelation.transitive_closure (USet.union rf co |> USet.inplace_union rb)
      in

      (* Atomicity: rmw ∩ (rb;co) = ∅ *)
      if USet.size rmw <> 0 then
        if USet.size (USet.intersection rmw (URelation.compose [ rb; co ])) <> 0
        then false
        else if
          (* Coherence: hb;eco ∪ hb is irreflexive *)
          not
            (URelation.is_irreflexive
               (USet.inplace_union (URelation.compose [ hb; eco ]) hb)
            )
        then false
        else
          (* SC consistency *)
          let sb_non_loc = USet.set_minus sb (loc_restrict sb) in
          let scb =
            USet.union sb (URelation.compose [ sb_non_loc; hb ])
            |> USet.union (loc_restrict hb)
            |> USet.union co
            |> USet.union rb
          in

          let sc_events =
            ModelUtils.match_events events _E Init (Some SC) None None
          in
          let f_sc =
            ModelUtils.match_events events _E Fence (Some SC) None None
          in

          let psc_base =
            URelation.compose
              [
                USet.inplace_union sc_events
                  (URelation.compose [ f_sc; URelation.reflexive_closure _E hb ]);
                scb;
                USet.inplace_union sc_events
                  (URelation.compose [ URelation.reflexive_closure _E hb; f_sc ]);
              ]
          in

          let psc_f =
            URelation.compose
              [
                f_sc;
                USet.inplace_union (URelation.compose [ hb; eco; hb ]) hb;
                f_sc;
              ]
          in

          let psc = USet.union psc_base psc_f in
            URelation.acyclic psc
      else if
        (* No RMW operations, just check coherence *)
        not
          (URelation.is_irreflexive
             (USet.inplace_union (URelation.compose [ hb; eco ]) hb)
          )
      then false
      else
        let sb_non_loc = USet.set_minus sb (loc_restrict sb) in
        let scb =
          USet.union sb (URelation.compose [ sb_non_loc; hb ])
          |> USet.union (loc_restrict hb)
          |> USet.union co
          |> USet.union rb
        in

        let sc_events =
          ModelUtils.match_events events _E Init (Some SC) None None
        in
        let f_sc =
          ModelUtils.match_events events _E Fence (Some SC) None None
        in

        let psc_base =
          URelation.compose
            [
              USet.inplace_union sc_events
                (URelation.compose [ f_sc; URelation.reflexive_closure _E hb ]);
              scb;
              USet.inplace_union sc_events
                (URelation.compose [ URelation.reflexive_closure _E hb; f_sc ]);
            ]
        in

        let psc_f =
          URelation.compose
            [
              f_sc;
              USet.inplace_union (URelation.compose [ hb; eco; hb ]) hb;
              f_sc;
            ]
        in

        let psc = USet.union psc_base psc_f in
        let acyclic = URelation.acyclic psc in
          Landmark.exit landmark;
          acyclic

  let check_thin_air (execution : symbolic_execution) (cache : cache) =
    URelation.acyclic (USet.union cache.sb execution.rf)

  let compute_dependencies _ _ _ _ _ = USet.create ()
end

module Undefined : MEMORY_MODEL = struct
  (** Cache type *)
  type cache = { rfi : (int * int) uset option; rmw : (int * int) uset option }

  (** Config type *)
  type config = unit

  let name = "undefined"
  let default_config = ()

  (** Build cache *)
  let build_cache (execution : symbolic_execution)
      (structure : symbolic_event_structure) (events : (int, event) Hashtbl.t)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    if USet.size execution.ex_rmw > 0 then
      {
        rfi = Some (URelation.inverse execution.rf);
        rmw = Some execution.ex_rmw;
      }
    else { rfi = None; rmw = None }

  (** Check coherence *)
  let check_coherence (co : (int * int) uset) (cache : cache) : bool =
    match cache with
    | { rfi = Some rfi; rmw = Some rmw } ->
        let fr = URelation.compose [ rfi; co ] in
          USet.size (USet.intersection rmw (URelation.compose [ fr; co ])) = 0
    | _ -> true

  let check_thin_air execution cache = true
  let compute_dependencies _ _ _ _ _ = USet.create ()
end

type restrictions = { coherent : string }

(** First-class module type for dynamic dispatch *)
type model = (module MEMORY_MODEL)

(** Model registry with configs *)
module ModelRegistry = struct
  type model_entry = { name : string; create : unit -> (module MEMORY_MODEL) }

  let models : (string, model_entry) Hashtbl.t = Hashtbl.create 10

  let register name create_fn =
    Hashtbl.add models name { name; create = create_fn }

  let lookup name =
    match Hashtbl.find_opt models name with
    | Some entry -> Some (entry.create ())
    | None -> None

  let () =
    register "imm" (fun () -> (module IMM : MEMORY_MODEL));

    register "rc11" (fun () ->
        let module M = RC11 (struct
          let config = RC11Config.default
        end) in
        (module M : MEMORY_MODEL)
    );

    register "rc11c" (fun () ->
        let module M = RC11 (struct
          let config = RC11Config.with_consume
        end) in
        (module M : MEMORY_MODEL)
    );

    register "undefined" (fun () -> (module Undefined : MEMORY_MODEL));
    register "" (fun () -> (module Undefined : MEMORY_MODEL))
end

(** Build location restrictions *)
let build_location_restriction structure execution eqlocs :
    (int * int) uset -> (int * int) uset =
 fun x -> USet.filter (fun (a, b) -> USet.mem eqlocs (a, b)) x

(** Try all coherence orders *)
let try_all_coherence_orders structure execution cache check_coherence eqlocs =
  let landmark = Landmark.register "try_all_coherence_orders" in
    Landmark.enter landmark;

    if USet.size execution.e = 0 then Lwt.return false
    else
      let ({ po; restrict; _ } : symbolic_event_structure) = structure in
      let writes =
        USet.filter
          (fun ev_id ->
            try
              let event = Hashtbl.find structure.events ev_id in
                event.typ = Write
            with Not_found -> false
          )
          execution.e
      in

      if USet.size writes < 2 then Lwt.return true
      else
        (* Check if reads from init *)
        let reads_from_init =
          USet.exists (fun (_, to_id) -> to_id = 0) execution.rf
        in

        (* Group writes by location *)
        let writes_per_location =
          let groups = ref [] in
            USet.iter
              (fun w ->
                let found = ref false in
                  List.iter
                    (fun group ->
                      if USet.mem eqlocs (List.hd !group, w) then (
                        group := w :: !group;
                        found := true
                      )
                    )
                    !groups;
                  if not !found then
                    groups :=
                      ref (if reads_from_init then [ w; 0 ] else [ w ])
                      :: !groups
              )
              writes;
            List.filter (fun g -> List.length !g > 1) !groups
            (* After grouping writes by location *)
            |> List.map (fun g ->
                let writes_list = !g in

                (* Extract po edges among these writes *)
                let po_edges_in_group =
                  USet.filter
                    (fun (a, b) ->
                      List.mem a writes_list && List.mem b writes_list
                    )
                    po
                in

                (* Helper function to convert permutation to pairs *)
                let rec to_pairs acc = function
                  | [] | [ _ ] -> List.rev acc
                  | x :: (y :: _ as rest) -> to_pairs ((x, y) :: acc) rest
                in

                (* Generate only permutations that respect po *)
                let valid_perms =
                  permutations writes_list
                  |> List.filter (fun perm ->
                      (* Check: for each (w1,w2) in po, w1 comes before w2 in perm *)
                      USet.for_all
                        (fun (w1, w2) ->
                          (* Find positions of w1 and w2 in permutation *)
                          let rec find_index x lst idx =
                            match lst with
                            | [] -> None
                            | h :: t ->
                                if h = x then Some idx
                                else find_index x t (idx + 1)
                          in
                          let idx1 = find_index w1 perm 0 in
                          let idx2 = find_index w2 perm 0 in
                            match (idx1, idx2) with
                            | Some i1, Some i2 -> i1 < i2
                            | _ -> true
                        )
                        po_edges_in_group
                  )
                in

                (* Convert each valid permutation to pairs *)
                List.map (fun perm -> to_pairs [] perm) valid_perms
            )
        in

        let rec choose_one i vals =
          if i < 0 then
            let co = URelation.transitive_closure (USet.of_list vals) in
              Lwt.return (check_coherence co cache)
          else
            let rec try_perms = function
              | [] -> Lwt.return false
              | p :: ps ->
                  let%lwt result = choose_one (i - 1) (vals @ p) in
                    if result then Lwt.return true else try_perms ps
            in
              try_perms (List.nth writes_per_location i)
        in

        let result = choose_one (List.length writes_per_location - 1) [] in
          Landmark.exit landmark;
          result

(** {1 Coherence Checking Entry Point} *)

let check_for_coherence structure execution restrictions =
  let landmark = Landmark.register "check_for_coherence" in
    Landmark.enter landmark;

    let events = structure.events in
      if USet.size execution.e = 0 then Lwt.return false
      else
        match ModelRegistry.lookup restrictions.coherent with
        | None ->
            Logs.warn (fun m -> m "Unknown model: %s" restrictions.coherent);
            Landmark.exit landmark;
            Lwt.return false
        | Some model ->
            let module M = (val model : MEMORY_MODEL) in
            (* Create location equivalence relation using semantic equality *)
            let%lwt eqlocs =
              let all_events = execution.e in
                USet.async_filter
                  (fun (a, b) ->
                    if a = b then Lwt.return true
                    else
                      try
                        let ev_a = Hashtbl.find structure.events a in
                        let ev_b = Hashtbl.find structure.events b in
                          match (ev_a.loc, ev_b.loc) with
                          | Some loc_a, Some loc_b ->
                              (* Use solver to check semantic equality *)
                              Solver.Semeq.exeq
                                (Solver.Semeq.create_state ())
                                loc_a loc_b
                          | _ -> Lwt.return false
                      with Not_found -> Lwt.return false
                  )
                  (URelation.cross all_events all_events
                  |> USet.filter (fun (a, b) -> a <= b)
                  )
            in
            let eqlocs = USet.inplace_union eqlocs (URelation.inverse eqlocs) in

            (* Build location restriction once *)
            let loc_restrict =
              build_location_restriction structure execution eqlocs
            in

            (* Build cache *)
            let cache = M.build_cache execution structure events loc_restrict in

            (* Check thin-air *)
            if not (M.check_thin_air execution cache) then (
              Landmark.exit landmark;
              Lwt.return false
            )
            else
              (* Try all coherence orders *)
              let result =
                try_all_coherence_orders structure execution cache
                  M.check_coherence eqlocs
              in
                Landmark.exit landmark;
                result
