(** Coherence checking for memory models *)

open Algorithms
open Expr
open Solver
open Types
open Uset

(** S4 (measure the waste ratio): when enabled, emit pipeline-stage and
    per-location coherence-permutation counts at info level. Harmless
    instrumentation, off by default; enabled via the [MORDOR_S4_COUNTERS]
    environment variable or by setting this ref. Shared by {!Executions}. *)
let s4_counters = ref (Option.is_some (Sys.getenv_opt "MORDOR_S4_COUNTERS"))

(** {1 Core Abstractions} *)

module type MEMORY_MODEL = sig
  type cache
  type config

  val name : string
  val default_config : config

  val build_cache :
    symbolic_execution ->
    symbolic_event_structure ->
    ((int * int) uset -> (int * int) uset) ->
    cache

  val check_coherence : cache -> (int * int) uset -> bool
  val check_thin_air : cache -> symbolic_execution -> bool

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
  (** C11/RC11/IMM access-mode lattice ordering.

      [mode_at_least m threshold] holds when access mode [m] is at least as
      strong as [threshold] in the partial order

      {[
      na, normal < rlx < con < acq, rel < acq_rel < sc
      ]}

      where [acq] and [rel] are mutually incomparable. This is what the [">"]
      operator passed to {!match_events} is meant to express (e.g. "release or
      stronger"); previously that operator was ignored and matching fell back to
      exact equality, so [sc]/[acq_rel] accesses were silently excluded from the
      release/acquire sets, under-approximating synchronization. *)
  let mode_at_least (m : mode) (threshold : mode) : bool =
    match threshold with
    | Nonatomic | Normal -> true
    | Relaxed -> (
        match m with
        | Relaxed | Consume | Acquire | Release | ReleaseAcquire | SC -> true
        | Nonatomic | Normal | Strong -> false
      )
    | Consume -> (
        match m with
        | Consume | Acquire | ReleaseAcquire | SC -> true
        | _ -> false
      )
    | Acquire -> (
        match m with
        | Acquire | ReleaseAcquire | SC -> true
        | _ -> false
      )
    | Release -> (
        match m with
        | Release | ReleaseAcquire | SC -> true
        | _ -> false
      )
    | ReleaseAcquire -> (
        match m with
        | ReleaseAcquire | SC -> true
        | _ -> false
      )
    | SC -> m = SC
    | Strong -> m = Strong

  (** Event matching - shared across all models *)
  let match_events (events : (int, event) Hashtbl.t) (e : int uset)
      (typ : event_type) (mode_opt : mode option) (op_opt : string option)
      (second_mode_opt : mode option) : (int * int) uset =
    let result = USet.create () in
      USet.iter
        (fun ev_id ->
          try
            let event = Hashtbl.find events ev_id in
            let type_match = event.typ = typ in
            let mode_match =
              match mode_opt with
              | None -> true
              | Some m -> (
                  (* [op_opt = Some ">"] means "[m] or stronger" per the access
                     mode lattice; anything else means exact mode equality.

                     Only the mode field of the event's own type is asked. The
                     test used to be OR-ed across all three, on the argument
                     that the fields a type does not use default to [Relaxed]
                     and so cannot over-match a threshold above it. RC11 asks
                     for thresholds at [Relaxed] -- the [W]s of [rs] and the [R]
                     of [sw] -- and there the defaults matched every read and
                     write, so a nonatomic store synchronised as if it were
                     relaxed. *)
                  let cmp ev_mode =
                    match op_opt with
                    | Some ">" -> mode_at_least ev_mode m
                    | _ -> ev_mode = m
                  in
                    match event.typ with
                    | Read -> cmp event.rmod
                    | Write -> cmp event.wmod
                    | Fence -> cmp event.fmod
                    | _ -> false
                )
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
        result

  (** Thread-local restriction *)
  let thread_internal po x = USet.intersection x po

  let thread_external po x = USet.set_minus x po

  (** Common relation builders *)
  (* let build_release_sequence events e po rf rmw loc_restrict = ... *)

  (* let build_synchronizes_with events e po rf release loc_restrict = ... *)
end

(** Coherence checks module *)
module CoherenceChecks = struct
  (** Atomicity check: rmw ∩ (rb;co) = ∅, for rb = rf⁻¹;co *)
  let rmw_atomicity ~rf ~rfi ~rmw ~co () =
    (* compose twice with co to establish the intermediate write witnessing the violation *)
    URelation.compose [ rfi; co; co ] |> USet.intersection rmw |> USet.is_empty

  let thin_air_check ~hb ~rf () = URelation.acyclic (USet.union hb rf)

  (** Coherence axiom check: hb;eco ∪ hb is irreflexive.

      The [∪ hb] term is the reflexive part of RC11's irreflexive(hb;eco?), and
      it is what asks whether hb is irreflexive at all -- for a transitively
      closed hb, whether the relation it closes is acyclic. It was missing from
      the composition below while both comments named it. *)
  let coherence_axiom ?eco ~rf ~rfi ~co ~hb () =
    let rb = URelation.compose [ rfi; co ] in
    (* eco = (rf ∪ co ∪ rb)⁺ *)
    let eco =
      if Option.is_some eco then Option.get eco
      else USet.union rf co |> USet.union rb |> URelation.transitive_closure
    in
      (* Coherence: hb;eco ∪ hb is irreflexive *)
      URelation.is_irreflexive
        (USet.inplace_union ~into:(URelation.compose [ hb; eco ]) hb)
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
      (structure : symbolic_event_structure)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    let ({ e; rf; rmw; _ } : symbolic_execution) = execution in
    let ({ events; po; restrict; _ } : symbolic_event_structure) = structure in

    let rf = USet.clone rf in
    let po = USet.clone po in
    let rmw = USet.clone rmw in

    let thread_internal_restriction x = USet.intersection x po in
    let thread_external_restriction x = USet.set_minus x po in

    let w = ModelUtils.match_events events e Write None None None in

    (* rs = [W];(po ∩ loc);[W] ∪ [W];([po ∩ loc]?;rf;rmw)⁺? *)
    let rs =
      let part1 = URelation.compose [ w; loc_restrict po; w ] in
      let inner =
        URelation.compose
          [ URelation.reflexive_closure e (loc_restrict po); rf; rmw ]
      in
      let part2 =
        URelation.compose
          [
            w; URelation.reflexive_closure e (URelation.transitive_closure inner);
          ]
      in
        USet.inplace_union ~into:part1 part2
    in

    (* release = ([W_rel] ∪ [F_rel];po);rs *)
    let release =
      let w_rel =
        ModelUtils.match_events events e Write (Some Release) None None
      in
      let f_rel_po =
        URelation.compose
          [
            ModelUtils.match_events events e Fence (Some Release) (Some ">")
              None;
            po;
          ]
      in
        URelation.compose [ USet.inplace_union ~into:w_rel f_rel_po; rs ]
    in

    (* sw = release;(rf ∩ ¬po ∪ [po ∩ loc]?;(rf \ po));([R_acq] ∪ po;[F_acq]) *)
    let sw =
      let rfi = thread_internal_restriction rf in
      let rfe = thread_external_restriction rf in
      let middle =
        URelation.compose
          [ URelation.reflexive_closure e (loc_restrict po); rfe ]
        |> USet.union rfi
      in
      let r_acq =
        ModelUtils.match_events events e Read (Some Acquire) None None
      in
      let po_f_acq =
        URelation.compose
          [
            po;
            ModelUtils.match_events events e Fence (Some Acquire) (Some ">")
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
            po; ModelUtils.match_events events e Write (Some Release) None None;
          ]
      in
      let p2 =
        URelation.compose
          [ ModelUtils.match_events events e Read (Some Acquire) None None; po ]
      in
      let p3 =
        URelation.compose
          [ po; ModelUtils.match_events events e Fence None None None ]
      in
      let p4 =
        URelation.compose
          [ ModelUtils.match_events events e Fence None None None; po ]
      in
      let p5 =
        URelation.compose
          [
            ModelUtils.match_events events e Write (Some Release) None None;
            loc_restrict po;
            ModelUtils.match_events events e Write None None None;
          ]
      in
        let acc = USet.union p1 p2 in
        let acc = USet.inplace_union ~into:acc p3 in
        let acc = USet.inplace_union ~into:acc p4 in
          USet.inplace_union ~into:acc p5
    in

    let deps = execution.dp in

    (* ppo = [R];(rf ∩ ¬po ∪ deps)⁺;[W] *)
    let ppo =
      let r = ModelUtils.match_events events e Read None None None in
      let w = ModelUtils.match_events events e Write None None None in
      let middle =
        URelation.transitive_closure
          (USet.inplace_union ~into:(thread_internal_restriction rf) deps)
      in
        URelation.compose [ r; middle; w ]
    in

    (* strong_ = [W_strong];po;[W] *)
    let strong_ =
      URelation.compose
        [
          ModelUtils.match_events events e Write None None (Some Strong);
          po;
          ModelUtils.match_events events e Write None None None;
        ]
    in

    (* ar_ = (rf \ po) ∪ bob ∪ ppo ∪ strong_

       Accumulator-first for the same reason as [eco] below: the pipeline form
       folds into [bob], [ppo] and [strong_] instead. *)
    let ar_ =
      let acc = thread_external_restriction rf in
      let acc = USet.inplace_union ~into:acc bob in
      let acc = USet.inplace_union ~into:acc ppo in
        USet.inplace_union ~into:acc strong_
    in

    (* psc_a = [F_sc];hb *)
    let psc_a =
      URelation.compose
        [ ModelUtils.match_events events e Fence (Some SC) None None; hb ]
    in

    (* psc_b = hb;[F_sc] *)
    let psc_b =
      URelation.compose
        [ hb; ModelUtils.match_events events e Fence (Some SC) None None ]
    in

    { hb; rf; rfi = URelation.inverse rf; ar_; po; psc_a; psc_b; rmw }

  (** IMM coherence checker *)
  let check_coherence (cache : cache) (co : (int * int) uset) : bool =
    let { hb; rfi; po; rf; ar_; psc_a; psc_b; rmw; _ } = cache in

    let result =
      let ( let*? ) (condition, msg) f = if condition then f () else false in

      let thread_external_restriction x = USet.set_minus x po in

      let dummy_adj_map = Hashtbl.create 0 in

      let co_adj_map = URelation.adjacency_map co in
      let rf_adj_map = URelation.adjacency_map rf in

      (* fr = rf⁻¹;co *)
      let fr = URelation.compose [ rfi; co ] in
      let fre = thread_external_restriction fr in

      (* eco = rf ∪ co;rf ∪ co ∪ fr;rf ∪ fr

         Written as a pipeline against the old unlabelled [inplace_union],
         this folded eco into [rf] and then into [co] rather than into the
         accumulator.  [rf] is a cache field shared by every candidate coherence
         order, so the first candidate checked left it holding eco and every
         later candidate was checked against a corrupted [rf]; and [co] itself
         came out of the line holding eco, which is what [coe] and [detour]
         below then read.  The search's answer depended on the order candidates
         were tried in, which for an exhaustive search it cannot.

         [~into] now names the mutated set at every call, and the pipeline form
         that caused this does not typecheck (github #88). *)
      let eco =
        let acc = URelation.compose [ co; rf ] in
        let acc = USet.inplace_union ~into:acc rf in
        let acc = USet.inplace_union ~into:acc co in
        let acc = USet.inplace_union ~into:acc (URelation.compose [ fr; rf ]) in
          USet.inplace_union ~into:acc fr
      in

      let eco_adj_map = URelation.adjacency_map eco in
      let hb_adj_map = URelation.adjacency_map hb in

      (* Coherence: hb;eco ∪ hb is irreflexive *)
      let hb_eco_hb =
        USet.inplace_union
          ~into:
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
              (psc_a, dummy_adj_map); (eco, eco_adj_map); (psc_b, psc_b_adj_map);
            ]
        in
        let ar = USet.inplace_union ~into:(USet.union ar_ psc) detour in

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
      result

  let check_thin_air _ _ = true

  (** IMM dependency calculation *)
  let compute_dependencies (execution : symbolic_execution)
      (events : (int, event) Hashtbl.t) (po : (int * int) uset) (e : int uset)
      (restrict : (int, expr list) Hashtbl.t) : (int * int) uset =
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
      let acc = USet.inplace_union ~into:data ctrl in
      let acc = USet.inplace_union ~into:acc (URelation.compose [ addr; po ]) in
      let acc = USet.inplace_union ~into:acc addr in
      let acc = USet.inplace_union ~into:acc casdep in
        USet.inplace_union ~into:acc (URelation.compose [ rex; po ])
    in

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
      (structure : symbolic_event_structure)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    let ({ e; rf; rmw; _ } : symbolic_execution) = execution in
    let ({ po; events; _ } : symbolic_event_structure) = structure in

    let rf = USet.clone rf in
    let rmw = USet.clone rmw in
    let sb = USet.clone po in

    (* rs = [W];[po ∩ loc]?;[W_rlx⁺];(rf;rmw)⁺? *)
    let rs =
      let w = ModelUtils.match_events events e Write None None None in
      let w_rlx =
        ModelUtils.match_events events e Write (Some Relaxed) (Some ">") None
      in
      let inner =
        URelation.transitive_closure (URelation.compose [ rf; rmw ])
      in
        URelation.compose
          [
            w;
            URelation.reflexive_closure e (loc_restrict sb);
            w_rlx;
            URelation.reflexive_closure e inner;
          ]
    in

    (* TODO check against spec *)
    (* sw = [R_rel⁺ ∪ W_rel⁺ ∪ F_rel⁺];([F];sb)?;rs;rf;[R_rlx⁺];(sb;[F])?;[R_acq⁺ ∪ W_acq⁺ ∪ F_acq⁺] *)
    let sw =
      let rel =
        USet.union
          (ModelUtils.match_events events e Read (Some Release) (Some ">") None)
          (ModelUtils.match_events events e Write (Some Release) (Some ">") None)
        |> fun acc ->
        USet.inplace_union ~into:acc
          (ModelUtils.match_events events e Fence (Some Release) (Some ">") None)
      in
      let fence_sb =
        URelation.reflexive_closure e
          (URelation.compose
             [ ModelUtils.match_events events e Fence None None None; sb ]
          )
      in
      let r_rlx =
        ModelUtils.match_events events e Read (Some Relaxed) (Some ">") None
      in
      let sb_fence =
        URelation.reflexive_closure e
          (URelation.compose
             [ sb; ModelUtils.match_events events e Fence None None None ]
          )
      in
      let acq =
        USet.union
          (ModelUtils.match_events events e Read (Some Acquire) (Some ">") None)
          (ModelUtils.match_events events e Write (Some Acquire) (Some ">") None)
        |> fun acc ->
        USet.inplace_union ~into:acc
          (ModelUtils.match_events events e Fence (Some Acquire) (Some ">") None)
      in
        URelation.compose [ rel; fence_sb; rs; rf; r_rlx; sb_fence; acq ]
    in

    (* hb = (sw ∪ sb)⁺ *)
    let hb = URelation.transitive_closure (USet.inplace_union ~into:sw sb) in

    { sb; hb; rfi = URelation.inverse rf; rf; e; events; rmw; loc_restrict }

  (** Check coherence *)
  let check_coherence (cache : cache) (co : (int * int) uset) : bool =
    let { sb; hb; rfi; rf; e; events; rmw; loc_restrict } = cache in

    (* rb = rf⁻¹;co *)
    let rb = URelation.compose [ rfi; co ] in

    (* eco = (rf ∪ co ∪ rb)⁺ *)
    let eco =
      URelation.transitive_closure (USet.inplace_union ~into:(USet.union rf co) rb)
    in

    (* SC consistency: psc is acyclic.

       Behind a closure so that only an execution which has already passed
       atomicity and coherence pays for it, as was the case when each arm of
       the RMW split below carried its own copy of this. *)
    let sc_consistent () =
      let sb_non_loc = USet.set_minus sb (loc_restrict sb) in
      let scb =
        USet.union sb (URelation.compose [ sb_non_loc; hb ])
        |> USet.union (loc_restrict hb)
        |> USet.union co
        |> USet.union rb
      in

      let sc_events =
        ModelUtils.match_events events e Init (Some SC) None None
      in
      let f_sc = ModelUtils.match_events events e Fence (Some SC) None None in

      (* psc_base = [E_sc U (F_sc;hb?)] ; scb ; [E_sc U (hb?;F_sc)]

         Both unions have to copy. [USet.inplace_union] mutates [~into], so
         building these two with it left sc_events holding
         E_sc U (F_sc;hb?) U (hb?;F_sc) and both ends of the composition
         pointing at that one set -- each end carrying the other's term. Which
         of the two got there first was not even determined: OCaml does not
         specify the evaluation order of list elements. *)
      let psc_base =
        URelation.compose
          [
            USet.union sc_events
              (URelation.compose [ f_sc; URelation.reflexive_closure e hb ]);
            scb;
            USet.union sc_events
              (URelation.compose [ URelation.reflexive_closure e hb; f_sc ]);
          ]
      in

      let psc_f =
        URelation.compose
          [
            f_sc;
            USet.inplace_union ~into:(URelation.compose [ hb; eco; hb ]) hb;
            f_sc;
          ]
      in

      let psc = USet.union psc_base psc_f in
        URelation.acyclic psc
    in

    (* Atomicity: rmw ∩ (rb;co) = ∅. Vacuous with no RMWs to violate it. *)
    (USet.size rmw = 0 || CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co ())
    (* Coherence: hb;eco ∪ hb is irreflexive.

       This used to sit inside the RMW arm, and the arm without RMWs spelled it
       out inline in a different form. The two were not the same check: the
       shared one omitted the [∪ hb] term, so an execution containing an RMW
       was never asked whether hb was irreflexive -- for hb = (sw ∪ sb)⁺,
       whether sb ∪ sw is acyclic. One check now, outside the split.

       The rest of this function did not depend on rmw either: both arms ran
       the same thirty-five lines of SC consistency, which is how they came to
       disagree in the first place. *)
    && CoherenceChecks.coherence_axiom ~eco ~rf ~rfi ~co ~hb ()
    && sc_consistent ()

  let check_thin_air (cache : cache) (execution : symbolic_execution) =
    let { hb; rf; _ } = cache in
      CoherenceChecks.thin_air_check ~hb ~rf ()

  let compute_dependencies _ _ _ _ _ = USet.create ()
end

module SMRD : MEMORY_MODEL = struct
  type cache = {
    rf : (int * int) uset;
    rfi : (int * int) uset;
    hb : (int * int) uset;
    rmw : (int * int) uset;
  }

  type config = unit

  let name = "smrd"
  let default_config = ()

  let build_cache (execution : symbolic_execution)
      (structure : symbolic_event_structure) loc_restrict =
    let po = USet.clone structure.po in
    let rf = USet.clone execution.rf in
    let rfi = URelation.inverse rf in
    let rmw = USet.clone execution.rmw in
    let dp = USet.clone execution.dp in
    let ppo = USet.clone execution.ppo in

    (* sw = [W_rel];rf;[R_acq]

       Synchronizes-with. Without it [hb] carries no cross-thread edge at all,
       so a release/acquire pair is invisible to the coherence axiom and MP over
       release/acquire comes out allowed. The two po legs of the message-passing
       shape are already in [ppo]: [Forwarding.compute_ppo_sync] orders every
       event into a release write and out of an acquire read, so composing this
       relation with [ppo] under the closure below yields the ordering from the
       release write's po-predecessors to the acquire read's po-successors.

       [rf] is deliberately *not* unioned in wholesale: that would order relaxed
       accesses too, which sMRD does not. Only the release-to-acquire edges join
       [hb]. Fences are not covered here -- a relaxed write po-after a release
       fence does not yet synchronize (see issue #63). *)
    let sw =
      let events = structure.events in
      let e = execution.e in
      let w_rel =
        ModelUtils.match_events events e Write (Some Release) (Some ">") None
      in
      let r_acq =
        ModelUtils.match_events events e Read (Some Acquire) (Some ">") None
      in
        URelation.compose [ w_rel; rf; r_acq ]
    in

    (* hb = (ppo ∪ dp ∪ sw)⁺ *)
    let hb =
      USet.inplace_union ~into:(USet.union ppo dp) sw |> URelation.transitive_closure
    in

    { rf; rfi; hb; rmw }

  let check_coherence cache co =
    let { rf; rfi; hb; rmw; _ } = cache in
    let result =
      CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co ()
      && CoherenceChecks.coherence_axiom ~rf ~rfi ~co ~hb ()
    in
      result

  let check_thin_air cache execution =
    let { rf; hb; _ } = cache in
    let result = CoherenceChecks.thin_air_check ~hb ~rf () in
      result

  let compute_dependencies _ _ _ _ _ = USet.create ()
end

module Undefined : MEMORY_MODEL = struct
  (** Cache type *)
  type cache = {
    rf : (int * int) uset;
    rfi : (int * int) uset;
    rmw : (int * int) uset;
  }

  (** Config type *)
  type config = unit

  let name = "undefined"
  let default_config = ()

  (** Build cache *)
  let build_cache (execution : symbolic_execution)
      (structure : symbolic_event_structure)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    let { rf; rmw; _ } : symbolic_execution = execution in
      { rf; rfi = URelation.inverse rf; rmw }

  (** Check coherence *)
  let check_coherence (cache : cache) (co : (int * int) uset) : bool =
    let { rf; rfi; rmw; _ } = cache in
      CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co ()

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

    register "smrd" (fun () -> (module SMRD : MEMORY_MODEL));

    register "undefined" (fun () -> (module Undefined : MEMORY_MODEL));
    register "" (fun () -> (module Undefined : MEMORY_MODEL))
end

(** Build location restrictions *)
let build_location_restriction structure execution eqlocs :
    (int * int) uset -> (int * int) uset =
 fun x -> USet.filter (fun (a, b) -> USet.mem eqlocs (a, b)) x

(** [try_all_coherence_orders ...] is the coherence order that admits
    [execution], or [None] if none does.

    It used to answer [bool] and throw the order away with the search, so
    nothing downstream could say what an execution had been admitted under
    (github #66). The order returned is the canonically least admitting one:
    each location's po-respecting permutations are enumerated in sorted order
    and the first accepted combination wins, so the answer is a function of the
    execution and the model rather than of the traversal. *)
let try_all_coherence_orders cache structure execution check_coherence eqlocs =
  if USet.size execution.e = 0 then None
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

    if USet.size writes < 2 then
      (* 0 or 1 writes: the only possible coherence order is empty (co only
         orders two writes to the same location), but we must still run the
         model's coherence / thin-air axioms. Returning [true] unconditionally
         was unsound — e.g. a read reading from a write that happens-after it is
         a coherence violation even with co = ∅. *)
      let empty = USet.create () in
        if check_coherence cache empty then Some empty else None
    else
      (* Check if reads from init *)
      let reads_from_init = USet.exists (fun (_, w) -> w = 0) execution.rf in

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
                    ref (if reads_from_init then [ w; 0 ] else [ w ]) :: !groups
            )
            writes;
          List.filter (fun g -> List.length !g > 1) !groups
          (* After grouping writes by location *)
          |> List.map (fun g ->
              (* The init write (event 0) is always the co-minimal write to its
                 location. Never permute it into a non-minimal position — that
                 would yield bogus coherence orders in which a real write is
                 co-before init. Permute only the real writes, then prepend
                 init. *)
              let group = !g in
              let has_init = List.mem 0 group in
              let writes_list = List.filter (fun w -> w <> 0) group in

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

              (* S4: per-location write-set size and the number of po-respecting
                 permutations it expands into (the coherence permutation-blowup
                 that S6/R9b target). *)
              if !s4_counters then
                Logs_safe.info (fun m ->
                    m "[S4] coherence-location: writes=%d perms=%d"
                      (List.length group) (List.length valid_perms)
                );

              (* Convert each valid permutation to pairs, keeping init
                 co-minimal by prepending it before the real writes. *)
              (* Sorted, so that the first accepted combination below is the
                 canonically least one rather than whichever [permutations]
                 happened to yield first. That is what makes the exported order
                 a function of the execution and the model. *)
              (* Sorted, so the first accepted combination below is the
                 canonically least one rather than whichever [permutations]
                 happened to yield first. That is what makes the order this
                 function returns a function of the execution and the model. *)
              List.map
                (fun perm -> to_pairs [] (if has_init then 0 :: perm else perm))
                valid_perms
              |> List.sort compare
          )
      in

      let rec choose_one i vals =
        if i < 0 then (
          let co = URelation.transitive_closure (USet.of_list vals) in
            if check_coherence cache co then (
              Logs_safe.debug (fun m ->
                  m "Coherence: execution %d admitted under co = {%s}"
                    execution.id
                    (USet.values co
                    |> List.sort compare
                    |> List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                    |> String.concat "; "
                    )
              );
              Some co
            )
            else None
        )
        else
          let rec try_perms = function
            | [] -> None
            | p :: ps -> (
                match choose_one (i - 1) (vals @ p) with
                | Some co -> Some co
                | None -> try_perms ps
              )
          in
            try_perms (List.nth writes_per_location i)
      in
        choose_one (List.length writes_per_location - 1) []

(** {1 Coherence Checking Entry Point} *)

(** [check_for_coherence structure execution restrictions] is the coherence
    order under which the model admits [execution], or [None] if it does not.

    The witnessing order comes back with the answer rather than being discarded
    with the search; see {!try_all_coherence_orders} (github #66). *)
let check_for_coherence structure execution restrictions =
  if USet.size execution.e = 0 then None
  else
    match ModelRegistry.lookup restrictions.coherent with
    | None ->
        Logs_safe.warn (fun m -> m "Unknown model: %s" restrictions.coherent);
        None
    | Some model ->
        let module M = (val model : MEMORY_MODEL) in
        (* Create location equivalence relation using semantic equality *)
        let eqlocs =
          let all_events = execution.e in
            USet.filter
              (fun (a, b) ->
                if a = b then true
                else
                  try
                    let ev_a = Hashtbl.find structure.events a in
                    let ev_b = Hashtbl.find structure.events b in
                      match (ev_a.loc, ev_b.loc) with
                      | Some loc_a, Some loc_b ->
                          (* Use solver to check semantic equality *)
                          exeq loc_a loc_b
                      | _ -> false
                  with Not_found -> false
              )
              (URelation.cross all_events all_events
              |> USet.filter (fun (a, b) -> a <= b)
              )
        in
        let eqlocs = USet.inplace_union ~into:eqlocs (URelation.inverse eqlocs) in

        (* Build location restriction once *)
        let loc_restrict =
          build_location_restriction structure execution eqlocs
        in

        (* Build cache *)
        let cache = M.build_cache execution structure loc_restrict in

        (* Check thin-air *)
        if not (M.check_thin_air cache execution) then None
        else
          (* Try all coherence orders *)
          try_all_coherence_orders cache structure execution M.check_coherence
            eqlocs
