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

  (** One candidate coherence order, with the cache it is checked against and
      the relations the axioms derive from the two. Each is computed once, and
      only if an axiom asks for it. *)
  type candidate

  val candidate : cache -> (int * int) uset -> candidate

  (** The model's axioms, by name, in the order {!check_coherence} asks them:
      [check_coherence cache co] holds when every one holds of
      [candidate cache co]. Each can be asked on its own. *)
  val axioms : (string * (candidate -> bool)) list

  val check_thin_air : cache -> symbolic_execution -> bool

  val uses_co : bool
  (** Whether [check_coherence] reads the coherence order it is given. A model
      whose axioms quantify over orders of their own -- a view per process, an
      arbitration per session -- does not, and the search then asks it once
      rather than once per candidate order. *)

  val orders_allocations : bool
  (** Whether allocations and deallocations are writes to the coherence order,
      as RC11z makes them. *)

  val check_program : symbolic_event_structure -> (unit, string) result
  (** [Error reason] when the model cannot answer for this program at all. It
      is asked once, before any execution is, and the pipeline fails with the
      reason rather than returning a verdict that is not the model's. *)

  val compute_dependencies :
    symbolic_execution ->
    (int, event) Hashtbl.t ->
    (int * int) uset ->
    int uset ->
    (int, expr list) Hashtbl.t ->
    (int * int) uset
end

(** A model that can be asked about a coherence order while it is being built.

    [start] is what is known before any edge; [extend] adds edges and answers
    [None] once no completion can be coherent, so that a search can stop there;
    [finalize] decides the complete order. {!Incremental} is the adapter every
    model has until it says more: it never prunes, and decides at the end with
    [check_coherence]. *)
module type INCREMENTAL_MODEL = sig
  include MEMORY_MODEL

  type partial

  val start : cache -> partial
  val extend : partial -> (int * int) uset -> partial option
  val finalize : partial -> (int * int) uset -> bool
end

(** The default adapter: nothing is known of a partial order but the cache. *)
module Incremental (M : MEMORY_MODEL) :
  INCREMENTAL_MODEL with type cache = M.cache and type partial = M.cache =
struct
  include M

  type partial = cache

  let start cache = cache
  let extend partial _ = Some partial
  let finalize partial co = M.check_coherence partial co
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

  (** [same_thread thread_index a b]: [a] and [b] are events of one thread.
      Events outside every thread -- the initial event, terminals -- are in
      none, so every pair involving one is external. *)
  let same_thread thread_index a b =
    match
      (Hashtbl.find_opt thread_index a, Hashtbl.find_opt thread_index b)
    with
    | Some ta, Some tb -> ta = tb
    | _ -> false

  (** [int] and [ext] of a relation by thread identity, where
      {!thread_internal} and {!thread_external} approximate them by [po]. *)
  let thread_internal_of thread_index x =
    USet.filter (fun (a, b) -> same_thread thread_index a b) x

  let thread_external_of thread_index x =
    USet.filter (fun (a, b) -> not (same_thread thread_index a b)) x

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

(** [holds axioms c] is whether every one of [axioms] holds of [c], asked in
    order and no further than the first that does not. *)
let holds axioms c = List.for_all (fun (_, axiom) -> axiom c) axioms

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

  type candidate = {
    cache : cache;
    fr : (int * int) uset Lazy.t;  (** [rf⁻¹;co] *)
    eco : (int * int) uset Lazy.t;  (** [rf ∪ co;rf ∪ co ∪ fr;rf ∪ fr] *)
    eco_adj_map : (int, int uset) Hashtbl.t Lazy.t;
    coe : (int * int) uset Lazy.t;  (** [co] less [po] *)
  }

  let candidate (cache : cache) co =
    let fr = lazy (URelation.compose [ cache.rfi; co ]) in
    (* Written as a pipeline against the old unlabelled [inplace_union], this
       folded eco into [rf] and then into [co] rather than into the
       accumulator. [rf] is a cache field shared by every candidate coherence
       order, so the first candidate checked left it holding eco and every
       later candidate was checked against a corrupted [rf]; and [co] itself
       came out of the line holding eco, which is what [coe] and [detour] then
       read. The search's answer depended on the order candidates were tried
       in, which for an exhaustive search it cannot.

       [~into] now names the mutated set at every call, and the pipeline form
       that caused this does not typecheck (github #88). *)
    let eco =
      lazy
        (let fr = Lazy.force fr in
         let acc = URelation.compose [ co; cache.rf ] in
         let acc = USet.inplace_union ~into:acc cache.rf in
         let acc = USet.inplace_union ~into:acc co in
         let acc =
           USet.inplace_union ~into:acc (URelation.compose [ fr; cache.rf ])
         in
           USet.inplace_union ~into:acc fr
        )
    in
      {
        cache;
        fr;
        eco;
        eco_adj_map = lazy (URelation.adjacency_map (Lazy.force eco));
        coe = lazy (USet.set_minus co cache.po);
      }

  (* The first relation of a [compose_adj_map] is not looked up by its
     adjacency map. *)
  let dummy_adj_map = Hashtbl.create 0

  (** Coherence: [hb;eco ∪ hb] is irreflexive. *)
  let coherence x =
    let { hb; _ } = x.cache in
    let eco = Lazy.force x.eco in
      USet.inplace_union
        ~into:
          (URelation.compose_adj_map
             [
               (hb, URelation.adjacency_map hb); (eco, Lazy.force x.eco_adj_map);
             ]
          )
        hb
      |> URelation.is_irreflexive

  (** No thin air: [ar = ar_ ∪ psc ∪ detour] is acyclic. *)
  let ar_acyclic x =
    let { rf; po; ar_; psc_a; psc_b; _ } = x.cache in
    let eco = Lazy.force x.eco and coe = Lazy.force x.coe in
    let rfe = USet.set_minus rf po in
    let detour =
      URelation.compose_adj_map
        [
          (coe, URelation.adjacency_map coe); (rfe, URelation.adjacency_map rfe);
        ]
      |> USet.intersection po
    in
    let psc =
      URelation.compose_adj_map
        [
          (psc_a, dummy_adj_map);
          (eco, Lazy.force x.eco_adj_map);
          (psc_b, URelation.adjacency_map psc_b);
        ]
    in
      URelation.acyclic (USet.inplace_union ~into:(USet.union ar_ psc) detour)

  (** Atomicity: [rmw ∩ (fre;coe) = ∅]. Vacuous with no RMWs to violate it. *)
  let atomicity x =
    let { rmw; po; _ } = x.cache in
      USet.size rmw = 0
      ||
      let fre = USet.set_minus (Lazy.force x.fr) po
      and coe = Lazy.force x.coe in
        URelation.compose_adj_map
          [ (fre, dummy_adj_map); (coe, URelation.adjacency_map coe) ]
        |> USet.intersection rmw
        |> USet.size
        = 0

  let axioms =
    [
      ("hb;eco ∪ hb is irreflexive", coherence);
      ("ar is acyclic", ar_acyclic);
      ("rmw ∩ (fre;coe) = ∅", atomicity);
    ]

  let check_coherence cache co = holds axioms (candidate cache co)

  let check_thin_air _ _ = true
  let uses_co = true
  let orders_allocations = false
  let check_program _ = Ok ()

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

(** RC11 and the models that are configurations of it. *)
module RC11Config = struct
  (** Which release sequence [rs] a model synchronises over.

      - [Rc11]: [\[W\];(sb ∩ loc)?;\[W_rlx⁺\];(rf;rmw)*], as herd's [rc11.cat].
      - [Rc17]: [\[W_rlx⁺\];(rf;rmw)*], C++17's, where a later same-thread
        relaxed store no longer continues the sequence ([rc17.cat]).
      - [Cpp11]: RC11's, less the pairs another thread's write intervenes in,
        [rs \ (coe;coe)] ([cpp11.cat]). It depends on the coherence order, so
        [hb] is built per candidate order rather than once per execution. *)
  type release_sequence = Rc11 | Rc17 | Cpp11

  type t = {
    with_consume : bool;
    name : string;
    release_sequence : release_sequence;
    allocations_are_writes : bool;
        (** RC11z: allocations and deallocations are writes to the location
            they allocate or free, ordered by [co] with the stores to it. *)
    no_thin_air : [ `Hb_rf | `Sb_rf ];
        (** [acyclic(hb ∪ rf)], as MoRDor's RC11 has always checked it, or the
            literal [acyclic(sb ∪ rf)] of Ou and Demsky's load-store ordering.
            The two agree whenever [hb] is built from [sb], [rf] and [rmw]. *)
  }

  let base =
    {
      with_consume = false;
      name = "rc11";
      release_sequence = Rc11;
      allocations_are_writes = false;
      no_thin_air = `Hb_rf;
    }

  let default = base
  let with_consume = { base with with_consume = true; name = "rc11c" }
  let rc17 = { base with name = "rc17"; release_sequence = Rc17 }
  let rc11z = { base with name = "rc11z"; allocations_are_writes = true }

  (** Ou and Demsky's load-store ordering criterion, [acyclic(sb ∪ rf)], over
      the C/C++11 model it constrains. *)
  let od_lso =
    { base with name = "od-lso"; release_sequence = Cpp11; no_thin_air = `Sb_rf }
end

module RC11 (Config : sig
  val config : RC11Config.t
end) : MEMORY_MODEL = struct
  (** Cache type *)
  type cache = {
    sb : (int * int) uset;
    hb : (int * int) uset option;
        (** [None] when [hb] depends on the coherence order; see
            {!RC11Config.release_sequence}. *)
    rfi : (int * int) uset;
    rf : (int * int) uset;
    e : int uset;
    events : (int, event) Hashtbl.t;
    thread_index : (int, int) Hashtbl.t;
    rmw : (int * int) uset;
    loc_restrict : (int * int) uset -> (int * int) uset;
  }

  (** Config type *)
  type config = RC11Config.t

  let name = Config.config.name
  let default_config = Config.config

  (** [W], and under RC11z the allocations and deallocations too. *)
  let writes events e =
    let w = ModelUtils.match_events events e Write None None None in
      if Config.config.allocations_are_writes then
        USet.union w (ModelUtils.match_events events e Malloc None None None)
        |> USet.union (ModelUtils.match_events events e Free None None None)
      else w

  (** [build_hb ~co ...] is [hb = (sw ∪ sb)⁺]. [co] is asked only by the
      [Cpp11] release sequence. *)
  let build_hb ?co ~events ~e ~sb ~rf ~rmw ~loc_restrict ~thread_index () =
    (* rs = [W];[po ∩ loc]?;[W_rlx⁺];(rf;rmw)⁺? *)
    let rs =
      let w = writes events e in
      let w_rlx =
        ModelUtils.match_events events e Write (Some Relaxed) (Some ">") None
      in
      let inner =
        URelation.transitive_closure (URelation.compose [ rf; rmw ])
      in
      let head =
        match Config.config.release_sequence with
        | Rc11 | Cpp11 ->
            URelation.compose
              [ w; URelation.reflexive_closure e (loc_restrict sb); w_rlx ]
        | Rc17 -> w_rlx
      in
      let head =
        match (Config.config.release_sequence, co) with
        | Cpp11, Some co ->
            let coe = ModelUtils.thread_external_of thread_index co in
              USet.set_minus head (URelation.compose [ coe; coe ])
        | _ -> head
      in
        URelation.compose [ head; URelation.reflexive_closure e inner ]
    in

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
    URelation.transitive_closure (USet.inplace_union ~into:sw sb)

  (** RC11 coherence cache builder *)
  let build_cache (execution : symbolic_execution)
      (structure : symbolic_event_structure)
      (loc_restrict : (int * int) uset -> (int * int) uset) : cache =
    let ({ e; rf; rmw; _ } : symbolic_execution) = execution in
    let ({ po; events; thread_index; _ } : symbolic_event_structure) =
      structure
    in

    let rf = USet.clone rf in
    let rmw = USet.clone rmw in
    let sb = USet.clone po in
    let hb =
      match Config.config.release_sequence with
      | Cpp11 -> None
      | Rc11 | Rc17 ->
          Some
            (build_hb ~events ~e ~sb ~rf ~rmw ~loc_restrict ~thread_index ())
    in

    {
      sb;
      hb;
      rfi = URelation.inverse rf;
      rf;
      e;
      events;
      thread_index;
      rmw;
      loc_restrict;
    }

  type candidate = {
    cache : cache;
    co : (int * int) uset;
    hb : (int * int) uset Lazy.t;
    rb : (int * int) uset Lazy.t;  (** [rf⁻¹;co] *)
    eco : (int * int) uset Lazy.t;  (** [(rf ∪ co ∪ rb)⁺] *)
  }

  let candidate (cache : cache) co =
    let { sb; hb; rfi; rf; e; events; thread_index; rmw; loc_restrict } =
      cache
    in
    let hb =
      match hb with
      | Some hb -> Lazy.from_val hb
      | None ->
          lazy
            (build_hb ~co ~events ~e ~sb ~rf ~rmw ~loc_restrict ~thread_index ())
    in
    let rb = lazy (URelation.compose [ rfi; co ]) in
    let eco =
      lazy
        (URelation.transitive_closure
           (USet.inplace_union ~into:(USet.union rf co) (Lazy.force rb))
        )
    in
      { cache; co; hb; rb; eco }

  (** Atomicity: [rmw ∩ (rb;co) = ∅]. Vacuous with no RMWs to violate it. *)
  let atomicity x =
    let { rf; rfi; rmw; _ } = x.cache in
      USet.size rmw = 0
      || CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co:x.co ()

  (* Coherence: [hb;eco ∪ hb] is irreflexive.

     This used to sit inside the RMW arm, and the arm without RMWs spelled it
     out inline in a different form. The two were not the same check: the
     shared one omitted the [∪ hb] term, so an execution containing an RMW
     was never asked whether hb was irreflexive -- for hb = (sw ∪ sb)⁺,
     whether sb ∪ sw is acyclic. One check now, outside the split.

     SC consistency did not depend on rmw either: both arms ran the same
     thirty-five lines of it, which is how they came to disagree in the first
     place. *)
  let coherence x =
    let { rf; rfi; _ } = x.cache in
      CoherenceChecks.coherence_axiom ~eco:(Lazy.force x.eco) ~rf ~rfi ~co:x.co
        ~hb:(Lazy.force x.hb) ()

  (** SC consistency: [psc] is acyclic. Asked last, so that only an execution
      which has passed atomicity and coherence pays for it. *)
  let sc_consistent x =
    let { sb; e; events; loc_restrict; _ } = x.cache in
    let co = x.co and hb = Lazy.force x.hb in
    let rb = Lazy.force x.rb and eco = Lazy.force x.eco in
    let sb_non_loc = USet.set_minus sb (loc_restrict sb) in
    (* scb = sb ∪ sbl;hb;sbl ∪ hbl ∪ co ∪ rb, with sbl = sb \ loc and
       hbl = hb ∩ loc, as in herd's rc11.cat.

       The middle term was sbl;hb, which contains sbl;hb;sbl and more: it
       let an event reach any hb-later one at another location, where RC11
       asks for an sb step at another location on both sides. At a fence end
       of psc_base the hb? there absorbs the difference; at an SC access it
       does not, and those ends were missing until the fix below. *)
    let scb =
      USet.union sb (URelation.compose [ sb_non_loc; hb; sb_non_loc ])
      |> USet.union (loc_restrict hb)
      |> USet.union co
      |> USet.union rb
    in

    (* E_sc, every access in mode sc: RC11's [SC], of any event type.

       This asked for [Init] events in mode sc, which never exist, so E_sc
       was empty and psc_base reduced to its fence terms. Store buffering
       over sc stores and loads came out allowed: psc is the only axiom that
       forbids it, and without the accesses it had nothing to order. *)
    let sc_events =
      USet.union
        (ModelUtils.match_events events e Read (Some SC) None None)
        (ModelUtils.match_events events e Write (Some SC) None None)
      |> USet.union (ModelUtils.match_events events e Fence (Some SC) None None)
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

  let axioms =
    [
      ("rmw ∩ (rb;co) = ∅", atomicity);
      ("hb;eco ∪ hb is irreflexive", coherence);
      ("psc is acyclic", sc_consistent);
    ]

  let check_coherence cache co = holds axioms (candidate cache co)

  let check_thin_air (cache : cache) (execution : symbolic_execution) =
    let { hb; rf; sb; _ } = cache in
      match (Config.config.no_thin_air, hb) with
      | `Hb_rf, Some hb -> CoherenceChecks.thin_air_check ~hb ~rf ()
      | _ -> CoherenceChecks.thin_air_check ~hb:sb ~rf ()

  let uses_co = true
  let orders_allocations = Config.config.allocations_are_writes
  let check_program _ = Ok ()
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

  type candidate = cache * (int * int) uset

  let candidate cache co = (cache, co)

  let axioms =
    [
      ( "rmw ∩ (rb;co) = ∅",
        fun ({ rf; rfi; rmw; _ }, co) ->
          CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co ()
      );
      ( "hb;eco ∪ hb is irreflexive",
        fun ({ rf; rfi; hb; _ }, co) ->
          CoherenceChecks.coherence_axiom ~rf ~rfi ~co ~hb ()
      );
    ]

  let check_coherence cache co = holds axioms (candidate cache co)

  let check_thin_air cache execution =
    let { rf; hb; _ } = cache in
    let result = CoherenceChecks.thin_air_check ~hb ~rf () in
      result

  let uses_co = true
  let orders_allocations = false
  let check_program _ = Ok ()
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

  type candidate = cache * (int * int) uset

  let candidate cache co = (cache, co)

  let axioms =
    [
      ( "rmw ∩ (rb;co) = ∅",
        fun ({ rf; rfi; rmw }, co) ->
          CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co ()
      );
    ]

  let check_coherence cache co = holds axioms (candidate cache co)

  let check_thin_air execution cache = true
  let uses_co = true
  let orders_allocations = false
  let check_program _ = Ok ()
  let compute_dependencies _ _ _ _ _ = USet.create ()
end

(** {1 Models over sMRD's relations as they stand}

    Each model below is a set of axioms over relations the pipeline already
    computes -- [po], [rf], [rmw], the candidate [co], access modes, symbolic
    locations and, since the interpreter numbers them, threads. They were
    surveyed against the Relaxed Memory Model Zoo and found to need no new
    primitive.

    Two limits apply to all of them, and neither is theirs. A model here is a
    filter on sMRD's candidate executions, so a model weaker than sMRD's
    thin-air discipline cannot exhibit an out-of-thin-air execution sMRD never
    generates. And the distributed consistency models are stated over
    histories; reading one as a shared-memory predicate needs an encoding,
    which each module's comment states. *)

(** The vocabulary shared by the models below: one execution's events and
    relations, restricted to the execution. *)
module Vocab = struct
  type t = {
    e : int uset;
    events : (int, event) Hashtbl.t;
    thread_index : (int, int) Hashtbl.t;
    po : (int * int) uset;  (** [po ∩ (E × E)] *)
    rf : (int * int) uset;
    rfi : (int * int) uset;  (** [rf⁻¹] *)
    rmw : (int * int) uset;
    reads : int uset;
    writes : int uset;
        (** Stores, and the initial event when it is one: event [0] is the
            write every uninitialised location reads from. *)
    r : (int * int) uset;  (** [\[R\]] *)
    w : (int * int) uset;  (** [\[W\]] *)
    loc_restrict : (int * int) uset -> (int * int) uset;
    same_loc : (int * int) uset;  (** same location, over reads and writes *)
    initial : int option;
    atomic : int uset;
        (** Accesses of an atomic instruction: the load and store of a CAS or
            FADD, whether it succeeds or not. *)
  }

  let make (execution : symbolic_execution)
      (structure : symbolic_event_structure) loc_restrict =
    let e = execution.e in
    let events = structure.events in
    let typed typ =
      USet.filter
        (fun id ->
          match Hashtbl.find_opt events id with
          | Some ev -> ev.typ = typ
          | None -> false
        )
        e
    in
    let initial =
      match Hashtbl.find_opt events 0 with
      | Some ev when ev.typ = Init && USet.mem e 0 -> Some 0
      | _ -> None
    in
    let reads = typed Read in
    let stores = typed Write in
    let writes = USet.clone stores in
      Option.iter (fun i -> USet.add writes i |> ignore) initial;
      let po = USet.filter (fun (a, b) -> USet.mem e a && USet.mem e b) structure.po in
      let rf = USet.clone execution.rf in
      let mem = USet.union reads stores in
      let atomic =
        USet.fold
          (fun acc (a, _, b) ->
            USet.add acc a |> ignore;
            USet.add acc b |> ignore;
            acc
          )
          structure.rmw (USet.create ())
        |> USet.intersection e
      in
        {
          e;
          events;
          thread_index = structure.thread_index;
          po;
          rf;
          rfi = URelation.inverse rf;
          rmw = USet.clone execution.rmw;
          reads;
          writes;
          r = URelation.identity reads;
          w = URelation.identity writes;
          loc_restrict;
          same_loc = loc_restrict (URelation.cross mem mem);
          initial;
          atomic;
        }

  let internal v x = ModelUtils.thread_internal_of v.thread_index x
  let external_ v x = ModelUtils.thread_external_of v.thread_index x

  (** [po] within a thread: program order as a process or session sees it. *)
  let po_int v = internal v v.po

  (** [po] between threads: what a block's threads inherit from the code
      before it, and what the code after it inherits from them. The
      initialising stores are the case that matters. They are program order,
      not another process's writes, and a view that could place [x := 0] after
      a thread's [x := 1] would let a reader see 1 and then 0. *)
  let fork_order v = external_ v v.po

  (** [co], with the initial event first at every location. The search puts it
      there only when a read reads from it and two writes exist, so a single
      store and a read of the initial value came with no order between them. *)
  let co v co =
    match v.initial with
    | None -> co
    | Some i ->
        let co = USet.clone co in
          USet.iter (fun w -> if w <> i then USet.add co (i, w) |> ignore) v.writes;
          co

  (** [fr = (rf⁻¹;co) \ id]: from a read to the writes after the one it read. *)
  let fr v co =
    URelation.compose [ v.rfi; co ] |> USet.filter (fun (a, b) -> a <> b)

  let atomicity v co =
    USet.is_empty v.rmw
    || CoherenceChecks.rmw_atomicity ~rf:v.rf ~rfi:v.rfi ~rmw:v.rmw ~co ()

  let union rels =
    List.fold_left (fun acc r -> USet.inplace_union ~into:acc r) (USet.create ()) rels

  let fences v =
    USet.filter
      (fun id ->
        match Hashtbl.find_opt v.events id with
        | Some ev -> ev.typ = Fence
        | None -> false
      )
      v.e
    |> URelation.identity
end

(** A candidate coherence order as an axiomatic model sees it: the vocabulary,
    what the model prepared from it, and the order as {!Vocab.co} gives it, with
    [fr] derived when an axiom first asks. *)
type 'd axiomatic_candidate = {
  v : Vocab.t;
  d : 'd;
  co : (int * int) uset;
  fr : (int * int) uset Lazy.t;
}

(** A model whose cache is {!Vocab.t} plus what [prepare] derives from it once
    per execution. *)
module Axiomatic (A : sig
  val name : string
  val uses_co : bool

  type derived

  val prepare : Vocab.t -> derived
  val axioms : (string * (derived axiomatic_candidate -> bool)) list
end) : MEMORY_MODEL = struct
  type cache = Vocab.t * A.derived
  type config = unit

  let name = A.name
  let default_config = ()

  let build_cache execution structure loc_restrict =
    let v = Vocab.make execution structure loc_restrict in
      (v, A.prepare v)

  type candidate = A.derived axiomatic_candidate

  let candidate (v, d) co =
    let co = Vocab.co v co in
      { v; d; co; fr = lazy (Vocab.fr v co) }

  let axioms = A.axioms
  let check_coherence cache co = holds axioms (candidate cache co)
  let check_thin_air _ _ = true
  let uses_co = A.uses_co
  let orders_allocations = false
  let check_program _ = Ok ()
  let compute_dependencies _ _ _ _ _ = USet.create ()
end

(** Sequential consistency: [acyclic(po ∪ rf ∪ co ∪ fr)], with herd's
    [sc.cat] atomicity for RMWs. *)
module SCAxioms (N : sig
  val name : string
end) =
Axiomatic (struct
  let name = N.name
  let uses_co = true

  type derived = (int * int) uset

  let prepare (v : Vocab.t) = Vocab.union [ v.po; v.rf ]

  let axioms =
    [
      ("rmw ∩ (fr;co) = ∅", fun x -> Vocab.atomicity x.v x.co);
      ( "po ∪ rf ∪ co ∪ fr is acyclic",
        fun x -> URelation.acyclic (Vocab.union [ x.d; x.co; Lazy.force x.fr ])
      );
    ]
end)

(** Total store order, as herd's [tso.cat]:

    - [acyclic(po-loc ∪ rf ∪ co ∪ fr)]
    - [rmw ∩ (fre;coe) = ∅], checked as the other models check atomicity
    - [acyclic(ppo ∪ rfe ∪ co ∪ fr)], with
      [ppo = \[R\];po;\[R\] ∪ \[M\];po;\[W\] ∪ \[M\];po;\[F\];po;\[M\] ∪ implied]
      and [implied = \[W\];po;\[R\];\[A\] ∪ \[A\];\[W\];po;\[R\]], the store buffer
      flushed by an atomic instruction.

    Every fence is a full fence: on x86 C11's fences compile to [mfence]. *)
module TSOAxioms (N : sig
  val name : string
end) =
Axiomatic (struct
  let name = N.name
  let uses_co = true

  type derived = { scperloc : (int * int) uset; ghb : (int * int) uset }

  let prepare (v : Vocab.t) =
    let m = URelation.identity (USet.union v.reads v.writes) in
    let a = URelation.identity v.atomic in
    let pow_r = URelation.compose [ v.w; v.po; v.r ] in
    let ppo =
      Vocab.union
        [
          URelation.compose [ v.r; v.po; v.r ];
          URelation.compose [ m; v.po; v.w ];
          URelation.compose [ m; v.po; Vocab.fences v; v.po; m ];
          URelation.compose [ pow_r; a ];
          URelation.compose [ a; pow_r ];
        ]
    in
      {
        scperloc = Vocab.union [ v.loc_restrict v.po; v.rf ];
        ghb = Vocab.union [ ppo; Vocab.external_ v v.rf ];
      }

  let axioms =
    [
      ( "po-loc ∪ rf ∪ co ∪ fr is acyclic",
        fun x ->
          URelation.acyclic (Vocab.union [ x.d.scperloc; x.co; Lazy.force x.fr ])
      );
      ("rmw ∩ (fr;co) = ∅", fun x -> Vocab.atomicity x.v x.co);
      ( "ppo ∪ rfe ∪ co ∪ fr is acyclic",
        fun x ->
          URelation.acyclic (Vocab.union [ x.d.ghb; x.co; Lazy.force x.fr ])
      );
    ]
end)

(** Per-location cache coherence, herd's [scperloc] alone:
    [acyclic(po-loc ∪ rf ∪ co ∪ fr)]. *)
module CoherenceModel = Axiomatic (struct
  let name = "coherence"
  let uses_co = true

  type derived = (int * int) uset

  let prepare (v : Vocab.t) = Vocab.union [ v.loc_restrict v.po; v.rf ]

  let axioms =
    [
      ( "po-loc ∪ rf ∪ co ∪ fr is acyclic",
        fun x -> URelation.acyclic (Vocab.union [ x.d; x.co; Lazy.force x.fr ])
      );
    ]
end)

(** The release-acquire family, as Lahav and Boker tabulate it (TOPLAS 2022,
    Table 1) and the zoo's [ra.cat], [sra.cat] and [wra.cat] state it:

    - [sw = \[W_rel⁺\];rf;\[R_acq⁺\]] and [hb = (po ∪ sw)⁺]; MoRDor's [po]
      already puts the initialisation before every thread
    - RA: [irreflexive hb], [irreflexive co;hb], [irreflexive co;hb;rf⁻¹],
      atomicity
    - SRA: RA with [acyclic(hb ∪ co)] for [irreflexive co;hb]
    - WRA: [irreflexive hb], [irreflexive (hb ∩ loc);\[W\];hb;rf⁻¹], and no
      two RMWs reading one write. [co] plays no part.
    - CC, Bouajjani et al.'s weak causal consistency, which Lahav and Boker
      show WRA equivalent to: WRA's axioms with every access synchronising,
      [sw = rf]. CC's histories have no RMWs, so it has no atomicity axiom. *)
module ReleaseAcquire (F : sig
  val name : string
  val variant : [ `RA | `SRA | `WRA | `CC ]
end) =
Axiomatic (struct
  let name = F.name
  let uses_co = match F.variant with `RA | `SRA -> true | `WRA | `CC -> false

  type derived = { hb : (int * int) uset; hb_ok : bool }

  let prepare (v : Vocab.t) =
    let sw =
      match F.variant with
      | `CC -> v.rf
      | `RA | `SRA | `WRA ->
          URelation.compose
            [
              ModelUtils.match_events v.events v.e Write (Some Release)
                (Some ">") None;
              v.rf;
              ModelUtils.match_events v.events v.e Read (Some Acquire) (Some ">")
                None;
            ]
    in
    let hb = URelation.transitive_closure (Vocab.union [ v.po; sw ]) in
      { hb; hb_ok = URelation.is_irreflexive hb }

  let co_hb_rfi (x : derived axiomatic_candidate) =
    URelation.is_irreflexive (URelation.compose [ x.co; x.d.hb; x.v.rfi ])

  let atomicity (x : derived axiomatic_candidate) = Vocab.atomicity x.v x.co

  let weak_read_coherence (x : derived axiomatic_candidate) =
    let v = x.v and hb = x.d.hb in
      URelation.is_irreflexive
        (URelation.compose [ v.loc_restrict hb; v.w; hb; v.rfi ])

  (* no two RMWs read one write: ((rf;[RMW])⁻¹;(rf;[RMW])) \ id = ∅ *)
  let weak_atomicity (x : derived axiomatic_candidate) =
    let v = x.v in
    let rmw_reads = URelation.identity (URelation.pi_1 v.rmw) in
    let rf_rmw = URelation.compose [ v.rf; rmw_reads ] in
      URelation.compose [ URelation.inverse rf_rmw; rf_rmw ]
      |> USet.for_all (fun (a, b) -> a = b)

  let axioms =
    ("hb is irreflexive", fun (x : derived axiomatic_candidate) -> x.d.hb_ok)
    ::
    ( match F.variant with
    | `RA ->
        [
          ( "co;hb is irreflexive",
            fun x ->
              URelation.is_irreflexive (URelation.compose [ x.co; x.d.hb ])
          );
          ("co;hb;rf⁻¹ is irreflexive", co_hb_rfi);
          ("rmw ∩ (fr;co) = ∅", atomicity);
        ]
    | `SRA ->
        [
          ( "hb ∪ co is acyclic",
            fun x -> URelation.acyclic (Vocab.union [ x.d.hb; x.co ])
          );
          ("co;hb;rf⁻¹ is irreflexive", co_hb_rfi);
          ("rmw ∩ (fr;co) = ∅", atomicity);
        ]
    | `WRA ->
        [
          ("(hb ∩ loc);[W];hb;rf⁻¹ is irreflexive", weak_read_coherence);
          ("no two RMWs read one write", weak_atomicity);
        ]
    | `CC -> [ ("(hb ∩ loc);[W];hb;rf⁻¹ is irreflexive", weak_read_coherence) ]
    )
end)

(** Per-process views, for the Steinke--Nutt lattice (JPDC 2004).

    A process's view is a total order over every write of the execution and
    that process's own reads, in which each read reads the latest write to its
    location before it. The models differ in what every view must respect:

    - Local: the process's own program order, and nothing else
    - Slow: also each process's writes to a location, in the order issued
    - PRAM: also each process's writes, in the order issued
    - Causal: also the causal order [(po ∪ rf)⁺], Ahamad et al.'s causal memory
    - PC: PRAM's, and one order of the writes to each location shared by every
      view -- that order is the candidate [co]

    A process is a thread. The initial event is before everything in every
    view, and so is program order between threads: the stores before a
    parallel block precede its threads' events, as the threads' events precede
    what follows the block. Nothing here makes an RMW atomic: the histories these models are
    stated over have none. Existence of a view is decided by search over the
    order its events are placed in, memoised on the events placed and the
    latest write at each location. *)
module Views (F : sig
  val name : string
  val variant : [ `Local | `Slow | `PRAM | `Causal | `PC ]
end) =
Axiomatic (struct
  let name = F.name
  let uses_co = F.variant = `PC

  type derived = {
    loc_of : (int, int) Hashtbl.t;  (** location class, by least member *)
    precedence : (int * int) uset;  (** what every view respects, less [co] *)
    processes : (int * int uset) list;  (** thread, and its reads and writes *)
  }

  let prepare (v : Vocab.t) =
    let loc_of = Hashtbl.create 32 in
      USet.iter
        (fun (a, b) ->
          match Hashtbl.find_opt loc_of b with
          | Some l when l <= a -> ()
          | _ -> Hashtbl.replace loc_of b a
        )
        v.same_loc;
      let po_int = Vocab.po_int v in
      let precedence =
        match F.variant with
        | `Local -> USet.create ()
        | `Slow -> URelation.compose [ v.w; v.loc_restrict po_int; v.w ]
        | `PRAM | `PC -> URelation.compose [ v.w; po_int; v.w ]
        | `Causal -> URelation.transitive_closure (Vocab.union [ v.po; v.rf ])
      in
      let precedence = Vocab.union [ precedence; Vocab.fork_order v ] in
      let processes =
        let tbl = Hashtbl.create 8 in
          USet.iter
            (fun id ->
              match Hashtbl.find_opt v.thread_index id with
              | Some t ->
                  let s =
                    match Hashtbl.find_opt tbl t with
                    | Some s -> s
                    | None ->
                        let s = USet.create () in
                          Hashtbl.replace tbl t s;
                          s
                  in
                    USet.add s id |> ignore
              | None -> ()
            )
            (USet.union v.reads v.writes);
          Hashtbl.fold (fun t s acc -> (t, s) :: acc) tbl []
      in
        { loc_of; precedence; processes }

  (** [view_exists v d ~co own]: some view of the process with events [own]. *)
  let view_exists (v : Vocab.t) d ~co own =
    let nodes =
      USet.union (USet.intersection own v.reads) v.writes
      |> USet.filter (fun id -> Some id <> v.initial)
      |> USet.values
      |> List.sort compare
      |> Array.of_list
    in
    let n = Array.length nodes in
      if n > Sys.int_size - 1 then
        failwith
          (Printf.sprintf
             "Memory model %s: a view of %d events is more than the search \
              can represent."
             F.name n
          );
      let index = Hashtbl.create n in
        Array.iteri (fun i id -> Hashtbl.replace index id i) nodes;
        let preds = Array.make n 0 in
        let add_pred (a, b) =
          match (Hashtbl.find_opt index a, Hashtbl.find_opt index b) with
          | Some i, Some j when i <> j -> preds.(j) <- preds.(j) lor (1 lsl i)
          | _ -> ()
        in
          (* the process's own program order *)
          USet.iter
            (fun (a, b) -> if USet.mem own a && USet.mem own b then add_pred (a, b))
            v.po;
          USet.iter add_pred d.precedence;
          USet.iter add_pred co;
          let locs =
            Array.map
              (fun id -> Hashtbl.find_opt d.loc_of id |> Option.value ~default:id)
              nodes
          in
          let is_read = Array.map (fun id -> USet.mem v.reads id) nodes in
          (* a read's source, as a node index, [-1] for the initial event, or
             [-2] when it reads from something that is not a write *)
          let source =
            Array.map
              (fun id ->
                if not (USet.mem v.reads id) then -2
                else
                  match
                    USet.values v.rf
                    |> List.find_opt (fun (_, r) -> r = id)
                  with
                  | Some (w, _) when Some w = v.initial -> -1
                  | Some (w, _) -> (
                      match Hashtbl.find_opt index w with
                      | Some i -> i
                      | None -> -2
                    )
                  | None -> -2
              )
              nodes
          in
          let all = if n = 0 then 0 else (1 lsl n) - 1 in
          let failed = Hashtbl.create 64 in
          let rec search placed (latest : (int * int) list) =
            if placed = all then true
            else
              let key = (placed, latest) in
                if Hashtbl.mem failed key then false
                else
                  let enabled i =
                    placed land (1 lsl i) = 0 && preds.(i) land placed = preds.(i)
                  in
                  let latest_at l =
                    List.assoc_opt l latest |> Option.value ~default:(-1)
                  in
                  let readable i =
                    source.(i) = -2 || latest_at locs.(i) = source.(i)
                  in
                  (* A read that can be placed now is placed now: it changes no
                     location, and anything placed before it could as well come
                     after. *)
                  let rec read_now i =
                    if i = n then None
                    else if is_read.(i) && enabled i && readable i then Some i
                    else read_now (i + 1)
                  in
                    match read_now 0 with
                    | Some i -> search (placed lor (1 lsl i)) latest
                    | None ->
                        let rec try_write i =
                          if i = n then false
                          else if (not is_read.(i)) && enabled i then
                            let latest' =
                              (locs.(i), i) :: List.remove_assoc locs.(i) latest
                              |> List.sort compare
                            in
                              search (placed lor (1 lsl i)) latest'
                              || try_write (i + 1)
                          else try_write (i + 1)
                        in
                        let ok = try_write 0 in
                          if not ok then Hashtbl.replace failed key ();
                          ok
          in
            search 0 []

  let axioms =
    [
      ( "every process has a view",
        fun (x : derived axiomatic_candidate) ->
          let co = if F.variant = `PC then x.co else USet.create () in
            List.for_all
              (fun (_, own) -> view_exists x.v x.d ~co own)
              x.d.processes
      );
    ]
end)

(** Per-object causal consistency (Burckhardt et al., POPL 2014, §7), over
    [vis := rf] and [ar := co]:

    - [hbo = ((po ∩ loc) ∪ rf)⁺], a session's order at one location with what
      its reads saw, is acyclic. Program order between threads counts as a
      session's own: a block's threads follow what came before it, and the
      code after the join follows them.
    - POCA: [irreflexive co;hbo] -- arbitration respects it
    - return values: [irreflexive fr;hbo] -- nothing [hbo]-before a read is
      arbitrated after the write it read

    [vis] is taken least, which is the choice every axiom here is weakest
    under. Eventual consistency's liveness clause says nothing of a finite
    execution. *)
module POCausal = Axiomatic (struct
  let name = "pocausal"
  let uses_co = true

  type derived = { hbo : (int * int) uset; acyclic : bool }

  let prepare (v : Vocab.t) =
    let hbo =
      URelation.transitive_closure
        (Vocab.union
           [
             v.loc_restrict (Vocab.po_int v);
             v.loc_restrict (Vocab.fork_order v);
             v.rf;
           ]
        )
    in
      { hbo; acyclic = URelation.is_irreflexive hbo }

  let axioms =
    [
      ("hbo is acyclic", fun (x : derived axiomatic_candidate) -> x.d.acyclic);
      ( "co;hbo is irreflexive",
        fun x -> URelation.is_irreflexive (URelation.compose [ x.co; x.d.hbo ])
      );
      ( "fr;hbo is irreflexive",
        fun x ->
          URelation.is_irreflexive
            (URelation.compose [ Lazy.force x.fr; x.d.hbo ])
      );
    ]
end)

(** Terry et al.'s session guarantees (PDIS 1994), in Viotti and Vukolić's
    form (ACM CSUR 2016) over an arbitration order and a visibility per read.

    A session is a thread. Visibility is taken least, closed under what the
    guarantees demand:

    [vis = (rf ∪ RYW) ; MR?], with [RYW = \[W\];po_int;\[R\]] and
    [MR = po_int;\[R\]], each present when its guarantee is. MW and WFR
    constrain arbitration and not visibility.

    Each reader has its own arbitration: a replica applies other sessions'
    writes in an order of its own. It exists when these are acyclic, with the
    initial event first and writes in program order across a fork or join:

    - return values: [((vis ∩ loc);\[R_p\];rf⁻¹) \ id], every write a read of
      session [p] saw is before the one it read
    - MW: [\[W\];po_int;\[W\]], every session's writes in the order issued
    - WFR: [vis;po_int;\[W\]], a session's writes after what it had read

    Arbitration is per reader rather than Viotti and Vukolić's one global
    order. With one order, RYW forbids two threads each reading the other's
    write after writing their own, which PRAM as Steinke and Nutt state it
    allows, and the zoo's edge from PRAM to RYW would not hold.

    A consequence worth knowing: MW alone forbids nothing. Least visibility
    gives a read only the write it read, so no reader has two writes of one
    session to arbitrate between, and the order MW adds can close no cycle.
    WFR can, since its edges run between sessions: load buffering orders each
    thread's store after the other's. MW bites in conjunction, which is how
    Brzezinski et al. (2003) obtain PRAM from RYW, MR and MW; PRAM itself is
    implemented by [Views]. *)
module Sessions (F : sig
  val name : string
  val ryw : bool
  val mr : bool
  val mw : bool
  val wfr : bool
end) =
Axiomatic (struct
  let name = F.name
  let uses_co = false

  type derived = {
    arbitration : (int * int) uset;  (** the edges every reader shares *)
    per_reader : (int * (int * int) uset) list;
  }

  let prepare (v : Vocab.t) =
    let po_int = Vocab.po_int v in
    let mw = URelation.compose [ v.w; po_int; v.w ] in
    let vis =
      let seen =
        if F.ryw then Vocab.union [ v.rf; URelation.compose [ v.w; po_int; v.r ] ]
        else USet.clone v.rf
      in
        if F.mr then
          URelation.compose
            [ seen; URelation.reflexive_closure v.reads (URelation.compose [ po_int; v.r ]) ]
        else seen
    in
    let initial_first =
      match v.initial with
      | Some i ->
          USet.filter (fun w -> w <> i) v.writes
          |> USet.map (fun w -> (i, w))
      | None -> USet.create ()
    in
    let arbitration =
      Vocab.union
        [
          initial_first;
          URelation.compose [ v.w; Vocab.fork_order v; v.w ];
          (if F.mw then mw else USet.create ());
          (if F.wfr then URelation.compose [ vis; po_int; v.w ]
           else USet.create ());
        ]
    in
    let vis_loc = USet.intersection vis v.same_loc in
    let readers =
      USet.fold
        (fun acc r ->
          match Hashtbl.find_opt v.thread_index r with
          | Some t when not (List.mem t acc) -> t :: acc
          | _ -> acc
        )
        v.reads []
    in
    let per_reader =
      List.map
        (fun t ->
          let of_reader =
            USet.filter
              (fun (_, r) -> Hashtbl.find_opt v.thread_index r = Some t)
              vis_loc
          in
            ( t,
              URelation.compose [ of_reader; v.rfi ]
              |> USet.filter (fun (w, s) -> w <> s) ))
        readers
    in
      { arbitration; per_reader }

  let axioms =
    [
      ( "arbitration is acyclic",
        fun (x : derived axiomatic_candidate) ->
          URelation.acyclic x.d.arbitration
      );
      ( "every reader's arbitration is acyclic",
        fun x ->
          List.for_all
            (fun (_, edges) ->
              URelation.acyclic (USet.union x.d.arbitration edges)
            )
            x.d.per_reader
      );
    ]
end)

(** MRD: sMRD's axioms, on the programs where sMRD and MRD are one model.

    sMRD extends MRD with symbolic and dynamic memory: alias analysis, the
    undefined-behaviour fold and allocation. On a program with none of those
    -- every access to a named global, nothing allocated or freed -- the two
    compute the same dependencies, and this is sMRD. On any other program sMRD
    admits executions MRD does not, and nothing here can tell which, so the
    model refuses the program. The undefined-behaviour fold is off under this
    model's name. *)
module MRD : MEMORY_MODEL = struct
  include SMRD

  let name = "mrd"

  let check_program (structure : symbolic_event_structure) =
    let offending =
      Hashtbl.fold
        (fun _ (ev : event) acc ->
          match (ev.typ, ev.loc) with
          | (Malloc | Free), _ -> ev :: acc
          | (Read | Write), Some (EVar _) -> acc
          | (Read | Write), _ -> ev :: acc
          | _ -> acc
        )
        structure.events []
    in
      match offending with
      | [] -> Ok ()
      | ev :: _ ->
          Error
            (Printf.sprintf
               "MRD is implemented as sMRD on programs whose accesses are all \
                to named globals and which allocate nothing; event %d (%s) is \
                outside that fragment, where sMRD admits executions MRD does \
                not."
               ev.label (show_event_type ev.typ)
            )
end

type restrictions = { coherent : string }

(** Model registry with configs *)
module ModelRegistry = struct
  let models : (string, unit -> (module MEMORY_MODEL)) Hashtbl.t =
    Hashtbl.create 10

  let register name create_fn = Hashtbl.add models name create_fn

  let lookup name =
    match Hashtbl.find_opt models name with
    | Some create -> Some (create ())
    | None -> None

  (* No model registers one of its own yet. *)
  let incremental : (string, unit -> (module INCREMENTAL_MODEL)) Hashtbl.t =
    Hashtbl.create 10

  let lookup_incremental name =
    match Hashtbl.find_opt incremental name with
    | Some create -> Some (create ())
    | None ->
        lookup name
        |> Option.map (fun model ->
            let module M = (val model : MEMORY_MODEL) in
            (module Incremental (M) : INCREMENTAL_MODEL)
        )

  let names () = Hashtbl.fold (fun name _ acc -> name :: acc) models []

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

    let rc11_variant config =
      let module M = RC11 (struct
        let config = config
      end) in
        (module M : MEMORY_MODEL)
    in
      register "rc17" (fun () -> rc11_variant RC11Config.rc17);
      register "rc11z" (fun () -> rc11_variant RC11Config.rc11z);
      register "od-lso" (fun () -> rc11_variant RC11Config.od_lso);
      register "mrd" (fun () -> (module MRD : MEMORY_MODEL));

      register "sc" (fun () ->
          let module M = SCAxioms (struct
            let name = "sc"
          end) in
          (module M : MEMORY_MODEL)
      );
      register "vbd" (fun () ->
          let module M = SCAxioms (struct
            let name = "vbd"
          end) in
          (module M : MEMORY_MODEL)
      );
      List.iter
        (fun name ->
          register name (fun () ->
              let module M = TSOAxioms (struct
                let name = name
              end) in
              (module M : MEMORY_MODEL)
          )
        )
        [ "tso"; "x86-tso"; "clighttso" ];
      register "coherence" (fun () -> (module CoherenceModel : MEMORY_MODEL));
      List.iter
        (fun (name, variant) ->
          register name (fun () ->
              let module M = ReleaseAcquire (struct
                let name = name
                let variant = variant
              end) in
              (module M : MEMORY_MODEL)
          )
        )
        [ ("ra", `RA); ("sra", `SRA); ("wra", `WRA); ("cc", `CC) ];
      List.iter
        (fun (name, variant) ->
          register name (fun () ->
              let module M = Views (struct
                let name = name
                let variant = variant
              end) in
              (module M : MEMORY_MODEL)
          )
        )
        [
          ("local", `Local);
          ("slow", `Slow);
          ("pram", `PRAM);
          ("causal", `Causal);
          ("pc", `PC);
        ];
      register "pocausal" (fun () -> (module POCausal : MEMORY_MODEL));
      List.iter
        (fun (name, ryw, mr, mw, wfr) ->
          register name (fun () ->
              let module M = Sessions (struct
                let name = name
                let ryw = ryw
                let mr = mr
                let mw = mw
                let wfr = wfr
              end) in
              (module M : MEMORY_MODEL)
          )
        )
        [
          ("ryw", true, false, false, false);
          ("mr", false, true, false, false);
          ("mw", false, false, true, false);
          ("wfr", false, false, false, true);
        ];

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
let try_all_coherence_orders ?(uses_co = true) ?(orders_allocations = false)
    cache structure execution check_coherence eqlocs =
  if USet.size execution.e = 0 then None
  else
    let ({ po; restrict; _ } : symbolic_event_structure) = structure in
    let writes =
      USet.filter
        (fun ev_id ->
          try
            let event = Hashtbl.find structure.events ev_id in
              event.typ = Write
              || orders_allocations
                 && (event.typ = Malloc || event.typ = Free)
          with Not_found -> false
        )
        execution.e
    in

    if (not uses_co) || USet.size writes < 2 then
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
                          (* Equal under the execution's own predicates. Asked
                             without them, a write through a pointer never
                             shared a location with a write to the location it
                             points at, so co never ordered the two and a read
                             could take the value the pointer write had
                             overwritten. *)
                          exeq ~state:execution.ex_p loc_a loc_b
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
          try_all_coherence_orders ~uses_co:M.uses_co
            ~orders_allocations:M.orders_allocations cache structure execution
            M.check_coherence eqlocs

(** [check_model_program structure name] fails, with the model's reason, when
    the coherence model [name] cannot answer for the program [structure] is the
    event structure of. Unknown names are left to {!check_for_coherence}. *)
let check_model_program structure name =
  match ModelRegistry.lookup name with
  | None -> ()
  | Some model -> (
      let module M = (val model : MEMORY_MODEL) in
        match M.check_program structure with
        | Ok () -> ()
        | Error reason -> failwith reason
    )
