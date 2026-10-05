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

(* S10 (see Executions.S10): coherence stage timings and locality. *)
let s10_stages = Option.is_some (Sys.getenv_opt "MORDOR_S10_RF_SAMPLES")
let s10_lock = Mutex.create ()

(** S6 (branch and bound over coherence orders): when [prune] is set, the search
    asks the model about each partial coherence order it builds, and abandons it
    when the model already rejects it. Off by default; enabled via
    [MORDOR_S6_PRUNE]. The counters record what the search did.

    Sound only for a model whose violations grow with co. od-lso's and c11's do
    not: their C++11 release sequence subtracts [coe;coe], so more co can mean
    less hb. Slower than the exhaustive search on every corpus measured; see
    spike/s6_coherence_bb/RESULTS.md on the bottom-up-refactor branch. *)
module S6 = struct
  let prune = ref (Option.is_some (Sys.getenv_opt "MORDOR_S6_PRUNE"))

  (* Ask about a partial order only when at least this many complete orders
     extend it: below that, a check costs as much as the leaves it could
     save. *)
  let min_leaves =
    ref
      (Option.bind (Sys.getenv_opt "MORDOR_S6_MIN_LEAVES") int_of_string_opt
      |> Option.value ~default:1
      )

  let partial_checks = ref 0
  let pruned = ref 0
  let leaf_checks = ref 0

  let reset () =
    partial_checks := 0;
    pruned := 0;
    leaf_checks := 0
end

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

  (** The model's data races in a candidate: conflicting accesses of two threads
      that [hb] leaves unordered. A model with this clause -- herd's
      [undefined_unless empty dr] -- gives a program with a consistent racy
      execution undefined behaviour; [None] for a model without one. *)
  val data_races : (candidate -> (int * int) uset) option

  (** Whether the model lets sMRD elide the write [elided], which the po-later
      write [by] of its thread to the same location overwrites. sMRD's write
      elision drops an overwritten write whatever its mode. Under a model whose
      release sequence continues through later stores of the writer's thread,
      eliding a release store loses the synchronisation those stores carried,
      and the model rejects every execution that does. *)
  val elidable : symbolic_event_structure -> elided:int -> by:int -> bool

  (** Whether the model allows out-of-thin-air executions: those whose
      reads-happen-before, [dp ∪ ppo ∪ rf], has a cycle. sMRD's generator
      drops them before any model is asked unless a model of the run allows
      them; then every model that does not rejects them itself. *)
  val allows_thin_air : bool

  (** Whether [check_coherence] reads the coherence order it is given. A model
      whose axioms quantify over orders of their own -- a view per process, an
      arbitration per session -- does not, and the search then asks it once
      rather than once per candidate order. *)
  val uses_co : bool

  (** Whether allocations and deallocations are writes to the coherence order,
      as RC11z makes them. *)
  val orders_allocations : bool

  (** [Error reason] when the model cannot answer for this program at all. It is
      asked once, before any execution is, and the pipeline fails with the
      reason rather than returning a verdict that is not the model's. *)
  val check_program : symbolic_event_structure -> (unit, string) result

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

  (** Every write elision stands. *)
  let elidable_always _ ~elided:_ ~by:_ = true

  (** A release store may be elided only by a release store. Under a release
      sequence that later stores of the writer's thread continue -- RC11's,
      C++11's, IMM's -- a relaxed store overwriting a release store carries its
      release on, and an acquire reading it synchronises with the release. With
      the release store elided there is nothing to synchronise with. A release
      store overwriting it synchronises with everything po-before it, the
      elided store's predecessors included. *)
  let release_elidable_by_release (structure : symbolic_event_structure)
      ~elided ~by =
    let events = structure.events in
    let release id =
      match Hashtbl.find_opt events id with
      | Some { typ = Write; wmod; _ } -> mode_at_least wmod Release
      | _ -> false
    in
      (not (release elided)) || release by

  (** [same_thread thread_index a b]: [a] and [b] are events of one thread.
      Events outside every thread -- the initial event, terminals -- are in
      none, so every pair involving one is external. *)
  let same_thread thread_index a b =
    match
      (Hashtbl.find_opt thread_index a, Hashtbl.find_opt thread_index b)
    with
    | Some ta, Some tb -> ta = tb
    | _ -> false

  (** [int] and [ext] of a relation by thread identity, where {!thread_internal}
      and {!thread_external} approximate them by [po]. *)
  let thread_internal_of thread_index x =
    USet.filter (fun (a, b) -> same_thread thread_index a b) x

  let thread_external_of thread_index x =
    USet.filter (fun (a, b) -> not (same_thread thread_index a b)) x

  (** [lock_orders structure e] is the lock orders the events [e] of an
      execution admit, each as the [[Unlock]; lo; [Lock]] edges it adds to [hb].

      Locks are reentrant, as Java's monitors are: a thread's locks and unlocks
      of one lock nest as brackets, and only an outermost pair is a critical
      section. The sections on one lock run one at a time, in some total order
      that respects [po]: each section's unlock happens before the next
      section's lock. A section with no unlock never releases the lock, so it
      must be the last on it; two such admit no order. Locks on different
      globals are ordered independently.

      With no lock in [e] there is exactly one lock order, and it is empty. *)
  let lock_orders (structure : symbolic_event_structure) (e : int uset) =
    let of_type typ =
      USet.values e
      |> List.filter (fun x ->
          match Hashtbl.find_opt structure.events x with
          | Some (ev : event) -> ev.typ = typ
          | None -> false
      )
      |> List.sort compare
    in
    let key x = (Hashtbl.find structure.events x).id in
    let po a b = USet.mem structure.po (a, b) in
    let locks = of_type Lock and unlocks = of_type Unlock in
    (* The lock's depth just after [x]: the locks of it [po]-up to and including
       [x], less the unlocks. *)
    let depth x =
      let count l =
        List.length (List.filter (fun y -> key y = key x && (y = x || po y x)) l)
      in
        count locks - count unlocks
    in
    let outermost = List.filter (fun l -> depth l = 1) locks in
    let release l =
      List.find_opt
        (fun u ->
          key u = key l
          && po l u
          && depth u = 0
          && not
               (List.exists
                  (fun x ->
                    x <> u && key x = key l && po l x && po x u && depth x = 0
                  )
                  unlocks
               )
        )
        unlocks
    in
    let sections = List.map (fun l -> (l, release l)) outermost in
    let keys = List.sort_uniq compare (List.map key locks) in
    let orders_on k =
      let on_k = List.filter (fun (l, _) -> key l = k) sections in
      let before (la, _) (lb, ub) = po la lb || (la <> lb && ub = None) in
        Algorithms.linear_extensions before on_k
    in
    let rec edges = function
      | (_, Some u) :: ((l, _) :: _ as rest) -> (u, l) :: edges rest
      | _ :: rest -> edges rest
      | [] -> []
    in
      List.fold_left
        (fun acc k ->
          List.concat_map
            (fun order -> List.map (fun prefix -> edges order @ prefix) acc)
            (orders_on k)
        )
        [ [] ] keys
      |> List.map USet.of_list

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

    (* release = ([W_rel] ∪ [F_rel];po);rs

       [W_rel], here and in [bob], is a write of mode [rel] or stronger, and
       [R_acq] a read of mode [acq] or stronger: IMM's modes are ordered
       [rlx ⊑ acq, rel ⊑ acqrel ⊑ sc]. They were matched exactly, so an [sc]
       write did not release, nor an [sc] read acquire, and message passing
       through [sc] accesses came out allowed. *)
    let release =
      let w_rel =
        ModelUtils.match_events events e Write (Some Release) (Some ">") None
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
        ModelUtils.match_events events e Read (Some Acquire) (Some ">") None
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
            po;
            ModelUtils.match_events events e Write (Some Release) (Some ">")
              None;
          ]
      in
      let p2 =
        URelation.compose
          [
            ModelUtils.match_events events e Read (Some Acquire) (Some ">")
              None;
            po;
          ]
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
            ModelUtils.match_events events e Write (Some Release) (Some ">")
              None;
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
  let data_races = None

  (* IMM's release sequence continues through [po ∩ loc]. *)
  let elidable = ModelUtils.release_elidable_by_release
  let allows_thin_air = false
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

      - [Rc11]: [[W];(sb ∩ loc)?;[W_rlx⁺];(rf;rmw)*], as herd's [rc11.cat].
      - [Rc17]: [[W_rlx⁺];(rf;rmw)*], C++17's, where a later same-thread relaxed
        store no longer continues the sequence ([rc17.cat]).
      - [Cpp11]: RC11's, less the pairs another thread's write intervenes in,
        [rs \ (coe;coe)] ([cpp11.cat]). It depends on the coherence order, so
        [hb] is built per candidate order rather than once per execution. *)
  type release_sequence = Rc11 | Rc17 | Cpp11

  type t = {
    with_consume : bool;
    name : string;
    release_sequence : release_sequence;
    allocations_are_writes : bool;
        (** RC11z: allocations and deallocations are writes to the location they
            allocate or free, ordered by [co] with the stores to it. *)
    no_thin_air : [ `Hb_rf | `Sb_rf | `None ];
        (** [acyclic(hb ∪ rf)], as MoRDor's RC11 has always checked it, or the
            literal [acyclic(sb ∪ rf)] of Ou and Demsky's load-store ordering.
            The two agree whenever [hb] is built from [sb], [rf] and [rmw].
            [`None] for the standard's models, which have no such axiom -- but
            see {!c11}. *)
    fragment : (string * (event -> bool)) option;
        (** The programs the model is defined on, described and as a test of
            each event; [None] for every program. A model stated over a fragment
            of RC11 refuses a program with an event outside it, rather than
            answering as RC11 where it says nothing. *)
    sc : [ `Psc | `C11 ];
        (** [acyclic psc], RC11's repaired SC of P0668, or the conditions C11
            places on its total order [S] over SC events, in the partial form of
            herd's [c11_partialSC.cat] (Batty, Donaldson and Wickerson, POPL
            2016). *)
  }

  let base =
    {
      with_consume = false;
      name = "rc11";
      release_sequence = Rc11;
      allocations_are_writes = false;
      no_thin_air = `Hb_rf;
      fragment = None;
      sc = `Psc;
    }

  let default = base
  let with_consume = { base with with_consume = true; name = "rc11c" }
  let rc17 = { base with name = "rc17"; release_sequence = Rc17 }
  let rc11z = { base with name = "rc11z"; allocations_are_writes = true }

  (** Ou and Demsky's load-store ordering criterion, [acyclic(sb ∪ rf)], over
      the C/C++11 model it constrains. *)
  let od_lso =
    {
      base with
      name = "od-lso";
      release_sequence = Cpp11;
      no_thin_air = `Sb_rf;
    }

  (** The C/C++ standard's model by revision, as the zoo's [cpp11.cat] and
      [cpp17.cat] state it, but with C11's own SC for C11 and C++17, which keep
      the SC of C++11 until P0668 repaired it in C++20. The cat files take
      RC11's [psc] for both, and so forbid IRIW with SC fences, which C11
      allows.

      None of the three has a thin-air axiom, and all three allow
      out-of-thin-air executions ([allows_thin_air]): when one is asked, the
      generator keeps executions with a cycle in [dp ∪ ppo ∪ rf], which every
      other model then rejects itself. *)
  let c11 =
    {
      base with
      name = "c11";
      release_sequence = Cpp11;
      no_thin_air = `None;
      sc = `C11;
    }

  (** C++17: C11 with release sequences continued only by RMWs (P0982). *)
  let c17 = { c11 with name = "c17"; release_sequence = Rc17 }

  (** C++20: C++17's release sequences and RC11's SC (P0668).

      Not the zoo's [cpp2w.cat], which adds [acyclic(tecotsb ∪ rb)] for
      [tecotsb = ([A];eco;[A])⁺;sb] from a later draft. That axiom forbids
      message passing over relaxed accesses, which C++20 allows: herd7 answers
      MP+rlx Never under [cpp2w.cat] and Sometimes under [cpp17.cat]. *)
  let c20 = { c17 with name = "c20"; sc = `Psc }

  (** The mode of an event of its own type: a read's, a write's or a fence's. *)
  let mode (ev : event) =
    match ev.typ with
    | Read -> Some ev.rmod
    | Write -> Some ev.wmod
    | Fence -> Some ev.fmod
    | _ -> None

  (** Operational RC11 (Dang, Jourdan, Kaiser and Dreyer, POPL 2020): RC11
      without SC accesses and SC fences, which ORC11 does not have. Its paper
      sketches the correspondence with that fragment of RC11, and states it in
      one direction: a program RC11 considers racy, ORC11 does too. MoRDor has
      no consume in ORC11 either, nor locks. *)
  let orc11 =
    {
      base with
      name = "orc11";
      fragment =
        Some
          ( "programs without SC accesses, SC fences, consume reads or locks",
            fun ev ->
              match (ev.typ, mode ev) with
              | (Lock | Unlock), _ -> false
              | _, Some (SC | Consume) -> false
              | _ -> true
          );
    }

  (** The release-acquire/relaxed fragment of RC11 that Doherty, Dongol,
      Wehrheim and Derrick (PPoPP 2019) give an operational semantics for and
      prove equivalent to: relaxed, release and acquire accesses and
      release-acquire updates. No non-atomic or SC accesses, no fences. *)
  let rar =
    {
      base with
      name = "rar";
      fragment =
        Some
          ( "programs whose accesses are relaxed, release, acquire or \
             release-acquire, with no fences, non-atomic or SC accesses, or \
             locks",
            fun ev ->
              match (ev.typ, mode ev) with
              | (Lock | Unlock | Fence), _ -> false
              | ( (Read | Write),
                  Some (Relaxed | Acquire | Release | ReleaseAcquire) ) ->
                  true
              | (Read | Write), _ -> false
              | _ -> true
          );
    }
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

  (** [build_hb ~co ...] is [hb = (sw ∪ sb)⁺]. [co] is asked only by the [Cpp11]
      release sequence. *)
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
          Some (build_hb ~events ~e ~sb ~rf ~rmw ~loc_restrict ~thread_index ())
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

  (** C11's SC: the conditions S1--S7 of the standard on a total order [S] of
      the SC events, as herd's [c11_partialSC.cat] states them for a partial
      one: the union [scp] of what each condition puts before what, restricted
      to SC events, is acyclic.

      - S1 [hb]; S2 [fsb?;mo;sbf?]; S3 [rf⁻¹;[SC];mo]; S4 [rf⁻¹;hbl;[W]]
      - S5 [fsb;fr]; S6 [fr;sbf]; S7 [fsb;fr;sbf]

      with [fsb = [F];sb] and [sbf = sb;[F]] over fences of any mode. The fences
      in S2 and S5--S7 order SC events through the relaxed accesses beside them,
      which is too weak to forbid IRIW with SC fences: P0668's defect. *)
  let c11_sc_consistent x =
    let { sb; e; events; loc_restrict; rfi; _ } = x.cache in
    let co = x.co and hb = Lazy.force x.hb and fr = Lazy.force x.rb in
    let opt = URelation.reflexive_closure e in
    let fences = ModelUtils.match_events events e Fence None None None in
    let fsb = URelation.compose [ fences; sb ] in
    let sbf = URelation.compose [ sb; fences ] in
    let sc =
      USet.union
        (ModelUtils.match_events events e Read (Some SC) None None)
        (ModelUtils.match_events events e Write (Some SC) None None)
      |> USet.union (ModelUtils.match_events events e Fence (Some SC) None None)
    in
    let w = ModelUtils.match_events events e Write None None None in
    let scp =
      List.fold_left USet.union hb
        [
          URelation.compose [ opt fsb; co; opt sbf ];
          URelation.compose [ rfi; sc; co ];
          URelation.compose [ rfi; loc_restrict hb; w ];
          URelation.compose [ fsb; fr ];
          URelation.compose [ fr; sbf ];
          URelation.compose [ fsb; fr; sbf ];
        ]
    in
      URelation.compose [ sc; scp; sc ]
      |> USet.filter (fun (a, b) -> a <> b)
      |> URelation.acyclic

  (** The reads and writes of [e]. *)
  let accesses events e =
    USet.filter
      (fun id ->
        match Hashtbl.find_opt events id with
        | Some { typ = Read | Write; _ } -> true
        | _ -> false
      )
      e

  let is_atomic events id =
    match Hashtbl.find_opt events id with
    | Some { typ = Read; rmod; _ } -> rmod <> Nonatomic
    | Some { typ = Write; wmod; _ } -> wmod <> Nonatomic
    | _ -> false

  (** [dr = (cnf ∩ ext) \ (hb ∪ hb⁻¹ ∪ A×A)], with [cnf] the pairs of accesses
      to one location of which one writes. Initial writes are [sb] before every
      thread, so [hb] orders them before everything they conflict with. Each
      race is given once, smaller event first. *)
  let data_races x =
    let { events; e; thread_index; loc_restrict; _ } = x.cache in
    let hb = Lazy.force x.hb in
    let acc = accesses events e in
    let writes id =
      match Hashtbl.find_opt events id with
      | Some { typ = Write; _ } -> true
      | _ -> false
    in
      URelation.cross acc acc
      |> USet.filter (fun (a, b) ->
          a < b
          && (writes a || writes b)
          && not (is_atomic events a && is_atomic events b)
      )
      |> loc_restrict
      |> USet.filter (fun (a, b) ->
          (not (ModelUtils.same_thread thread_index a b))
          && (not (USet.mem hb (a, b)))
          && not (USet.mem hb (b, a))
      )

  let axioms =
    [
      ("rmw ∩ (rb;co) = ∅", atomicity);
      ("hb;eco ∪ hb is irreflexive", coherence);
    ]
    @
    match Config.config.sc with
    | `Psc -> [ ("psc is acyclic", sc_consistent) ]
    | `C11 -> [ ("scp is acyclic on SC events", c11_sc_consistent) ]

  let check_coherence cache co = holds axioms (candidate cache co)

  let check_thin_air (cache : cache) (execution : symbolic_execution) =
    let { hb; rf; sb; _ } = cache in
      match (Config.config.no_thin_air, hb) with
      | `None, _ -> true
      | `Hb_rf, Some hb -> CoherenceChecks.thin_air_check ~hb ~rf ()
      | _ -> CoherenceChecks.thin_air_check ~hb:sb ~rf ()

  let data_races = Some data_races

  (* C++17's release sequence stops at a relaxed store of the writer's thread,
     so eliding the release store before it changes nothing. *)
  let elidable =
    match Config.config.release_sequence with
    | Rc11 | Cpp11 -> ModelUtils.release_elidable_by_release
    | Rc17 -> ModelUtils.elidable_always

  (* The standard's models have no thin-air axiom (RC11Config.no_thin_air). *)
  let allows_thin_air = Config.config.no_thin_air = `None
  let uses_co = true
  let orders_allocations = Config.config.allocations_are_writes

  (* A model over a fragment refuses a program with an event outside it. *)
  let check_program (structure : symbolic_event_structure) =
    match Config.config.fragment with
    | None -> Ok ()
    | Some (description, inside) -> (
        let outside =
          Hashtbl.fold
            (fun _ (ev : event) acc -> if inside ev then acc else ev :: acc)
            structure.events []
          |> List.sort (fun (a : event) (b : event) -> compare a.label b.label)
        in
          match outside with
          | [] -> Ok ()
          | ev :: _ ->
              Error
                (Printf.sprintf
                   "%s is defined on %s; event %d (%s) is outside that \
                    fragment."
                   (String.uppercase_ascii Config.config.name)
                   description ev.label (show_event_type ev.typ)
                )
      )
  let compute_dependencies _ _ _ _ _ = USet.create ()
end

module SMRD : MEMORY_MODEL = struct
  type cache = {
    rf : (int * int) uset;
    rfi : (int * int) uset;
    hbs : (int * int) uset list;
        (** [hb] under each lock order the execution admits; none when it admits
            none. *)
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

    (* hb = (ppo ∪ dp ∪ sw ∪ [Unlock];lo;[Lock])⁺, for each lock order [lo].

       Lock and unlock are acquire and release in [ppo], so a section's accesses
       lie between its lock and unlock; the edge from one section's unlock to
       the next's lock then orders the whole of each before the whole of the
       next. An execution is coherent when some lock order makes it so. *)
    let base = USet.inplace_union ~into:(USet.union ppo dp) sw in
    let hbs =
      List.map
        (fun lo -> USet.union base lo |> URelation.transitive_closure)
        (ModelUtils.lock_orders structure execution.e)
    in

    { rf; rfi; hbs; rmw }

  type candidate = cache * (int * int) uset

  let candidate cache co = (cache, co)

  let axioms =
    [
      ( "rmw ∩ (rb;co) = ∅",
        fun ({ rf; rfi; rmw; _ }, co) ->
          CoherenceChecks.rmw_atomicity ~rf ~rfi ~rmw ~co ()
      );
      ( "hb;eco ∪ hb is irreflexive, for some lock order",
        fun ({ rf; rfi; hbs; _ }, co) ->
          List.exists
            (fun hb -> CoherenceChecks.coherence_axiom ~rf ~rfi ~co ~hb ())
            hbs
      );
    ]

  let check_coherence cache co = holds axioms (candidate cache co)

  let check_thin_air cache execution =
    let { rf; hbs; _ } = cache in
      List.exists (fun hb -> CoherenceChecks.thin_air_check ~hb ~rf ()) hbs

  let data_races = None

  (* [sw = [W_rel];rf;[R_acq]], with no release sequence to break. *)
  let elidable = ModelUtils.elidable_always
  let allows_thin_air = false
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
  let data_races = None
  let elidable = ModelUtils.elidable_always
  let allows_thin_air = false
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
    filter on sMRD's candidate executions, which have no cycle in
    [dp ∪ ppo ∪ rf] unless a model of the run allows out-of-thin-air
    executions; none of these does. And the distributed consistency models are
    stated over histories; reading one as a shared-memory predicate needs an
    encoding, which each module's comment states. *)

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
        (** Stores, and the initial event when it is one: event [0] is the write
            every uninitialised location reads from. *)
    r : (int * int) uset;  (** [[R]] *)
    w : (int * int) uset;  (** [[W]] *)
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
      let po =
        USet.filter (fun (a, b) -> USet.mem e a && USet.mem e b) structure.po
      in
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

  (** [po] between threads: what a block's threads inherit from the code before
      it, and what the code after it inherits from them. The initialising stores
      are the case that matters. They are program order, not another process's
      writes, and a view that could place [x := 0] after a thread's [x := 1]
      would let a reader see 1 and then 0. *)
  let fork_order v = external_ v v.po

  (** [co], with the initial event first at every location. The search puts it
      there only when a read reads from it and two writes exist, so a single
      store and a read of the initial value came with no order between them. *)
  let co v co =
    match v.initial with
    | None -> co
    | Some i ->
        let co = USet.clone co in
          USet.iter
            (fun w -> if w <> i then USet.add co (i, w) |> ignore)
            v.writes;
          co

  (** [fr = (rf⁻¹;co) \ id]: from a read to the writes after the one it read. *)
  let fr v co =
    URelation.compose [ v.rfi; co ] |> USet.filter (fun (a, b) -> a <> b)

  let atomicity v co =
    USet.is_empty v.rmw
    || CoherenceChecks.rmw_atomicity ~rf:v.rf ~rfi:v.rfi ~rmw:v.rmw ~co ()

  let union rels =
    List.fold_left
      (fun acc r -> USet.inplace_union ~into:acc r)
      (USet.create ()) rels

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

(** Helpers for the models below: a model refusing a program outside the
    fragment it is defined on, and the data races of an execution under an
    [hb]. *)

(** [refuse_outside ~name ~description inside structure] refuses the program
    of [structure] when some event is not [inside], naming the first. *)
let refuse_outside ~name ~description inside
    (structure : symbolic_event_structure) =
  let outside =
    Hashtbl.fold
      (fun _ (ev : event) acc -> if inside ev then acc else ev :: acc)
      structure.events []
    |> List.sort (fun (a : event) (b : event) -> compare a.label b.label)
  in
    match outside with
    | [] -> Ok ()
    | ev :: _ ->
        Error
          (Printf.sprintf "%s is defined on %s; event %d (%s) is outside it."
             name description ev.label (show_event_type ev.typ)
          )

(** The mode of an access or fence: [None] for any other event. *)
let mode_of (ev : event) =
  match ev.typ with
  | Read -> Some ev.rmod
  | Write -> Some ev.wmod
  | Fence -> Some ev.fmod
  | _ -> None

(** The accesses of [v] in a mode [atomic] accepts. *)
let accesses_in (v : Vocab.t) atomic =
  USet.filter
    (fun id ->
      match Option.bind (Hashtbl.find_opt v.events id) mode_of with
      | Some m -> atomic m
      | None -> false
    )
    (USet.union v.reads v.writes)

(** [races v ~hb ~atomic]: pairs of accesses to one location, of two threads,
    one a write and not both [atomic], that [hb] leaves unordered. The initial
    event is [po] before everything, so it races with nothing. *)
let races (v : Vocab.t) ~hb ~atomic =
  let accesses =
    USet.union v.reads v.writes
    |> USet.filter (fun id -> Some id <> v.initial)
  in
    URelation.cross accesses accesses
    |> USet.filter (fun (a, b) ->
        a < b
        && (USet.mem v.writes a || USet.mem v.writes b)
        && (not (USet.mem atomic a && USet.mem atomic b))
        && USet.mem v.same_loc (a, b)
        && (not (ModelUtils.same_thread v.thread_index a b))
        && (not (USet.mem hb (a, b)))
        && not (USet.mem hb (b, a))
    )

let no_locks (ev : event) = ev.typ <> Lock && ev.typ <> Unlock

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
module AxiomaticWith (A : sig
  val name : string
  val uses_co : bool

  type derived

  val prepare : Vocab.t -> derived
  val axioms : (string * (derived axiomatic_candidate -> bool)) list

  val data_races :
    (derived axiomatic_candidate -> (int * int) uset) option

  val allows_thin_air : bool
  val check_program : symbolic_event_structure -> (unit, string) result
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
  let data_races = A.data_races

  let elidable = ModelUtils.elidable_always

  let allows_thin_air = A.allows_thin_air
  let uses_co = A.uses_co
  let orders_allocations = false
  let check_program = A.check_program
  let compute_dependencies _ _ _ _ _ = USet.create ()
end

(** {!AxiomaticWith} for a model with no race clause, no thin air, and every
    program in its domain. *)
module Axiomatic (A : sig
  val name : string
  val uses_co : bool

  type derived

  val prepare : Vocab.t -> derived
  val axioms : (string * (derived axiomatic_candidate -> bool)) list
end) : MEMORY_MODEL = AxiomaticWith (struct
  include A

  let data_races = None
  let allows_thin_air = false
  let check_program _ = Ok ()
end)

(** Sequential consistency: [acyclic(po ∪ rf ∪ co ∪ fr)], with herd's [sc.cat]
    atomicity for RMWs. *)
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
      [ppo = [R];po;[R] ∪ [M];po;[W] ∪ [M];po;[F];po;[M] ∪ implied] and
      [implied = [W];po;[R];[A] ∪ [A];[W];po;[R]], the store buffer flushed by
      an atomic instruction.

    Every fence is a full fence: on x86 C11's fences compile to [mfence]. *)
module TSOAxioms (N : sig
  val name : string

  val java_volatiles : bool
  (** BMM (Demange et al., POPL 2013), the buffered memory model for Java:
      TSO, where a store and a later load stay in order when either is
      volatile, which MoRDor writes as mode [sc]. Locks are refused. *)
end) =
AxiomaticWith (struct
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
    let ppo =
      if not N.java_volatiles then ppo
      else
        let vol = URelation.identity (accesses_in v (fun m -> m = SC)) in
          Vocab.union
            [
              ppo;
              URelation.compose [ vol; pow_r ];
              URelation.compose [ pow_r; vol ];
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

  let data_races = None
  let allows_thin_air = false

  let check_program =
    if N.java_volatiles then
      refuse_outside ~name:(String.uppercase_ascii N.name)
        ~description:"programs without locks" no_locks
    else fun _ -> Ok ()
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

    - [sw = [W_rel⁺];rf;[R_acq⁺]] and [hb = (po ∪ sw)⁺]; MoRDor's [po] already
      puts the initialisation before every thread
    - RA: [irreflexive hb], [irreflexive co;hb], [irreflexive co;hb;rf⁻¹],
      atomicity
    - SRA: RA with [acyclic(hb ∪ co)] for [irreflexive co;hb]
    - WRA: [irreflexive hb], [irreflexive (hb ∩ loc);[W];hb;rf⁻¹], and no two
      RMWs reading one write. [co] plays no part.
    - CC, Bouajjani et al.'s weak causal consistency, which Lahav and Boker show
      WRA equivalent to: WRA's axioms with every access synchronising,
      [sw = rf]. CC's histories have no RMWs, so it has no atomicity axiom. *)
module ReleaseAcquire (F : sig
  val name : string
  val variant : [ `RA | `SRA | `WRA | `CC ]
end) =
Axiomatic (struct
  let name = F.name

  let uses_co =
    match F.variant with
    | `RA | `SRA -> true
    | `WRA | `CC -> false

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
              ModelUtils.match_events v.events v.e Read (Some Acquire)
                (Some ">") None;
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

    A process's view is a total order over every write of the execution and that
    process's own reads, in which each read reads the latest write to its
    location before it. The models differ in what every view must respect:

    - Local: the process's own program order, and nothing else
    - Slow: also each process's writes to a location, in the order issued
    - PRAM: also each process's writes, in the order issued
    - Causal: also the causal order [(po ∪ rf)⁺], Ahamad et al.'s causal memory
    - PC: PRAM's, and one order of the writes to each location shared by every
      view -- that order is the candidate [co]

    A process is a thread. The initial event is before everything in every view,
    and so is program order between threads: the stores before a parallel block
    precede its threads' events, as the threads' events precede what follows the
    block. Nothing here makes an RMW atomic: the histories these models are
    stated over have none. Existence of a view is decided by search over the
    order its events are placed in, memoised on the events placed and the latest
    write at each location. *)
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
             "Memory model %s: a view of %d events is more than the search can \
              represent."
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
            (fun (a, b) ->
              if USet.mem own a && USet.mem own b then add_pred (a, b)
            )
            v.po;
          USet.iter add_pred d.precedence;
          USet.iter add_pred co;
          let locs =
            Array.map
              (fun id ->
                Hashtbl.find_opt d.loc_of id |> Option.value ~default:id
              )
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
                    USet.values v.rf |> List.find_opt (fun (_, r) -> r = id)
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
                    placed land (1 lsl i) = 0
                    && preds.(i) land placed = preds.(i)
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
      session's own: a block's threads follow what came before it, and the code
      after the join follows them.
    - POCA: [irreflexive co;hbo] -- arbitration respects it
    - return values: [irreflexive fr;hbo] -- nothing [hbo]-before a read is
      arbitrated after the write it read

    [vis] is taken least, which is the choice every axiom here is weakest under.
    Eventual consistency's liveness clause says nothing of a finite execution.
*)
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

(** Terry et al.'s session guarantees (PDIS 1994), in Viotti and Vukolić's form
    (ACM CSUR 2016) over an arbitration order and a visibility per read.

    A session is a thread. Visibility is taken least, closed under what the
    guarantees demand:

    [vis = (rf ∪ RYW) ; MR?], with [RYW = [W];po_int;[R]] and [MR = po_int;[R]],
    each present when its guarantee is. MW and WFR constrain arbitration and not
    visibility.

    Each reader has its own arbitration: a replica applies other sessions'
    writes in an order of its own. It exists when these are acyclic, with the
    initial event first and writes in program order across a fork or join:

    - return values: [((vis ∩ loc);[R_p];rf⁻¹) \ id], every write a read of
      session [p] saw is before the one it read
    - MW: [[W];po_int;[W]], every session's writes in the order issued
    - WFR: [vis;po_int;[W]], a session's writes after what it had read

    Arbitration is per reader rather than Viotti and Vukolić's one global order.
    With one order, RYW forbids two threads each reading the other's write after
    writing their own, which PRAM as Steinke and Nutt state it allows, and the
    zoo's edge from PRAM to RYW would not hold.

    A consequence worth knowing: MW alone forbids nothing. Least visibility
    gives a read only the write it read, so no reader has two writes of one
    session to arbitrate between, and the order MW adds can close no cycle. WFR
    can, since its edges run between sessions: load buffering orders each
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
        if F.ryw then
          Vocab.union [ v.rf; URelation.compose [ v.w; po_int; v.r ] ]
        else USet.clone v.rf
      in
        if F.mr then
          URelation.compose
            [
              seen;
              URelation.reflexive_closure v.reads
                (URelation.compose [ po_int; v.r ]);
            ]
        else seen
    in
    let initial_first =
      match v.initial with
      | Some i ->
          USet.filter (fun w -> w <> i) v.writes |> USet.map (fun w -> (i, w))
      | None -> USet.create ()
    in
    let arbitration =
      Vocab.union
        [
          initial_first;
          URelation.compose [ v.w; Vocab.fork_order v; v.w ];
          (if F.mw then mw else USet.create ());
          ( if F.wfr then URelation.compose [ vis; po_int; v.w ]
            else USet.create ()
          );
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
              |> USet.filter (fun (w, s) -> w <> s)
            )
        )
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
    undefined-behaviour fold and allocation. On a program with none of those --
    every access to a named global, nothing allocated or freed -- the two
    compute the same dependencies, and this is sMRD. On any other program sMRD
    admits executions MRD does not, and nothing here can tell which, so the
    model refuses the program. The undefined-behaviour fold is off under this
    model's name. *)

(** Sequential consistency for data-race-free programs, and catch-fire for the
    rest: DRFx (Marino et al., PLDI 2010), whose runtime raises an exception at
    a race, and DeNovoSync (Sung and Adve, ASPLOS 2015), which adopts the DRF
    model of C++ and Java. Each admits the SC executions, and a race in one is
    reported as undefined behaviour, an exception being no outcome either. A
    race is between accesses of two threads to one location, one a write and
    one non-atomic, that [hb = (po ∪ [A];rf;[A])⁺] does not order: atomic
    accesses, any but [na], are the synchronisation operations. Locks are
    refused, the SC axioms here having no lock order. *)
module DRFSC (N : sig
  val name : string
end) =
AxiomaticWith (struct
  let name = N.name
  let uses_co = true

  type derived = {
    sc : (int * int) uset;  (** [po ∪ rf] *)
    hb : (int * int) uset;
    atomic : int uset;
  }

  let prepare (v : Vocab.t) =
    let atomic = accesses_in v (fun m -> m <> Nonatomic) in
    let a = URelation.identity atomic in
    let hb =
      URelation.transitive_closure
        (Vocab.union [ v.po; URelation.compose [ a; v.rf; a ] ])
    in
      { sc = Vocab.union [ v.po; v.rf ]; hb; atomic }

  let axioms =
    [
      ("rmw ∩ (fr;co) = ∅", fun x -> Vocab.atomicity x.v x.co);
      ( "po ∪ rf ∪ co ∪ fr is acyclic",
        fun x ->
          URelation.acyclic (Vocab.union [ x.d.sc; x.co; Lazy.force x.fr ])
      );
    ]

  let data_races = Some (fun x -> races x.v ~hb:x.d.hb ~atomic:x.d.atomic)
  let allows_thin_air = false

  let check_program =
    refuse_outside ~name:(String.uppercase_ascii N.name)
      ~description:"programs without locks" no_locks
end)

(** CRC, the C11 fragment of Dodds, Batty and Gotsman's compositional
    semantics (ESOP 2018): release-acquire and non-atomic accesses, and SC
    fences. Every atomic access is release-acquire, so [rf] between atomic
    accesses synchronises; a fence is a load-link/store-conditional pair on one
    fence location, so the fences are totally ordered and each happens before
    the next. Over [hb = (po ∪ [A];rf;[A] ∪ fences)⁺], RA's axioms (hb acyclic,
    [co;hb] and [co;hb;rf⁻¹] irreflexive, atomicity) and [rf;hb] irreflexive,
    for a non-atomic read. A race on a non-atomic access is undefined
    behaviour. Accesses in [acq], [rel] or [ra] mode are atomic and every
    other but [sc] non-atomic; SC accesses and fences other than SC fences are
    refused, and so are locks. *)
module CRC = AxiomaticWith (struct
  let name = "crc"
  let uses_co = true

  type derived = {
    base : (int * int) uset;  (** [po ∪ [A];rf;[A]] *)
    fences : int list;
    atomic : int uset;
  }

  let atomic_mode = function
    | Acquire | Release | ReleaseAcquire -> true
    | _ -> false

  let prepare (v : Vocab.t) =
    let atomic = accesses_in v atomic_mode in
    let a = URelation.identity atomic in
    let fences =
      USet.filter
        (fun id ->
          match Hashtbl.find_opt v.events id with
          | Some { typ = Fence; fmod = SC; _ } -> true
          | _ -> false
        )
        v.e
      |> USet.values |> List.sort compare
    in
      {
        base = Vocab.union [ v.po; URelation.compose [ a; v.rf; a ] ];
        fences;
        atomic;
      }

  (** [hb] for each order of the fences that extends [po ∪ sw]. *)
  let hbs (x : derived axiomatic_candidate) =
    let base_hb = URelation.transitive_closure x.d.base in
      Algorithms.linear_extensions
        (fun a b -> USet.mem base_hb (a, b))
        x.d.fences
      |> List.map (fun order ->
          let chain =
            let rec pairs = function
              | a :: (b :: _ as rest) -> (a, b) :: pairs rest
              | _ -> []
            in
              USet.of_list (pairs order)
          in
            URelation.transitive_closure (Vocab.union [ x.d.base; chain ])
      )

  let consistent (x : derived axiomatic_candidate) hb =
    URelation.is_irreflexive hb
    && URelation.is_irreflexive (URelation.compose [ x.co; hb ])
    && URelation.is_irreflexive (URelation.compose [ x.co; hb; x.v.rfi ])
    && URelation.is_irreflexive (URelation.compose [ x.v.rf; hb ])

  let axioms =
    [
      ("rmw ∩ (fr;co) = ∅", fun x -> Vocab.atomicity x.v x.co);
      ( "some order of the fences makes hb acyclic, and co;hb, co;hb;rf⁻¹ \
         and rf;hb irreflexive",
        fun x -> List.exists (consistent x) (hbs x)
      );
    ]

  (* The races under some consistent order of the fences that has any. *)
  let data_races =
    Some
      (fun x ->
        List.filter (consistent x) (hbs x)
        |> List.map (fun hb -> races x.v ~hb ~atomic:x.d.atomic)
        |> List.find_opt (fun r -> USet.size r > 0)
        |> Option.value ~default:(USet.create ())
      )

  let allows_thin_air = false

  let check_program =
    refuse_outside ~name:"CRC"
      ~description:
        "release-acquire and non-atomic accesses and SC fences, without SC \
         accesses, other fences or locks"
      (fun ev ->
        no_locks ev
        &&
        match (ev.typ, mode_of ev) with
        | Fence, Some m -> m = SC
        | (Read | Write), Some SC -> false
        | _ -> true
      )
end)

(** The OCaml memory model (Dolan, Sivaramakrishnan and Madhavapeddy, PLDI
    2018, §6). Atomicity belongs to a location in OCaml, an [Atomic.t]; here an
    access in mode [sc] is atomic and any other non-atomic, and [rf] and [co]
    order only between two atomic accesses. [hb] is the transitive closure of
    [po], the initial writes before everything, and [co ∪ rf] between atomic
    accesses to one location:

    - Causality: [hb ∪ rf ∪ fr_at] is acyclic, [fr_at] being [fr] between
      atomic accesses, so load buffering is forbidden
    - CoWW: [hb;co] is irreflexive
    - CoWR: [hb;fr] is irreflexive

    A race is defined, not undefined, and non-atomic reads need not be coherent:
    nothing orders two reads of a location in one thread. Fences, locks and
    release/acquire modes are refused. *)
module OCaml = AxiomaticWith (struct
  let name = "ocaml"
  let uses_co = true

  type derived = { atomic : (int * int) uset  (** [[A]] *) }

  let prepare (v : Vocab.t) =
    { atomic = URelation.identity (accesses_in v (fun m -> m = SC)) }

  let hb (x : derived axiomatic_candidate) =
    let a = x.d.atomic in
    let com =
      x.v.loc_restrict
        (URelation.compose [ a; Vocab.union [ x.co; x.v.rf ]; a ])
    in
      URelation.transitive_closure (Vocab.union [ x.v.po; com ])

  let axioms =
    [
      ( "hb ∪ rf ∪ fr_at is acyclic",
        fun x ->
          let fr_at =
            URelation.compose [ x.d.atomic; Lazy.force x.fr; x.d.atomic ]
          in
            URelation.acyclic (Vocab.union [ hb x; x.v.rf; fr_at ])
      );
      ( "hb;co is irreflexive",
        fun x -> URelation.is_irreflexive (URelation.compose [ hb x; x.co ])
      );
      ( "hb;fr is irreflexive",
        fun x ->
          URelation.is_irreflexive
            (URelation.compose [ hb x; Lazy.force x.fr ])
      );
    ]

  let data_races = None
  let allows_thin_air = false

  let check_program =
    refuse_outside ~name:"OCAML"
      ~description:
        "programs whose accesses are atomic ([sc]) or non-atomic, without \
         fences or locks"
      (fun ev ->
        no_locks ev
        &&
        match (ev.typ, mode_of ev) with
        | Fence, _ -> false
        | (Read | Write), Some (SC | Nonatomic | Relaxed) -> true
        | (Read | Write), _ -> false
        | _ -> true
      )
end)

(** Java Access Modes (Bender and Palsberg, OOPSLA 2019), the herd model of
    their Appendix A. Modes: [na] is Java's plain, [rlx] (and so a plain [:=])
    opaque, [acq], [rel] and [ra] release-acquire, [sc] volatile.

    The coherence order is the model's own, partial and derived from a
    visibility order [vo = (rf ∪ svo ∪ ra ∪ push ∪ pushto;push)⁺ ∪ po-loc] by
    the rules coww, cowr, corw, corr, cofw, coinit, and for RMWs cormwtotal and
    the recursive cormwexcl; the axioms are [acyclic co] and
    [acyclic ((po ∪ rf) ∩ (opq × opq))]. So plain accesses are coherent but may
    be out of thin air, which the model allows. The final writes cofw orders
    the other writes before are the last in the candidate coherence order, as
    in herd. The trace order [to], a linearisation of the accesses, matters
    only for full fences, volatiles and RMWs, and is then searched.

    The paper's [filters.cat], which turns fences into specified orders, is not
    published; here, after the JDK: a release fence orders accesses before it
    before writes after it, an acquire fence reads before it before accesses
    after it, and a full ([sc]) fence is a push order. Java has no undefined
    behaviour, so a race is defined. Locks and consume are refused. *)
module JAM = AxiomaticWith (struct
  let name = "jam"
  let uses_co = true

  type derived = {
    nodes : int list;  (** the accesses, less the initial event *)
    loc : int -> int -> bool;  (** one location, the initial event at all *)
    writes : int uset;  (** with the initial event *)
    base : (int * int) uset;  (** [rf ∪ svo ∪ ra ∪ push] *)
    po_loc : (int * int) uset;
    push : (int * int) uset;
    into : (int * int) uset;
    needs_to : bool;
    causality : bool;
  }

  let in_modes (v : Vocab.t) modes =
    accesses_in v (fun m -> List.mem m modes) |> URelation.identity

  let fences_in (v : Vocab.t) modes =
    USet.filter
      (fun id ->
        match Hashtbl.find_opt v.events id with
        | Some { typ = Fence; fmod; _ } -> List.mem fmod modes
        | _ -> false
      )
      v.e
    |> URelation.identity

  let prepare (v : Vocab.t) =
    let initial = v.initial in
    let mem = USet.union v.reads v.writes in
    let m = URelation.identity mem in
    let opq = accesses_in v (fun m -> m <> Nonatomic) in
    let rel = URelation.compose [ v.w; in_modes v [ Release; ReleaseAcquire ] ]
    and acq = URelation.compose [ v.r; in_modes v [ Acquire; ReleaseAcquire ] ]
    and vol = in_modes v [ SC ] in
    let after f = URelation.compose [ v.po; f; v.po ] in
    let svo =
      Vocab.union
        [
          URelation.compose [ m; after (fences_in v [ Release ]); v.w ];
          URelation.compose [ v.r; after (fences_in v [ Acquire ]); m ];
          URelation.compose [ m; after (fences_in v [ ReleaseAcquire ]); m ];
        ]
    in
    let spush = URelation.compose [ m; after (fences_in v [ SC ]); m ] in
    let ra =
      Vocab.union
        [ URelation.compose [ v.po; rel ]; URelation.compose [ acq; v.po ] ]
    in
    let volint =
      Vocab.union
        [
          URelation.compose [ v.po; URelation.compose [ vol; v.r ] ];
          URelation.compose [ URelation.compose [ vol; v.w ]; v.po ];
        ]
    in
    let push = Vocab.union [ spush; volint ] in
    let loc a b =
      Some a = initial || Some b = initial || USet.mem v.same_loc (a, b)
    in
    let causal =
      Vocab.union [ v.po; v.rf ]
      |> USet.filter (fun (a, b) -> USet.mem opq a && USet.mem opq b)
    in
      {
        nodes =
          USet.values mem
          |> List.filter (fun id -> Some id <> initial)
          |> List.sort compare;
        loc;
        writes = v.writes;
        base = Vocab.union [ v.rf; svo; ra; push ];
        po_loc = v.loc_restrict v.po;
        push;
        into = Vocab.union [ svo; spush; ra; volint ];
        needs_to = USet.size push > 0 || USet.size v.rmw > 0;
        causality = URelation.acyclic causal;
      }

  let wwco (d : derived) r =
    USet.filter
      (fun (a, b) ->
        a <> b && USet.mem d.writes a && USet.mem d.writes b && d.loc a b
      )
      r

  (** [co-jom] under the final writes [cofw] and the trace order [to]. *)
  let co_jom (x : derived axiomatic_candidate) ~cofw ~to_ =
    let v = x.v and d = x.d in
    let pushto =
      match to_ with
      | None -> USet.create ()
      | Some t ->
          let heads = URelation.pi_1 d.push in
            USet.filter (fun (a, b) -> USet.mem heads a && USet.mem heads b) t
    in
    let vo =
      Vocab.union
        [
          URelation.transitive_closure
            (Vocab.union [ d.base; URelation.compose [ pushto; d.push ] ]);
          d.po_loc;
        ]
    in
    let coinit =
      match v.initial with
      | None -> USet.create ()
      | Some i ->
          USet.filter (fun w -> w <> i) v.writes
          |> USet.map (fun w -> (i, w))
    in
    let rmw_writes = URelation.pi_2 v.rmw in
    let cormwtotal =
      match to_ with
      | None -> USet.create ()
      | Some t ->
          USet.filter
            (fun (a, b) -> USet.mem rmw_writes a || USet.mem rmw_writes b)
            t
    in
    let base =
      wwco d
        (Vocab.union
           [
             vo;
             URelation.compose [ vo; v.rfi ];
             URelation.compose [ vo; v.po ];
             URelation.compose [ v.rf; v.po; v.rfi ];
             cofw;
             coinit;
             cormwtotal;
           ]
        )
    in
    let excl = URelation.inverse (URelation.compose [ v.rf; v.rmw ]) in
    let rec fix co =
      let next = Vocab.union [ co; wwco d (URelation.compose [ excl; co ]) ] in
        if USet.size next = USet.size co then co else fix next
    in
      fix base

  let coherent (x : derived axiomatic_candidate) =
    let v = x.v and d = x.d in
    (* The final write of each location is the last in the candidate order. *)
    let final w =
      not
        (USet.exists
           (fun w' -> w' <> w && d.loc w w' && USet.mem x.co (w, w'))
           v.writes
        )
    in
    let cofw =
      URelation.cross v.writes (USet.filter final v.writes)
      |> USet.filter (fun (a, b) -> a <> b && d.loc a b)
    in
      if not d.needs_to then URelation.acyclic (co_jom x ~cofw ~to_:None)
      else
        let order =
          URelation.transitive_closure (Vocab.union [ cofw; v.rf; d.into ])
        in
          List.exists
            (fun linear ->
              let rec pairs = function
                | [] -> []
                | a :: rest -> List.map (fun b -> (a, b)) rest @ pairs rest
              in
              let to_ = USet.of_list (pairs linear) in
                URelation.acyclic (co_jom x ~cofw ~to_:(Some to_))
            )
            (Algorithms.linear_extensions
               (fun a b -> USet.mem order (a, b))
               d.nodes
            )

  let axioms =
    [
      ( "(po ∪ rf) ∩ (opq × opq) is acyclic",
        fun (x : derived axiomatic_candidate) -> x.d.causality
      );
      ("co-jom is acyclic for some trace order", coherent);
    ]

  let data_races = None
  let allows_thin_air = true

  let check_program =
    refuse_outside ~name:"JAM" ~description:"programs without locks or consume"
      (fun ev -> no_locks ev && mode_of ev <> Some Consume)
end)

(** WebAssembly's memory model (Watt, Rossberg and Pichon-Pharabod, OOPSLA
    2019, Fig. 7), on MoRDor's accesses: each is to one whole location, so all
    are aligned, of one size and tear-free, and each read reads from one write.

    Two access modes: [sc] accesses are seqcst, every other access unordered.
    [sw] is [rf] from a seqcst write to a seqcst read, [hb = (po ∪ sw)⁺]. For
    each [rf] edge from [W] to [R]:

    - hb-consistent: [R] is not hb-before [W], and no write to the location is
      hb-between them;
    - sc-last-visible, over a total order [tot ⊇ hb], where [W] happens before
      [R]: a seqcst [R] of a seqcst [W] reads the last seqcst write to the
      location tot-before it; (†) a seqcst [R] of an unordered [W] has no
      seqcst write to the location hb-after [W] and tot-before [R]; (‡) an
      unordered [R] of a seqcst [W] has no seqcst write to the location
      tot-after [W] and hb-before [R].

    Every [tot] constraint is between seqcst events, so a [tot] exists iff some
    linear order of the seqcst events extends [hb] and meets them, which is
    searched. An RMW is one event in the paper and two here, so the order must
    also put no seqcst write to its location between its read and its write.

    There is no coherence order, since unordered accesses need not be coherent;
    no undefined behaviour, a race being defined; and no thin-air axiom, the
    paper's model admitting out-of-thin-air executions. Wasm 2019 has no fences
    and no other modes, so a program with them is refused. *)
module Wasm : MEMORY_MODEL = struct
  include Axiomatic (struct
    let name = "wasm"
    let uses_co = false

    type derived = {
      hb : (int * int) uset;
      sc : int list;  (** the seqcst accesses *)
      sc_set : int uset;
      sc_writes : int uset;
    }

    let is_sc (v : Vocab.t) id =
      match Hashtbl.find_opt v.events id with
      | Some { typ = Read; rmod = SC; _ }
      | Some { typ = Write; wmod = SC; _ } ->
          true
      | _ -> false

    let prepare (v : Vocab.t) =
      let sc_set = USet.filter (is_sc v) (USet.union v.reads v.writes) in
      let sc_rel = URelation.identity sc_set in
      let sw = URelation.compose [ sc_rel; v.rf; sc_rel ] in
      let hb = URelation.transitive_closure (Vocab.union [ v.po; sw ]) in
        {
          hb;
          sc = USet.values sc_set |> List.sort compare;
          sc_set;
          sc_writes = USet.intersection sc_set v.writes;
        }

    let hb_consistent (x : derived axiomatic_candidate) =
      let v = x.v and hb = x.d.hb in
        USet.for_all
          (fun (w, r) ->
            (not (USet.mem hb (r, w)))
            && not
                 (USet.exists
                    (fun w' ->
                      w' <> w
                      && USet.mem hb (w, w')
                      && USet.mem hb (w', r)
                      && USet.mem v.same_loc (w', r)
                    )
                    v.writes
                 )
          )
          v.rf

    (** Some linear order of the seqcst accesses extends [hb] and meets
        sc-last-visible and the atomicity of RMWs. *)
    let sc_last_visible (x : derived axiomatic_candidate) =
      let v = x.v and d = x.d in
      let hb = d.hb in
      let same a b = USet.mem v.same_loc (a, b) in
      let sc = USet.mem d.sc_set in
      (* (†) and (‡) as edges every order must have. Like the first condition,
         they apply only where [W] happens before [R] (Fig. 7's premise), so a
         racing read is not held to them. *)
      let forced = USet.create () in
        USet.iter
          (fun (w, r) ->
            if not (USet.mem hb (w, r)) then ()
            else if sc r && not (sc w) then
              USet.iter
                (fun w' ->
                  if same w' r && USet.mem hb (w, w') then
                    USet.add forced (r, w') |> ignore
                )
                d.sc_writes
            else if sc w && not (sc r) then
              USet.iter
                (fun w' ->
                  if w' <> w && same w' w && USet.mem hb (w', r) then
                    USet.add forced (w', w) |> ignore
                )
                d.sc_writes
          )
          v.rf;
        let before a b = USet.mem hb (a, b) || USet.mem forced (a, b) in
        let between pos a b c = pos a < pos c && pos c < pos b in
        let meets order =
          let index = Hashtbl.create 16 in
            List.iteri (fun i id -> Hashtbl.replace index id i) order;
            let pos id = Hashtbl.find index id in
            let none_between a b =
              not
                (USet.exists
                   (fun w' -> w' <> a && same w' b && between pos a b w')
                   d.sc_writes
                )
            in
              USet.for_all
                (fun (w, r) -> not (sc w && sc r) || none_between w r)
                v.rf
              && USet.for_all
                   (fun (r, w) -> not (sc r && sc w) || none_between r w)
                   v.rmw
        in
          List.exists meets (Algorithms.linear_extensions before d.sc)

    let axioms =
      [
        ("rf is hb-consistent", hb_consistent);
        ("some tot meets sc-last-visible", sc_last_visible);
      ]
  end)

  let allows_thin_air = true

  let check_program (structure : symbolic_event_structure) =
    let outside =
      Hashtbl.fold
        (fun _ (ev : event) acc ->
          match ev.typ with
          | Lock | Unlock | Fence -> ev :: acc
          | Read when not (List.mem ev.rmod [ SC; Nonatomic; Relaxed ]) ->
              ev :: acc
          | Write when not (List.mem ev.wmod [ SC; Nonatomic; Relaxed ]) ->
              ev :: acc
          | _ -> acc
        )
        structure.events []
      |> List.sort (fun (a : event) (b : event) -> compare a.label b.label)
    in
      match outside with
      | [] -> Ok ()
      | ev :: _ ->
          Error
            (Printf.sprintf
               "WASM has unordered and seqcst accesses only, and no fences or \
                locks; event %d (%s) is outside that fragment. Write [sc] for \
                seqcst and [na], [rlx] or a plain access for unordered."
               ev.label (show_event_type ev.typ)
            )
end

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

(** {1 Symbolic Models}

    A model asked about a whole combination at once, as constraints a solver
    decides, rather than about one execution at a time (R16, #102). *)

type encoding = {
  enc_events : int list;  (** The combination's events. *)
  enc_reads : int list;  (** Its reads, each choosing a write. *)
  enc_writes : int list;  (** Its writes, each with a location. *)
  enc_candidates : int -> int list;  (** A read's candidate writes. *)
  enc_rmw : (int * int) uset;  (** Its read-modify-write pairs. *)
  enc_reaches : int -> int -> bool;
      (** Whether program order and dependencies reach from one event to
          another: [(dp ∪ ppo)*], which no choice of read-from changes. *)
  enc_chosen : int -> int -> expr;  (** That read takes that write. *)
  enc_position : int -> expr;
      (** A write's place in the coherence order at its location, and a read's
          the place of the write it takes. *)
  enc_sameloc : int -> int -> expr option;
      (** The two events' locations are equal, where both have one. *)
  enc_fresh : string -> expr;  (** A variable of the model's own. *)
  enc_structure : symbolic_event_structure;
}

module type SYMBOLIC_MODEL = sig
  val name : string

  (** Constraints every execution the model admits satisfies, from the cheapest
      statement of them to the fullest. A level may leave out what it cannot
      afford, as long as what it keeps is {e necessary}: unsatisfiable then
      means the combination has no execution the model admits. The caller takes
      the first level that decides it. *)
  val levels : (encoding -> expr list) list
end

(** smrd as constraints: [hb;eco ∪ hb] irreflexive and [rmw ∩ (rb;co) = ∅] over
    each write's position in [co], with [eco] in its positional form --
    [eco (x, y)] is [pos x < pos y], or [x] the write [y] reads.

    Two levels. The first takes [hb] as [(dp ∪ ppo)⁺]; the second adds
    [sw = [W_rel];rf;[R_acq]], whose edges the read-from decides, as
    reachability between the candidate edges. The first is a subset of smrd's
    [hb], so both are necessary; the second decides the combinations whose
    coherence turns on a release/acquire pair (S19, #96). *)
module SymbolicSMRD : SYMBOLIC_MODEL = struct
  let name = "smrd"
  let num n = ENum (Z.of_int n)
  let eq a b = EBinOp (a, "=", b)
  let lt a b = EBinOp (a, "<", b)
  let imp a b = EBinOp (a, "=>", b)
  let neg a = EUnOp ("!", a)

  let conj = function
    | [] -> EBoolean true
    | x :: xs -> List.fold_left (fun a b -> EBinOp (a, "&&", b)) x xs

  let disj = function
    | [] -> EBoolean false
    | [ x ] -> x
    | l -> EOr l

  (* [eco (b, a)]: the pair is at one location, so the coherence order at it
     decides them. *)
  let eco enc b a =
    disj
      (lt (enc.enc_position b) (enc.enc_position a)
      ::
      ( if List.mem b enc.enc_writes && List.mem a enc.enc_reads then
          [ enc.enc_chosen a b ]
        else []
      )
      )

  let atomicity enc =
    List.concat_map
      (fun (r, w) ->
        List.filter_map
          (fun x ->
            if x = w then None
            else
              Option.map
                (fun same ->
                  neg
                    (conj
                       [
                         same;
                         lt (enc.enc_position r) (enc.enc_position x);
                         lt (enc.enc_position x) (enc.enc_position w);
                       ]
                    )
                )
                (enc.enc_sameloc x r)
          )
          enc.enc_writes
      )
      (USet.values enc.enc_rmw)

  (* The candidate [sw] edges: an acquire read and a release write it may read
     from. *)
  let sw_edges enc =
    let matching typ mode =
      URelation.pi_1
        (ModelUtils.match_events enc.enc_structure.events
           (USet.of_list enc.enc_events)
           typ (Some mode) (Some ">") None
        )
    in
    let releases = matching Write Release
    and acquires = matching Read Acquire in
      List.concat_map
        (fun r ->
          if not (USet.mem acquires r) then []
          else
            List.filter_map
              (fun w ->
                if w <> 0 && USet.mem releases w then Some (w, r) else None
              )
              (enc.enc_candidates r)
        )
        enc.enc_reads
      |> Array.of_list

  (* [hb] as a formula per pair, and the constraints the encoding of [sw]
     needs of itself. *)
  let happens_before enc ~sw =
    let accesses = enc.enc_reads @ enc.enc_writes in
    let static a b = a <> b && enc.enc_reaches a b in
      if not sw then
        ([], fun a b -> if static a b then Some (EBoolean true) else None)
      else
        let edges = sw_edges enc in
        let indices = List.init (Array.length edges) Fun.id in
        let active i =
          let w, r = edges.(i) in
            enc.enc_chosen r w
        in
        let z i j = enc.enc_fresh (Printf.sprintf "sw%d_%d" i j) in
        let chains =
          List.concat_map
            (fun i ->
              let _, ri = edges.(i) in
                List.concat_map
                  (fun j ->
                    let wj, _ = edges.(j) in
                      if not (enc.enc_reaches ri wj) then []
                      else
                        imp (active j) (eq (z i j) (num 1))
                        :: List.filter_map
                             (fun k ->
                               let wk, _ = edges.(k) in
                               let _, rj = edges.(j) in
                                 if k = j || not (enc.enc_reaches rj wk) then
                                   None
                                 else
                                   Some
                                     (imp
                                        (conj [ eq (z i j) (num 1); active k ])
                                        (eq (z i k) (num 1))
                                     )
                             )
                             indices
                  )
                  indices
            )
            indices
        in
        let reach_from i b =
          let _, ri = edges.(i) in
            if enc.enc_reaches ri b then Some (EBoolean true)
            else
              match
                List.filter_map
                  (fun j ->
                    let _, rj = edges.(j) in
                      if j = i || not (enc.enc_reaches rj b) then None
                      else Some (eq (z i j) (num 1))
                  )
                  indices
              with
              | [] -> None
              | l -> Some (disj l)
        in
        let through a b =
          List.filter_map
            (fun i ->
              let wi, _ = edges.(i) in
                if not (enc.enc_reaches a wi) then None
                else
                  Option.map
                    (fun reach -> conj [ active i; reach ])
                    (reach_from i b)
            )
            indices
        in
          ( chains,
            fun a b ->
              if static a b then Some (EBoolean true)
              else if not (List.mem a accesses && List.mem b accesses) then None
              else
                match through a b with
                | [] -> None
                | l -> Some (disj l)
          )

  let coherence enc ~sw =
    let extra, happens_before = happens_before enc ~sw in
    let accesses = enc.enc_reads @ enc.enc_writes in
      extra
      @ List.concat_map
          (fun a ->
            List.filter_map
              (fun b ->
                if a = b then None
                else
                  match (enc.enc_sameloc a b, happens_before a b) with
                  | Some same, Some hb ->
                      Some (imp (conj [ same; hb ]) (neg (eco enc b a)))
                  | _ -> None
              )
              accesses
          )
          accesses

  let levels =
    [
      (fun enc -> coherence enc ~sw:false @ atomicity enc);
      (fun enc -> coherence enc ~sw:true @ atomicity enc);
    ]
end

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

  (* A model with a symbolic form says so here; the rest are asked about one
     execution at a time, as before. *)
  let symbolic_models : (string, (module SYMBOLIC_MODEL)) Hashtbl.t =
    Hashtbl.create 4

  let register_symbolic name m = Hashtbl.replace symbolic_models name m
  let lookup_symbolic name = Hashtbl.find_opt symbolic_models name

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
    register_symbolic "smrd" (module SymbolicSMRD : SYMBOLIC_MODEL);

    let rc11_variant config =
      let module M = RC11 (struct
        let config = config
      end) in
      (module M : MEMORY_MODEL)
    in
      register "rc17" (fun () -> rc11_variant RC11Config.rc17);
      register "rc11z" (fun () -> rc11_variant RC11Config.rc11z);
      register "od-lso" (fun () -> rc11_variant RC11Config.od_lso);
      register "c11" (fun () -> rc11_variant RC11Config.c11);
      register "c17" (fun () -> rc11_variant RC11Config.c17);
      register "c20" (fun () -> rc11_variant RC11Config.c20);
      register "orc11" (fun () -> rc11_variant RC11Config.orc11);
      register "wasm" (fun () -> (module Wasm : MEMORY_MODEL));
      register "bmm" (fun () ->
          let module M = TSOAxioms (struct
            let name = "bmm"
            let java_volatiles = true
          end) in
          (module M : MEMORY_MODEL)
      );
      List.iter
        (fun name ->
          register name (fun () ->
              let module M = DRFSC (struct
                let name = name
              end) in
              (module M : MEMORY_MODEL)
          )
        )
        [ "drfx"; "denovosync" ];
      register "crc" (fun () -> (module CRC : MEMORY_MODEL));
      register "ocaml" (fun () -> (module OCaml : MEMORY_MODEL));
      register "jam" (fun () -> (module JAM : MEMORY_MODEL));
      register "rar" (fun () -> rc11_variant RC11Config.rar);
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
                let java_volatiles = false
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

(** [coherence_writes ~orders_allocations structure execution] is the events of
    [execution] a coherence order orders: its writes, and with
    [orders_allocations] its allocations and frees. *)
let coherence_writes ~orders_allocations structure execution =
  USet.filter
    (fun ev_id ->
      try
        let event = Hashtbl.find structure.events ev_id in
          event.typ = Write
          || (orders_allocations && (event.typ = Malloc || event.typ = Free))
      with Not_found -> false
    )
    execution.e

(** [po_orders_per_location structure execution eqlocs writes] is, for each
    location with more than one of [writes] ([eqlocs] deciding which share one),
    the po-respecting orders of its writes as lists of consecutive pairs, Init
    first where the execution reads from it, sorted. *)
let po_orders_per_location structure execution eqlocs writes =
  let ({ po; _ } : symbolic_event_structure) = structure in
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
              (fun (a, b) -> List.mem a writes_list && List.mem b writes_list)
              po
          in

          (* Helper function to convert permutation to pairs *)
          let rec to_pairs acc = function
            | [] | [ _ ] -> List.rev acc
            | x :: (y :: _ as rest) -> to_pairs ((x, y) :: acc) rest
          in

          (* Only the permutations that respect po: every (w1, w2) in po
             has w1 before w2. *)
          let valid_perms =
            linear_extensions
              (fun w1 w2 -> USet.mem po_edges_in_group (w1, w2))
              writes_list
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
    writes_per_location

(** [try_all_coherence_orders ...] is the coherence order that admits
    [execution], or [None] if none does.

    It used to answer [bool] and throw the order away with the search, so
    nothing downstream could say what an execution had been admitted under
    (github #66). The order returned is the canonically least admitting one:
    each location's po-respecting permutations are enumerated in sorted order
    and the first accepted combination wins, so the answer is a function of the
    execution and the model rather than of the traversal.

    [~prune:false] keeps S6's pruning off, for a [check_coherence] that does not
    only reject more as co grows. *)
let try_all_coherence_orders ?(uses_co = true) ?(orders_allocations = false)
    ?(prune = true) cache structure execution check_coherence eqlocs =
  if USet.size execution.e = 0 then None
  else
    let writes = coherence_writes ~orders_allocations structure execution in
      if (not uses_co) || USet.size writes < 2 then
        (* 0 or 1 writes: the only possible coherence order is empty (co only
         orders two writes to the same location), but we must still run the
         model's coherence / thin-air axioms. Returning [true] unconditionally
         was unsound — e.g. a read reading from a write that happens-after it is
         a coherence violation even with co = ∅. *)
        let empty = USet.create () in
          if check_coherence cache empty then Some empty else None
      else
        let writes_per_location =
          po_orders_per_location structure execution eqlocs writes
        in

        (* S6: a model whose violations only grow as co grows rejects every
         completion of a partial order it rejects, so the subtree can go. The
         prune never accepts: an order is admitted only at a leaf, on the
         whole of it. *)
        (* leaves_below.(i): how many complete orders extend a choice made for
         every location from the last down to [i]. *)
        let leaves_below =
          lazy
            (let n = List.length writes_per_location in
             let a = Array.make (n + 1) 1 in
               List.iteri
                 (fun i perms -> a.(i + 1) <- a.(i) * max 1 (List.length perms))
                 writes_per_location;
               a
            )
        in
        let rejected ~below vals =
          prune
          && !S6.prune
          && (Lazy.force leaves_below).(below) >= !S6.min_leaves
          && begin
            incr S6.partial_checks;
            let co = URelation.transitive_closure (USet.of_list vals) in
              (not (check_coherence cache co))
              &&
              ( incr S6.pruned;
                true
              )
          end
        in
        let rec choose_one i vals =
          if i < 0 then (
            incr S6.leaf_checks;
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
                  let vals' = vals @ p in
                    if i > 0 && rejected ~below:i vals' then try_perms ps
                    else
                      match choose_one (i - 1) vals' with
                      | Some co -> Some co
                      | None -> try_perms ps
                )
            in
              try_perms (List.nth writes_per_location i)
        in
          (* S10: is the rejection local? The model's violations only grow with
         co, so a location none of whose orders passes on its own, every other
         location unordered, rejects the execution whatever the rest. *)
          ( if s10_stages then
              let passes vals =
                check_coherence cache
                  (URelation.transitive_closure (USet.of_list vals))
              in
              let empty_ok = passes [] in
              let per_loc =
                List.map
                  (fun perms ->
                    (List.length perms, List.length (List.filter passes perms))
                  )
                  writes_per_location
              in
              let rejecting = List.filter (fun (_, ok) -> ok = 0) per_loc in
                Mutex.protect s10_lock (fun () ->
                    Printf.eprintf
                      "S10 coherence-local id=%d empty_ok=%b locations=%d \
                       rejecting=%d leaves=%d [%s]\n\
                       %!"
                      execution.id empty_ok (List.length per_loc)
                      (List.length rejecting)
                      (List.fold_left (fun a (n, _) -> a * max 1 n) 1 per_loc)
                      (String.concat " "
                         (List.map
                            (fun (n, ok) -> Printf.sprintf "%d/%d" ok n)
                            per_loc
                         )
                      )
                )
          );
          let last = List.length writes_per_location - 1 in
            if last >= 0 && rejected ~below:(last + 1) [] then None
            else choose_one last []

(** {1 Coherence Checking Entry Point} *)

(** [location_equality structure execution] is the pairs of [execution]'s events
    whose locations are equal under its predicates, [ex_p]: which writes a
    coherence order orders together. *)
let location_equality structure execution =
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
    USet.inplace_union ~into:eqlocs (URelation.inverse eqlocs)

(** [elisions_admitted model structure execution]: [model] lets every write
    elision [execution] was built with stand. [we] pairs the overwriting write
    with the one it elides. A partial execution's elisions are among its
    completion's, so a partial execution this rejects has no admitted
    completion.

    An out-of-thin-air execution, one with a cycle in [dp ∪ ppo ∪ rf], reaches
    a model only if the model allows thin air, and then only with elisions
    within a thread. Eliding a store because another thread overwrites it -- an
    initialising store, overwritten through the fork -- left such an execution
    reading the initial event at a value nothing wrote. *)
let elisions_admitted (module M : MEMORY_MODEL)
    (structure : symbolic_event_structure) (execution : symbolic_execution) =
  USet.for_all
    (fun (by, elided) -> M.elidable structure ~elided ~by)
    execution.we
  && ((not M.allows_thin_air)
     || URelation.acyclic
          (USet.union (USet.union execution.dp execution.ppo) execution.rf)
     || USet.for_all
          (fun (by, elided) ->
            ModelUtils.same_thread structure.thread_index elided by
          )
          execution.we
     )

(** [allows_thin_air models]: some model of [models] allows out-of-thin-air
    executions, so the generator has to keep them for it. *)
let allows_thin_air models =
  List.exists
    (fun name ->
      match ModelRegistry.lookup name with
      | Some model ->
          let module M = (val model : MEMORY_MODEL) in
          M.allows_thin_air
      | None -> false
    )
    models

(** [thin_air_admitted model execution]: [model] allows out-of-thin-air
    executions, or [execution]'s reads-happen-before, [dp ∪ ppo ∪ rf], is
    acyclic. A model that does not allow them asks this itself, since the
    generator keeps them when another model of the run does. *)
let thin_air_admitted (module M : MEMORY_MODEL) (execution : symbolic_execution)
    =
  M.allows_thin_air
  || URelation.acyclic
       (USet.union (USet.union execution.dp execution.ppo) execution.rf)

(** [rejected_by_one_location structure execution restrictions]: the model
    rejects [execution] whatever the coherence order at other locations, because
    it elides a write the model does not let be elided, its thin-air check
    fails, or because some location has no po-respecting
    order its axioms accept with every other location left unordered.

    Sound for a model whose violations only grow with co (S6: all but od-lso),
    rf and hb: every completion of a partial execution it holds of is rejected
    too, as long as the completion's locations are grouped at least as coarsely
    ([ex_p] only grows). A location's orders are checked on their own, so this
    never searches the product over locations. *)
let rejected_by_one_location ?eqlocs structure execution restrictions =
  match ModelRegistry.lookup restrictions.coherent with
  | None -> false
  | Some model ->
      let module M = (val model : MEMORY_MODEL) in
      let eqlocs =
        match eqlocs with
        | Some eqlocs -> eqlocs
        | None -> location_equality structure execution
      in
      let cache =
        M.build_cache execution structure
          (build_location_restriction structure execution eqlocs)
      in
        (not (elisions_admitted model structure execution))
        || (not (thin_air_admitted model execution))
        || (not (M.check_thin_air cache execution))
        ||
        let writes =
          coherence_writes ~orders_allocations:M.orders_allocations structure
            execution
        in
          if (not M.uses_co) || USet.size writes < 2 then
            not (M.check_coherence cache (USet.create ()))
          else
            List.exists
              (fun orders ->
                not
                  (List.exists
                     (fun order ->
                       M.check_coherence cache
                         (URelation.transitive_closure (USet.of_list order))
                     )
                     orders
                  )
              )
              (po_orders_per_location structure execution eqlocs writes)

(** [rejects_partial_executions name]: {!rejected_by_one_location} holding of a
    partial execution means model [name] rejects every completion of it. It does
    for a model whose violations only grow with co, rf and hb; S6 found that of
    every registered model but od-lso, whose C++11 release sequence subtracts
    [coe;coe]. C11 has the same release sequence. *)
let rejects_partial_executions name =
  (not (List.mem name [ "od-lso"; "c11" ]))
  && Option.is_some (ModelRegistry.lookup name)

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
        let s10_t0 = Unix.gettimeofday () in
        let eqlocs = location_equality structure execution in

        (* Build location restriction once *)
        let loc_restrict =
          build_location_restriction structure execution eqlocs
        in

        (* Build cache *)
        let cache = M.build_cache execution structure loc_restrict in

        let s10_t1 = Unix.gettimeofday () in
        (* Check thin-air *)
        let thin_air =
          elisions_admitted model structure execution
          && thin_air_admitted model execution
          && M.check_thin_air cache execution
        in
        let s10_t2 = Unix.gettimeofday () in
        let result =
          if not thin_air then None
          else
            (* Try all coherence orders *)
            try_all_coherence_orders ~uses_co:M.uses_co
              ~orders_allocations:M.orders_allocations cache structure execution
              M.check_coherence eqlocs
        in
          (* S10 (see Executions.S10): where the time goes, and which check
             rejects. *)
          if s10_stages then
            Mutex.protect s10_lock (fun () ->
                Printf.eprintf
                  "S10 coherence-stages id=%d model=%s setup_ms=%.0f \
                   thin_air=%b thin_air_ms=%.0f search_ms=%.0f admitted=%b\n\
                   %!"
                  execution.id restrictions.coherent
                  ((s10_t1 -. s10_t0) *. 1000.)
                  thin_air
                  ((s10_t2 -. s10_t1) *. 1000.)
                  ((Unix.gettimeofday () -. s10_t2) *. 1000.)
                  (Option.is_some result)
            );
          result

(** [data_races structure execution name] is the data races of [execution] under
    model [name], in the first coherence order the model admits it under that
    has any; empty if the model has no race clause or no admitting order has a
    race.

    One racy consistent execution makes the whole program undefined, so the
    search asks for a racy order rather than taking the witness
    {!check_for_coherence} kept: under C11's release sequences a different order
    can mean a different [hb]. Every race clause registered excuses two atomic
    accesses, so an execution with no non-atomic access has none, and is not
    searched. *)
let data_races structure execution name =
  let none = USet.create () in
  let has_nonatomic () =
    USet.exists
      (fun id ->
        match Hashtbl.find_opt structure.events id with
        | Some { typ = Read; rmod = Nonatomic; _ }
        | Some { typ = Write; wmod = Nonatomic; _ } -> true
        | _ -> false
      )
      execution.e
  in
    match ModelRegistry.lookup name with
    | None -> none
    | Some model -> (
        let module M = (val model : MEMORY_MODEL) in
        match M.data_races with
        | None -> none
        | Some _ when USet.size execution.e = 0 || not (has_nonatomic ()) ->
            none
        | Some races -> (
            let eqlocs = location_equality structure execution in
            let cache =
              M.build_cache execution structure
                (build_location_restriction structure execution eqlocs)
            in
              if
                not
                  (elisions_admitted model structure execution
                  && thin_air_admitted model execution
                  && M.check_thin_air cache execution
                  )
              then none
              else
                let racy cache co =
                  M.check_coherence cache co
                  && USet.size (races (M.candidate cache co)) > 0
                in
                  match
                    try_all_coherence_orders ~uses_co:M.uses_co
                      ~orders_allocations:M.orders_allocations ~prune:false
                      cache structure execution racy eqlocs
                  with
                  | Some co -> races (M.candidate cache co)
                  | None -> none
          )
      )

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
