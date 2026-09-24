(** Execution generation from symbolic event structures.

    This module implements the core algorithm for generating concrete executions
    from symbolic event structures. It combines justifications for write events,
    computes read-from relations, validates consistency constraints, and filters
    executions for coherence. The process involves:

    1. Computing all control-flow paths through the event structure 2. Combining
    justifications for write events on each path 3. Computing valid read-from
    relations 4. Instantiating and validating executions 5. Filtering for memory
    model coherence

    The implementation uses streaming processing to handle large numbers of
    candidate executions efficiently. *)

open Algorithms
open Coherence
open Context
open Events
open Eventstructures
open Expr
open Forwarding
open Justifications
open Lwt.Syntax
open Types
open Uset

(** {1 Compute Abstraction} *)

(** Abstract parallel computation strategy.

    Encapsulates the choice between single-threaded and parallel execution. Each
    stage of the pipeline receives a [compute_fn] and uses it to map a pure
    worker function over a list of items, returning results in an Lwt promise.

    - [sequential]: applies the worker with [List.map], no parallelism.
    - [parallel pool]: dispatches the items to a domain pool in chunks, via
      {!Parallel.map}. *)
type compute_fn = {
  run : 'a 'b. ?stage:string * string -> ('a -> 'b) -> 'a list -> 'b list Lwt.t;
}

(* [staged ?stage run f items]: with [stage], a {!Progress} stage named and
   counted as it says, ticked as each item is done. *)
let staged ?stage run f items =
  match stage with
  | None -> run f items
  | Some (name, unit) ->
      Progress.stage ~total:(List.length items) ~unit name (fun () ->
          run
            (fun x ->
              let y = f x in
                Progress.tick ();
                y
            )
            items
      )

(** [sequential_compute] is a [compute_fn] that runs items one by one. *)
let sequential_compute : compute_fn =
  {
    run =
      (fun ?stage f items ->
        staged ?stage (fun f items -> Lwt.return (List.map f items)) f items
      );
  }

(** [parallel_compute pool] is a [compute_fn] that dispatches items to [pool].
*)
let parallel_compute pool : compute_fn =
  { run = (fun ?stage f items -> staged ?stage (Parallel.map pool) f items) }

(** {1 Basic Types} *)

(** Provides comparison, hashing, and subsumption checking for executions.
    Executions that are subsumed by others can be filtered out to reduce
    redundancy in the final result set. *)
module Execution : sig
  type t = symbolic_execution

  val equal : t -> t -> bool
  val hash : t -> int
  val contains : t -> t -> bool
  val to_string : t -> string

  val get_relation :
    string -> symbolic_event_structure -> symbolic_execution -> (int * int) uset

  val get_writes_in_rhb_order :
    symbolic_event_structure -> symbolic_execution -> int list
end = struct
  (** The execution type. *)
  type t = symbolic_execution

  (** [equal ex1 ex2] tests execution equality.

      Two executions are equal if they have the same events and relations (event
      set, dependencies, PPO, and read-from).

      @param ex1 First execution.
      @param ex2 Second execution.
      @return [true] if executions are equal. *)
  let equal ex1 ex2 =
    USet.equal ex1.e ex2.e
    && USet.equal ex1.dp ex2.dp
    && USet.equal ex1.ppo ex2.ppo
    && USet.equal ex1.rf ex2.rf

  (** [hash ex] computes hash value for execution.

      Hash is based on the event set and all relations for use in hash tables.

      @param ex The execution to hash.
      @return Hash value. *)
  let hash ex =
    let hash_list lst =
      List.fold_left (fun acc e -> Hashtbl.hash (acc, e)) 0 lst
    in
    let hash_uset uset = USet.values uset |> List.sort compare |> hash_list in
      Hashtbl.hash
        (hash_uset ex.e, hash_uset ex.dp, hash_uset ex.ppo, hash_uset ex.rf)

  (** [contains exec1 exec2] checks if [exec1] subsumes [exec2].

      Execution [exec1] contains [exec2] if they have the same events but
      [exec1] has strictly more edges in its relations. Subsumed executions are
      redundant and can be filtered out.

      @param exec1 Potentially containing execution.
      @param exec2 Potentially contained execution.
      @return [true] if [exec1] contains [exec2]. *)
  let contains exec1 exec2 =
    USet.equal exec2.e exec1.e
    && USet.subset exec2.dp exec1.dp
    && USet.subset exec2.ppo exec1.ppo
    && USet.subset exec2.rf exec1.rf
    && not
         (USet.equal exec1.rf exec2.rf
         && USet.equal exec1.ppo exec2.ppo
         && USet.equal exec1.dp exec2.dp
         )

  (** [to_string exec] converts execution to string representation.

      @param exec The execution.
      @return String representation. *)
  let to_string exec = show_symbolic_execution exec

  (** [get_relation name structure execution] retrieves a relation by name.

      Looks up relations from either the event structure or execution. Supported
      names: [".ppo"], [".po"], [".rf"], [".dp"], [".rmw"], [".co"].

      [".co"] is the order coherence admitted the execution under, and is empty
      before the coherence stage has run.

      @param name The relation name (must include leading dot).
      @param structure The event structure.
      @param execution The execution.
      @return The requested relation, or empty set if unknown. *)
  let get_relation name (structure : symbolic_event_structure)
      (execution : symbolic_execution) =
    match name with
    | ".ppo" -> execution.ppo
    | ".po" -> structure.po
    | ".rf" -> execution.rf
    | ".dp" -> execution.dp
    | ".rmw" -> execution.rmw
    | ".co" -> Option.value execution.co ~default:(USet.create ())
    | _ ->
        Logs_safe.warn (fun m ->
            m "Unknown or unsupported relation: %s, returning empty" name
        );
        USet.create ()

  (** [get_writes_in_rhb_inv_order structure execution] gets writes in RHB^-1
      order.

      Computes the reads-happen-before (RHB) relation as the union of DP, PPO,
      and RF, takes its inverse and transitive closure, and returns the write
      events in the execution sorted according to this inverse RHB order.

      @param structure The event structure.
      @param execution The execution.
      @return List of write events sorted by RHB^-1 order. *)
  let get_writes_in_rhb_order (structure : symbolic_event_structure)
      (execution : symbolic_execution) =
    let dp_ppo = USet.union execution.dp execution.ppo in
    let rhb = USet.union dp_ppo execution.rf |> URelation.transitive_closure in
    let write_events =
      USet.intersection structure.write_events execution.e |> USet.values
    in
      List.sort
        (fun w1 w2 ->
          if USet.mem rhb (w1, w2) then -1
          else if USet.mem rhb (w2, w1) then 1
          else 0
        )
        write_events
end

(** Cache key type for executions. *)
module ExecutionCacheKey = struct
  type t = symbolic_execution

  let equal = Execution.equal
  let hash = Execution.hash
end

(** Hash table keyed by executions for deduplication. *)
module ExecutionCache = Hashtbl.Make (ExecutionCacheKey)

(** Intermediate results from freezing justification combinations.

    A freeze result represents a partially validated execution before final
    coherence checking. It includes the execution relations and the predicates
    that must be satisfied. *)
module FreezeResult = struct
  (** Freeze result type containing execution relations and constraints. *)
  type t = {
    e : int uset;  (** Event set. *)
    dp : (int * int) uset;  (** Dependency relation. *)
    ppo : (int * int) uset;  (** Preserved program order. *)
    rf : (int * int) uset;  (** Read-from relation. *)
    rmw : (int * int) uset;  (** Read-modify-write pairs. *)
    fwd : (int * int) uset;
        (** Forwarding edges of the justification combination this came from.
            Not part of {!equal}, {!hash} or {!contains}: two results that agree
            on the relations above are the same execution whichever forwarding
            reached them, and deduplication unions the contexts rather than
            keeping one and dropping the other. *)
    we : (int * int) uset;  (** Write elisions, on the same terms as [fwd]. *)
    mutable justs : justification list;
        (** The justification combination this result was frozen from. On the
            same terms as [fwd]: not part of {!equal}, {!hash} or {!contains},
            and deduplication unions the sets rather than keeping one.

            Discarded until github #3, so an execution could not say what
            justified it. *)
    pp : expr list;  (** Path predicates that must be satisfied. *)
    conds : expr list;  (** Additional conditions. *)
  }

  (** [merge_justs kept fr] folds [fr]'s justifications into [kept]'s.

      Deduplication keeps one result and drops the rest, and the dropped ones
      are the same execution reached from a different justification combination.
      Keeping only the survivor's would under-report what justified the
      execution. *)
  let merge_justs (kept : t) (fr : t) =
    let seen = Hashtbl.create (List.length kept.justs) in
      List.iter
        (fun j -> Hashtbl.replace seen (Justification.to_string j) ())
        kept.justs;
      let extra =
        List.filter
          (fun j ->
            let key = Justification.to_string j in
              if Hashtbl.mem seen key then false
              else (
                Hashtbl.replace seen key ();
                true
              )
          )
          fr.justs
      in
        kept.justs <- kept.justs @ extra

  (** [equal fr1 fr2] tests freeze result equality.

      @param fr1 First freeze result.
      @param fr2 Second freeze result.
      @return [true] if results are equal. *)
  let equal fr1 fr2 =
    USet.equal fr1.e fr2.e
    && USet.equal fr1.dp fr2.dp
    && USet.equal fr1.ppo fr2.ppo
    && USet.equal fr1.rf fr2.rf
    && USet.equal fr1.rmw fr2.rmw
    && List.equal Expr.equal fr1.pp fr2.pp
    && List.equal Expr.equal fr1.conds fr2.conds

  (** [hash fr] computes hash for freeze result.

      @param fr The freeze result.
      @return Hash value. *)
  let hash fr =
    let hash_list lst =
      List.fold_left (fun acc e -> Hashtbl.hash (acc, e)) 0 lst
    in
    let hash_uset uset = USet.values uset |> List.sort compare |> hash_list in
      Hashtbl.hash
        ( hash_uset fr.e,
          hash_uset fr.dp,
          hash_uset fr.ppo,
          hash_uset fr.rf,
          hash_uset fr.rmw
        )

  (** [contains fr1 fr2] checks if [fr1] subsumes [fr2].

      Similar to execution containment, checks if [fr1] has strictly more edges
      than [fr2] for the same event set.

      @param fr1 Potentially containing result.
      @param fr2 Potentially contained result.
      @return [true] if [fr1] contains [fr2]. *)
  let contains fr1 fr2 =
    USet.equal fr2.e fr1.e
    && USet.equal fr1.rf fr2.rf
    && USet.subset fr2.dp fr1.dp
    && USet.subset fr2.ppo fr1.ppo
    && not (USet.equal fr1.ppo fr2.ppo && USet.equal fr1.dp fr2.dp)
end

(** Cache key type for freeze results. *)
module FreezeResultCacheKey = struct
  type t = FreezeResult.t

  let equal = FreezeResult.equal
  let hash = FreezeResult.hash
end

(** Hash table keyed by freeze results for deduplication. *)
module FreezeResultCache = Hashtbl.Make (FreezeResultCacheKey)

(** {1 Utilities} *)

(** [disjoint (loc1, val1) (loc2, val2)] creates disjointness predicate.

    Two memory accesses are disjoint if their locations differ. This is used to
    ensure atomicity of allocation operations.

    @param loc1 First location.
    @param val1 First value (unused, kept for symmetry).
    @param loc2 Second location.
    @param val2 Second value (unused, kept for symmetry).
    @return Expression asserting locations are unequal. *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ. Written with
     the lesser location first, so that the same fact reached from either end
     is the same predicate. *)
  if Expr.compare loc1 loc2 <= 0 then EBinOp (loc1, "!=", loc2)
  else EBinOp (loc2, "!=", loc1)

(** {1 RF Validation} *)

(** The checks an execution's read-from relation is validated by, over explicit
    inputs, as {!Freeze.instantiate_execution} asks them.

    Each has a [_delta] form, shaped for a fragment merge that knows what it is
    adding to relations already checked: the plain arguments are what was
    checked, and the [d] arguments what is added. Those are stubs: they check
    the union from scratch, and are there to be replaced by forms that look at
    the added edges alone. *)
module Validation = struct
  (** [rf_respects_ppo ~rf ~ppo]: every rf edge [(w, r)] that is in [ppo] has
      [r] among [w]'s successors in [ppo].

      As stated this never fails -- an edge in [ppo] is its own witness -- and
      it is kept as it was found. *)
  let rf_respects_ppo ~rf ~ppo =
    (* Built only if an edge asks for it: it was built for every read-from
       candidate, and on rcu-3-2t-trunc that was 6% of the run. *)
    let ppo_tree = lazy (URelation.adjacency_map ppo) in
      USet.for_all
        (fun (w, r) ->
          if USet.mem ppo (w, r) then
            (* If (w,r) in ppo, check that r is reachable from w *)
            try
              let successors = Hashtbl.find (Lazy.force ppo_tree) w in
                USet.mem successors r
            with Not_found -> false
          else true
        )
        rf

  let rf_respects_ppo_delta ~rf ~ppo ~drf ~dppo =
    rf_respects_ppo ~rf:(USet.union rf drf) ~ppo:(USet.union ppo dppo)

  (** [rf_not_elided ~rf ~delta]: no read reads from a write that [delta], the
      forwarding and write-elision edges, elides. *)
  let rf_not_elided ~rf ~delta =
    USet.size (USet.intersection (URelation.pi_2 delta) (URelation.pi_1 rf)) = 0

  let rf_not_elided_delta ~rf ~delta ~drf ~ddelta =
    rf_not_elided ~rf:(USet.union rf drf) ~delta:(USet.union delta ddelta)

  (** [rf_total ~rf ~reads ~delta]: every read of [reads] that [delta] does not
      elide reads from something. *)
  let rf_total ~rf ~reads ~delta =
    USet.subset (USet.set_minus reads (URelation.pi_2 delta)) (URelation.pi_2 rf)

  let rf_total_delta ~rf ~reads ~delta ~drf ~dreads ~ddelta =
    rf_total ~rf:(USet.union rf drf) ~reads:(USet.union reads dreads)
      ~delta:(USet.union delta ddelta)

  (** [rhb ~dp ~ppo ~rf] is reads-happen-before, [dp ∪ ppo ∪ rf]. *)
  let rhb ~dp ~ppo ~rf = USet.union (USet.union dp ppo) rf

  (** [rhb_acyclic rhb]: no event reads-happens-before itself. *)
  let rhb_acyclic rhb = URelation.acyclic rhb

  let rhb_acyclic_delta rhb ~drhb = rhb_acyclic (USet.union rhb drhb)

  (** [rf_closes_rhb_cycle ~succ ~rf (w, r)]: the read-from edge [(w, r)] closes
      a cycle in reads-happen-before, that is [r] reaches [w] through [succ],
      the successors in [dp ∪ ppo], and [rf], the edges so far as
      [(read, write)] pairs.

      rhb only grows as edges are added, so a read-from relation that has one
      has a cyclic rhb however it is completed, and {!rhb_acyclic} rejects every
      completion. *)
  let rf_closes_rhb_cycle ~succ ~rf (w, r) =
    let visited = Hashtbl.create 64 in
    let rec reaches x =
      x = w
      || (not (Hashtbl.mem visited x))
         && begin
           Hashtbl.replace visited x ();
           ( match Hashtbl.find_opt succ x with
             | Some next -> USet.exists reaches next
             | None -> false
             )
           || List.exists (fun (r', w') -> w' = x && reaches r') rf
         end
    in
      reaches r
end

(** Read-from relation validation.

    Validates that read-from relations satisfy various consistency requirements
    including PPO respect, totality, and semantic correctness. *)
module ReadFromValidation = struct
  (** [env_rf structure rf] computes value equality constraints from RF.

      For each RF edge [(w,r)], creates constraint that the value read equals
      the value written (after accounting for forwarding).

      @param structure The event structure.
      @param rf Read-from relation.
      @return Set of value equality expressions. *)
  let env_rf structure rf =
    USet.filter_map
      (fun (w, r) ->
        if w = 0 then None
        else
          (* Not from the justification, though a note here long asked for it.
             Value assignment concretises a write's value from whatever model
             Solver.solve happens to return for that justification's
             predicates: an arbitrary witness that licenses dropping the
             dependency on the read, not the value the write takes in this
             execution. Constraining rf to it pins every execution to that one
             witness.

             Measured, 2026-09-08: substituting it removes executions from the
             forwarding and OOTA tests -- avoidoota/additional_inventintload
             244 -> 232, avoidoota/listing26 59 -> 51, fwd/rlx/lift_F1r 28 ->
             24, own/FWD-STRENGTHEN-LIFT 68 -> 52 -- and flips jctc/JCTC18 from
             allowed to forbidden, which is the causality case the model exists
             to admit.

             Still true with value assignment made entailment-only: measured
             again after that change, reading the licensed value here loses the
             LB+UB+data+z refinement chain. rf is the wrong lever -- it pins
             which write a read takes its value from, where what github #65
             needs is the value that write puts in the execution's value map.
             That is fix_rf_map, below. *)
          let w_val = vale structure w r in
            match get_val structure r with
            | Some r_val -> Some (Expr.evaluate (Expr.binop w_val "=" r_val))
            | None ->
                failwith ("Read event " ^ string_of_int r ^ " has no value!")
      )
      rf

  (** [check_rf structure rf] computes location equality constraints.

      For each RF edge [(w,r)], creates constraint that locations match.

      @param structure The event structure.
      @param rf Read-from relation.
      @return Set of location equality expressions. *)
  let check_rf structure rf =
    USet.filter_map
      (fun (w, r) ->
        if w = 0 then None
        else
          (* TODO this look-up logic is contrived *)
          let w_loc = loce structure w r in
            match get_loc structure r with
            | Some r_loc -> Some (Expr.evaluate (Expr.binop w_loc "=" r_loc))
            | None ->
                failwith ("Read event " ^ string_of_int r ^ " has no location!")
      )
      rf

  (** [adjacent_same_location_allocation_events structure path rhb p] finds
      adjacent allocations at same location.

      Computes pairs of allocation events at the same location without
      intermediate free events. Used to generate atomicity constraints.

      @param structure The event structure.
      @param path Current path information.
      @param rhb The "reads-happen-before" relation (dp ∪ ppo ∪ rf).
      @param p Predicates for semantic equality checking.
      @return Promise of allocation event pairs requiring disjointness. *)
  let adjacent_same_location_allocation_events structure path rhb p =
    let e_set = path.path in
    let malloc_events = USet.intersection structure.malloc_events e_set in
    let free_events = USet.intersection structure.free_events e_set in
    (* Only compute pairs from malloc events, not reads *)
    let allocation_events = malloc_events in
    let allocation_events_in_po =
      URelation.cross allocation_events allocation_events
      |> USet.intersection structure.po
    in

    USet.filter
      (fun (e_1, e_2) ->
        (* Check if there's no intermediate FREE event between e_1 and e_2 *)
        let has_intermediate =
          USet.exists
            (fun ep ->
              if not (USet.mem rhb (e_1, ep) && USet.mem rhb (ep, e_2)) then
                false
              else
                (* Check if loc(e_1) = loc(ep) under env_rf using semeq *)
                match (get_loc structure e_1, get_loc structure ep) with
                | None, _ | _, None -> false
                | Some loc_e1, Some loc_ep -> Solver.exeq ~state:p loc_e1 loc_ep
            )
            free_events
        in
          not has_intermediate
      )
      allocation_events_in_po
end

(** {1 Justification Validation} *)

(** Validation for justification combinations.

    Checks that combinations of justifications are consistent and satisfy
    necessary constraints for valid executions. *)
module JustValidation = struct
  (** [check_origins_elided structure just fwd_elided] checks symbol origins.

      Verifies that symbols used in the justification don't originate from reads
      that have been elided by forwarding.

      @param structure The event structure.
      @param just The justification to check.
      @param fwd_elided Set of events elided by forwarding.
      @return [true] if no symbol origins are elided. *)
  let check_origins_elided structure just fwd_elided =
    let d_origins =
      USet.map (fun symbol -> origin structure symbol |> Option.get) just.d
    in
    let p_origins =
      List.map Expr.get_symbols just.p
      |> List.flatten
      |> USet.of_list
      |> USet.map (fun symbol -> origin structure symbol |> Option.get)
    in
    let origins = USet.union d_origins p_origins in
    let origin_elided = USet.intersection origins fwd_elided in
      USet.size origin_elided = 0

  (** [check_delta_not_on_path just path] verifies delta events are on path.

      Checks that all events in the justification's forwarding and
      write-exclusion edges are present on the current path.

      @param just The justification.
      @param path Path information.
      @return [true] if all delta events are on the path. *)
  let check_delta_not_on_path just path =
    let just_delta = USet.union just.fwd just.we in
    let just_delta_events =
      USet.union (URelation.pi_1 just_delta) (URelation.pi_2 just_delta)
    in
      USet.subset just_delta_events path.path

  (** [check_partial structure path combo ?alternatives pair] validates partial
      combination.

      Called during combination building to prune invalid partial combinations
      early. Checks symbol origins, delta constraints, and supersession.

      @param structure The event structure.
      @param path Current path.
      @param combo Current partial combination.
      @param alternatives
        Optional list of alternative justifications for same write.
      @param pair The [(write, justification)] pair being added.
      @return Promise of [true] if combination is valid. *)
  let check_partial structure (path : path_info)
      (combo : (int * justification) list) ?(alternatives = [])
      (pair : int * justification) =
    (* conduit code between pair-based and tuple output *)
    let w, just = pair in
    let combo = List.map snd combo in

    let ( let*? ) (condition, msg) f = if condition then f () else false in

    (* Prune if any origins of symbols in d of current justification are not on the path *)
    let sym_origins =
      USet.map (fun symbol -> origin structure symbol |> Option.get) just.d
    in
      let*? () =
        (USet.subset sym_origins path.path, "missing symbol origins")
      in

      (* Prune if delta of current justification is not on the path. *)
      let*? () =
        (check_delta_not_on_path just path, "delta events not on path")
      in

      (* Prune if any orgins of symbols are elided by fwd edges of the
           combination and current justification *)
      let fwd =
        List.map (fun j -> j.fwd) combo |> USet.of_list |> USet.flatten
      in
      (* only consider fwd edges for symbol origins *)
      let fwd_elided =
        USet.union (URelation.pi_2 fwd) (URelation.pi_2 just.fwd)
      in

      let*? () =
        (check_origins_elided structure just fwd_elided, "origins elided")
      in

      let we = USet.flatten (USet.map (fun j -> j.we) (USet.of_list combo)) in
      (* Prune if delta of current justification is contained in the
             accumulated delta of the combination and there exists an
             alternative justification other than the current one, whose delta
             is also contained in the accumulated delta, and which in turn
             contains the delta of the current justification. This avoids
             exploring superseeded justifications. *)
      let superseeded =
        USet.subset just.fwd fwd
        && USet.subset just.we we
        && List.exists
             (fun alt ->
               alt != just (* physical inequality *)
               && just.w = alt.w (* given by inputs *)
               && USet.subset alt.fwd fwd
               && USet.subset alt.we we
               && USet.equal just.d alt.d
               && USet.subset just.fwd alt.fwd
               && USet.subset just.we alt.we
               && List.equal Expr.equal just.p alt.p
             )
             alternatives
      in
        let*? () = (not superseeded, "justification superseeded in delta") in

        (* Prune if delta of current justification is contained in the
               accumulated delta of the combination and there exists an
               alternative justification other than the current one, whose delta
               is also contained in the accumulated delta, and which in turn
               contains the delta of the current justification, and whose
               predicates are a superset of the current justification's
               predicates. This avoids exploring superseeded justifications in
               terms of ordering constraints. *)
        let superseeded =
          USet.subset just.fwd fwd
          && USet.subset just.we we
          && List.exists
               (fun alt ->
                 alt != just (* physical inequality *)
                 && just.w = alt.w (* given by inputs *)
                 && USet.subset alt.fwd fwd
                 && USet.subset alt.we we
                 && USet.subset alt.d just.d
                 (* alt.p is a subset of just.p *)
                 && List.for_all
                      (fun expr ->
                        List.exists (fun expr2 -> Expr.equal expr expr2) just.p
                      )
                      alt.p
               )
               alternatives
        in
          let*? () =
            ( not superseeded,
              "justification superseeded in ordering constraints"
            )
          in

          true

  (** [check_final structure path combo] validates complete combination.

      Called after a combination is complete to verify final constraints:
      acyclicity, functionality, and satisfiability.

      @param structure The event structure.
      @param path Current path.
      @param combo Complete combination of [(write, justification)] pairs.
      @return Promise of [true] if combination is valid. *)
  let check_final structure (path : path_info)
      (combo : (int * justification) list) =
    (* conduit code between pair-based and tuple output *)
    let combo = List.map snd combo in

    let ( let*? ) (condition, msg) f = if condition then f () else false in

    let delta =
      List.map (fun j -> USet.union j.fwd j.we) combo
      |> USet.of_list
      |> USet.flatten
    in
    let elided = URelation.pi_2 delta in

    let*? () = (URelation.acyclic delta, "cyclic delta relation") in

    let*? () =
      ( URelation.is_function (URelation.exhaustive_closure delta),
        "non-functional delta relation"
      )
    in

    let satisfiable =
      List.filter (fun just -> not (USet.mem elided just.w.label)) combo
      |> List.map (fun (just : justification) -> just.p)
      |> List.flatten
      |> List.append path.p
      |> List.map Expr.evaluate
      |> USet.of_list
      |> USet.values
      |> Solver.is_sat_cached
    in
      let*? () = (satisfiable, "unsatisfiable path predicates") in

      Logs_safe.debug (fun m ->
          m
            "[JustValidation.check_final] Justification combination passed \
             final checks:\n\
            \ %s"
            (String.concat "\n"
               (List.map
                  (fun just ->
                    Printf.sprintf "- Justification for w=%d: %s" just.w.label
                      (Justification.to_string just)
                  )
                  combo
               )
            )
      );

      true
end

(** [partial_execution ~e ~dp ~ppo ~rmw ~rf ~ex_p] is an execution with these
    relations and nothing else, for asking a coherence model about a read-from
    relation still being built. *)
let partial_execution ~e ~dp ~ppo ~rmw ~rf ~ex_p : symbolic_execution =
  {
    id = -1;
    e;
    rf;
    dp;
    ppo;
    rmw;
    fwd = USet.create ();
    we = USet.create ();
    ex_p;
    justifications = [];
    co = None;
    fix_rf_map = Hashtbl.create 1;
    pointer_map = None;
    final_env = Hashtbl.create 1;
  }

(** S10 (step 0 of per-thread read-from enumeration): with
    [MORDOR_S10_RF_SAMPLES=k], {!Freeze.freeze} keeps k read-from relations per
    justification combination, each the first valid one of a depth-first search
    in a random order, instead of every one; with [MORDOR_S10_COMBO_STRIDE=n],
    only every n-th combination is frozen. The rest of the pipeline, coherence
    included, runs on that sample, and [S10] lines on stderr report each
    combination's read-from alternatives, by thread, and each execution's
    coherence check. Measurement only; off by default. *)
module S10 = struct
  let int_env name = Option.bind (Sys.getenv_opt name) int_of_string_opt
  let samples = int_env "MORDOR_S10_RF_SAMPLES"

  let combo_stride =
    int_env "MORDOR_S10_COMBO_STRIDE" |> Option.value ~default:1

  let lock = Mutex.create ()

  let print fmt =
    Printf.ksprintf
      (fun line ->
        Mutex.protect lock (fun () ->
            Progress.while_writing (fun () -> prerr_endline line)
        )
      )
      fmt

  exception Found of (int * int) list * FreezeResult.t

  (** A try's budget of extension steps: a random order can make a choice early
      that leaves no write for a read much later, and the search then exhausts
      everything between before it backs out. A try over budget is abandoned for
      a new order. *)
  exception Over_budget

  let budget = int_env "MORDOR_S10_BUDGET" |> Option.value ~default:2000
  let model = Sys.getenv_opt "MORDOR_S10_MODEL" |> Option.value ~default:"smrd"
  let locality = Sys.getenv_opt "MORDOR_S10_LOCALITY" <> None

  (* How early a per-location coherence check, made during read-from
     enumeration, would reject [fr]: the least number of its reads, in
     enumeration order, whose edges alone make
     {!Coherence.rejected_by_one_location} hold. Once with the predicates
     those edges add, which a check during enumeration has; once with the
     combination's alone, which it could compute once per combination. Found
     by bisection: rejection only grows with edges. [alternatives] is how many
     writes each read had, to say how much a rejection at that point cuts. *)
  let report_locality structure (result : FreezeResult.t) p_combined fr
      alternatives =
    let restrictions = { Coherence.coherent = model } in
    let execution rf ex_p =
      partial_execution ~e:result.e ~dp:result.dp ~ppo:result.ppo
        ~rmw:result.rmw ~rf ~ex_p
    in
    let n = List.length fr in
    let prefix d =
      List.filteri (fun i _ -> i < d) fr
      |> List.map (fun (r, w) -> (w, r))
      |> USet.of_list
    in
    let with_edges rf =
      USet.of_list p_combined
      |> USet.union (ReadFromValidation.env_rf structure rf)
      |> USet.union (ReadFromValidation.check_rf structure rf)
      |> USet.values
    in
    let calls = ref 0 in
    let rejected preds d =
      incr calls;
      let rf = prefix d in
        Coherence.rejected_by_one_location structure
          (execution rf (preds rf))
          restrictions
    in
    (* The least d in [0, n] rejected, or None if n is not. *)
    let least preds =
      if not (rejected preds n) then None
      else
        let rec go lo hi =
          if lo >= hi then hi
          else
            let mid = (lo + hi) / 2 in
              if rejected preds mid then go lo mid else go (mid + 1) hi
        in
          Some (go 0 n)
    in
    let cut d =
      List.filteri (fun i _ -> i >= d) alternatives
      |> List.fold_left (fun a k -> a +. log10 (float_of_int (max 1 k))) 0.
    in
    let t = Unix.gettimeofday () in
    let full =
      Coherence.rejected_by_one_location structure
        (execution (prefix n) result.pp)
        restrictions
    in
    let d_rf = least with_edges in
    let d_p = least (fun _ -> p_combined) in
    let show = Option.fold ~none:"-" ~some:string_of_int in
    let show_cut =
      Option.fold ~none:"-" ~some:(fun d -> Printf.sprintf "%.1f" (cut d))
    in
      print
        "S10 local model=%s reads=%d full=%b d_rf=%s d_p=%s cut_rf=%s cut_p=%s \
         total=%.1f calls=%d ms_per_call=%.0f"
        model n full (show d_rf) (show d_p) (show_cut d_rf) (show_cut d_p)
        (cut 0) (!calls + 1)
        ((Unix.gettimeofday () -. t) *. 1000. /. float_of_int (!calls + 1))

  let hex s = String.sub (Digest.to_hex (Digest.string s)) 0 12

  (* Each read's alternatives: the writes of its own thread, of another
     thread, and outside every thread (Init, before the fork). And, per
     thread, a digest of its reads' alternatives, alone and with the
     combination's predicates: what a per-thread enumeration would be keyed
     on, at most and at least. *)
  let report_alternatives structure p_combined
      (alternatives : (int, int list) Hashtbl.t) reads =
    let thread e = Hashtbl.find_opt structure.thread_index e in
    let per_read =
      List.map
        (fun r ->
          let ws = try Hashtbl.find alternatives r with Not_found -> [] in
          let same, other, outside =
            List.fold_left
              (fun (s, o, x) w ->
                match (thread r, thread w) with
                | Some tr, Some tw when tr = tw -> (s + 1, o, x)
                | Some _, Some _ -> (s, o + 1, x)
                | _ -> (s, o, x + 1)
              )
              (0, 0, 0) ws
          in
            (r, thread r, List.sort compare ws, same, other, outside)
        )
        reads
    in
    let log10 f =
      List.fold_left
        (fun a x -> a +. log10 (float_of_int (max 1 (f x))))
        0. per_read
    in
      print "S10 alts reads=%d log10=%.1f local_log10=%.1f [%s]"
        (List.length reads)
        (log10 (fun (_, _, ws, _, _, _) -> List.length ws))
        (log10 (fun (_, _, _, s, _, x) -> s + x))
        (String.concat " "
           (List.map
              (fun (r, t, _, s, o, x) ->
                Printf.sprintf "%d@%s:%d/%d/%d" r
                  (Option.fold ~none:"-" ~some:string_of_int t)
                  s o x
              )
              per_read
           )
        );
      let threads =
        List.sort_uniq compare
          (List.filter_map (fun (_, t, _, _, _, _) -> t) per_read)
      in
      let preds = hex (Marshal.to_string p_combined [ Marshal.No_sharing ]) in
        List.iter
          (fun t ->
            let own =
              List.filter_map
                (fun (r, t', ws, _, _, _) ->
                  if t' = Some t then Some (r, ws) else None
                )
                per_read
            in
            let key = Marshal.to_string own [ Marshal.No_sharing ] in
              print "S10 key thread=%d alts=%s alts+p=%s" t (hex key)
                (hex (key ^ preds))
          )
          threads
end

(** S11 (combination dominance): with [MORDOR_S11_DOMINANCE] set,
    {!Freeze.freeze} enumerates nothing. It records, for each justification
    combination, what minimality compares its results by -- their events, and dp
    and ppo restricted to them -- with the combination's predicates and each
    read's choice of writes, and the freeze stage then reports how many
    combinations another dominates: one whose results would all be removed by
    minimality, or be duplicates, so that it could be skipped. Measurement only;
    off by default. *)
module S11 = struct
  let enabled = Option.is_some (Sys.getenv_opt "MORDOR_S11_DOMINANCE")

  type record = {
    e : int list;
    dp : (int * int) uset;
    ppo : (int * int) uset;
    preds : string list;  (** sorted, distinct *)
    choices : (int * int list) list;  (** by read, each sorted *)
    product : float;
  }

  let lock = Mutex.create ()
  let records : record list ref = ref []
  let unsatisfiable = Atomic.make 0

  exception Stop of (int, int list) Hashtbl.t * int list

  let record r = Mutex.protect lock (fun () -> records := r :: !records)

  let rec subset_sorted a b =
    match (a, b) with
    | [], _ -> true
    | _, [] -> false
    | x :: a', y :: b' ->
        if x = y then subset_sorted a' b'
        else if x > y then subset_sorted a b'
        else false

  (* [c'] dominates [c]: the levels a skip needs, cumulatively. *)
  let frame c' c =
    USet.subset c'.dp c.dp
    && USet.subset c'.ppo c.ppo
    && not (USet.equal c'.dp c.dp && USet.equal c'.ppo c.ppo)

  let predicates c' c = subset_sorted c'.preds c.preds

  (* Every write a read of [c] may read, [c'] offers too, and a read [c] lets
     read Init only because Init is its sole write is so in [c'] too: [c']
     drops Init where a read has another write. *)
  let choices c' c =
    List.for_all
      (fun (r, ws) ->
        let ws' = List.assoc_opt r c'.choices |> Option.value ~default:[] in
          subset_sorted ws ws' && (ws <> [ 0 ] || ws' = [ 0 ])
      )
      c.choices

  let same c' c =
    USet.equal c'.dp c.dp
    && USet.equal c'.ppo c.ppo
    && c'.preds = c.preds
    && c'.choices = c.choices

  let report () =
    (* One program's: several can be run in one process. *)
    let all = Mutex.protect lock (fun () -> !records) in
      Mutex.protect lock (fun () -> records := []);
      let n = List.length all in
      let groups = Hashtbl.create 64 in
        List.iter
          (fun c ->
            Hashtbl.replace groups c.e
              (c :: (Hashtbl.find_opt groups c.e |> Option.value ~default:[]))
          )
          all;
        let dominated test =
          Hashtbl.fold
            (fun _ cs acc ->
              List.filter
                (fun c -> List.exists (fun c' -> c' != c && test c' c) cs)
                cs
              @ acc
            )
            groups []
        in
        let weight cs = List.fold_left (fun a c -> a +. c.product) 0. cs in
        let total = weight all in
        let line name cs =
          Printf.eprintf
            "S11 %-40s %6d of %d combinations, %.3g of %.3g relations\n%!" name
            (List.length cs) n (weight cs) total
        in
        (* Duplicates: all but the first of each class of equals. *)
        let duplicates =
          Hashtbl.fold
            (fun _ cs acc ->
              let rec go kept acc = function
                | [] -> acc
                | c :: rest ->
                    if List.exists (fun k -> same k c) kept then
                      go kept (c :: acc) rest
                    else go (c :: kept) acc rest
              in
                go [] acc (List.rev cs)
            )
            groups []
        in
        let sizes =
          Hashtbl.fold (fun _ cs acc -> List.length cs :: acc) groups []
        in
          Printf.eprintf
            "S11 combinations=%d (plus %d with unsatisfiable predicates) \
             event-sets=%d largest=%d\n\
             %!"
            n
            (Atomic.exchange unsatisfiable 0)
            (Hashtbl.length groups)
            (List.fold_left max 0 sizes);
          line "dominated: frame" (dominated frame);
          line "dominated: frame+predicates"
            (dominated (fun c' c -> frame c' c && predicates c' c));
          line "dominated: frame+predicates+choices"
            (dominated (fun c' c ->
                 frame c' c && predicates c' c && choices c' c
             )
            );
          line "duplicates (frame, predicates, choices equal)" duplicates;
          let dom =
            dominated (fun c' c -> frame c' c && predicates c' c && choices c' c)
          in
            line "skippable (dominated fully, or duplicate)"
              (dom @ List.filter (fun c -> not (List.memq c dom)) duplicates)
end

(** S12 (thread scaling): a fixed piece of a large program's work. With
    [MORDOR_S12_FREEZE_CAP=k] a combination's enumeration stops at its k-th
    execution, and with [MORDOR_S10_COMBO_STRIDE=n] only every n-th combination
    is frozen, without S10's sampling. Measurement only; off by default. *)
module S12 = struct
  let freeze_cap = S10.int_env "MORDOR_S12_FREEZE_CAP"
  let stride = S10.int_env "MORDOR_S10_COMBO_STRIDE"

  (* [MORDOR_S12_STEP_CAP=k]: and at its k-th extension step. *)
  let step_cap = S10.int_env "MORDOR_S12_STEP_CAP"

  exception Capped of (int list * FreezeResult.t) list
  exception Out_of_steps
end

(** S13 (work estimate): with [MORDOR_S13_PROBES=k], {!Freeze.enumerate}
    enumerates nothing. It estimates, by Knuth's method, how many valid
    executions its read-from search would produce and how many extension steps
    it would take: k random descents, each multiplying the number of writes that
    pass at each read, averaged. Unbiased; its variance is what the probes'
    spread says. Measurement only; off by default. *)
module S13 = struct
  let probes = S10.int_env "MORDOR_S13_PROBES"

  (* One descent: the product of passing choices at each read, if it reaches a
     valid leaf, else 0; and the sum of the products at each depth, the
     number of extension steps' nodes. *)
  let probe rng alternatives reads
      ~(check_partial :
         (int * int) list -> ?alternatives:int list -> int * int -> bool
         ) ~valid =
    let rec go combo reads weight nodes =
      match reads with
      | [] -> ((if valid (List.rev combo) then weight else 0.), nodes)
      | r :: rest -> (
          let alts = try Hashtbl.find alternatives r with Not_found -> [] in
          let ok =
            List.filter
              (fun w -> check_partial combo ~alternatives:alts (r, w))
              alts
          in
            match ok with
            | [] -> (0., nodes)
            | _ ->
                let b = float_of_int (List.length ok) in
                let w = List.nth ok (Random.State.int rng (List.length ok)) in
                  go ((r, w) :: combo) rest (weight *. b)
                    (nodes +. (weight *. b))
        )
    in
      go [] reads 1. 1.
end

(** {1 Freezing} *)

module Freeze = struct
  type scope = { reads : int uset; writes : int uset }

  let path_scope structure path ~elided =
    let reads =
      USet.set_minus (USet.intersection structure.read_events path.path) elided
    in
    let writes =
      USet.union structure.write_events structure.free_events
      |> USet.intersection path.path
      |> fun writes -> USet.set_minus writes elided
    in
      { reads; writes = USet.add writes 0 (* include init write *) }

  (** How many read-from relations a combination must have before
      {!fold_path_rf} prunes by coherence: [MORDOR_RF_COHERENCE_PRUNE_MIN],
      10,000 by default. *)
  let coherence_prune_min =
    ref
      (Option.bind
         (Sys.getenv_opt "MORDOR_RF_COHERENCE_PRUNE_MIN")
         float_of_string_opt
      |> Option.value ~default:10_000.
      )

  (** Whether {!fold_path_rf} prunes a read-from relation as soon as it closes a
      cycle in reads-happen-before. On by default; [MORDOR_RF_NO_RHB_PRUNE]
      turns it off, to measure what it prunes.

      Measured 2026-09-19: on rcu-2's futures it stopped a third of the steps
      that extend a relation, before the solver was asked about them, and
      complete relations came twice as fast. On listing15, 307 of 39,972. *)
  let rf_prune_rhb =
    ref (Option.is_none (Sys.getenv_opt "MORDOR_RF_NO_RHB_PRUNE"))

  (** [fold_path_rf structure path ~scope ~elided ~constraints statex ppo dp
       p_combined f init] folds [f] over candidate read-from relations.

      Generates all valid read-from combinations for the reads of [scope], each
      reading from a write of [scope], by: 1. Filtering potential RF edges by
      location equality 2. Checking edges don't violate program order 3.
      Verifying writes aren't shadowed 4. Building combinations incrementally,
      depth-first, dropping one as soon as it is unsatisfiable or closes a cycle
      in [dp ∪ ppo ∪ rf].

      Each relation is passed to [f] as it is completed and not kept, with the
      indices {!ListMapCombinationBuilder.fold_combinations} gives it.

      @param structure The event structure.
      @param path Current path.
      @param scope
        The reads to choose a write for, and the writes to choose among.
      @param elided Set of elided events.
      @param constraints Additional constraints.
      @param statex Static constraints.
      @param ppo Preserved program order.
      @param dp Dependency relation.
      @param p_combined Combined predicates.
      @param f
        Called as [f acc indices rf], with [rf] as a list of [(read, write)]
        pairs. *)
  let rf_search ?shuffle ?inspect ?prune ?(order = `Label) structure
      (path : path_info) ~scope ~elided ~constraints statex ppo dp p_combined =
    let { reads = read_events; writes = write_events } = scope in
    let w_cross_r = URelation.cross write_events read_events in

    Logs_safe.debug (fun m ->
        m
          "[compute_path_rf] Starting RF computation: %d writes (+ init), %d \
           reads, %d potential edges"
          (USet.size write_events) (USet.size read_events) (USet.size w_cross_r)
    );

    let preds = path.p @ constraints @ statex |> USet.of_list |> USet.values in

    (* w must not be po-after r *)
    let po = URelation.restrict path.path structure.po in
    let po_inv = URelation.inverse po in
    let w_cross_r_minus_po = USet.set_minus w_cross_r po_inv in
      Logs_safe.debug (fun m ->
          m
            "[compute_path_rf] After PO filtering: %d edges (removed %d edges \
             where w po-after r)"
            (USet.size w_cross_r_minus_po)
            (USet.size w_cross_r - USet.size w_cross_r_minus_po)
      );
      let all_rf =
        USet.filter
          (fun rf_edge ->
            let ( let*? ) (condition, msg) f =
              if condition then f () else false
            in
            let w, r = rf_edge in
            (* Check that loc(w) = loc(r) is satisfiable *)
            let loc_eq =
              if w = 0 then
                (* init write: skip location check *)
                true
              else
                match (get_loc structure w, get_loc structure r) with
                | Some loc_w, Some loc_r ->
                    Solver.expoteq ~state:preds loc_w loc_r
                | _ -> false
            in
              let*? () = (loc_eq, "RF locs not equal") in
              (* Check that writes are not shadowed for read-from, under the
                 same predicates the location test above just used. *)
              let has_dslwb =
                dslwb ~exclude:elided ~state:preds structure w r
              in
                let*? () = (not has_dslwb, "RF edge is shadowed (dslwb)") in

                true
          )
          w_cross_r_minus_po
      in

      let dp_ppo = USet.union dp ppo in
      let dp_ppo_tc = URelation.transitive_closure dp_ppo in

      (* exclude rf edges that form immediate cycles with ppo and dp *)
      let all_rf_inv = URelation.inverse all_rf in
      let all_rf_inv_before_cycle = URelation.inverse all_rf in
      let all_rf_inv =
        USet.filter (fun (r, w) -> not (USet.mem dp_ppo_tc (r, w))) all_rf_inv
      in

      let all_rf_inv_map = URelation.adjacency_list_map all_rf_inv in

      (* The immediate cycles are excluded above; a longer one, through other
         reads' writes, used to be found only once every read had its write, by
         instantiate_execution. Checked on each edge as it is added, it prunes
         the relations that would all be rejected there. Over its [dp] and
         [ppo], restricted as there to the events the combination does not
         elide: the relations above are not, and a cycle through an elided event
         is not one there. *)
      let rhb_succ =
        USet.union dp ppo
        |> URelation.restrict (USet.set_minus path.path elided)
        |> URelation.adjacency_map
      in

      (* S10 only: a random order, and a look at the alternatives. *)
      Option.iter
        (fun rng ->
          Hashtbl.filter_map_inplace
            (fun _ ws ->
              let a = Array.of_list ws in
                for i = Array.length a - 1 downto 1 do
                  let j = Random.State.int rng (i + 1) in
                  let x = a.(i) in
                    a.(i) <- a.(j);
                    a.(j) <- x
                done;
                Some (Array.to_list a)
            )
            all_rf_inv_map
        )
        shuffle;
      Option.iter
        (fun inspect ->
          inspect all_rf_inv_map (USet.values read_events |> List.sort compare)
        )
        inspect;

      let steps = ref 0 in
      (* Set up only where the relations are many: it asks the solver about
         every pair of events once, and a combination with a handful of
         relations is enumerated sooner than that. *)
      let prune =
        let product =
          List.fold_left
            (fun acc r ->
              acc
              *. float_of_int
                   (List.length
                      (try Hashtbl.find all_rf_inv_map r with Not_found -> [])
                   )
            )
            1. (USet.values read_events)
        in
          match prune with
          | Some prune when product >= !coherence_prune_min -> prune ()
          | _ -> None
      in
      let check_partial combo ?alternatives pair =
        ( match S12.step_cap with
        | Some cap ->
            incr steps;
            if !steps > cap then raise S12.Out_of_steps
        | None -> ()
        );
        if Option.is_some shuffle then (
          incr steps;
          if !steps > S10.budget then raise S10.Over_budget
        );
        let r, w = pair in
          (* discard the combination if we have alternatives to reading
                 from init *)
          if
            w = 0
            && Option.map (fun alts -> List.length alts > 1) alternatives
               |> Option.value ~default:false
          then false
          else if
            !rf_prune_rhb
            && Validation.rf_closes_rhb_cycle ~succ:rhb_succ ~rf:combo (w, r)
          then false
          else
            let new_combo_inv =
              URelation.inverse (USet.of_list (pair :: combo))
            in
            let env_rf = ReadFromValidation.env_rf structure new_combo_inv in
            let check_rf =
              ReadFromValidation.check_rf structure new_combo_inv
            in
            let combined_preds =
              USet.of_list p_combined
              |> USet.union env_rf
              |> USet.union check_rf
              |> USet.values
            in
              Solver.is_sat_cached combined_preds
              && not
                   ( match prune with
                   | Some rejected -> rejected (pair :: combo)
                   | None -> false
                   )
      in
      let reads = USet.values read_events |> List.sort compare in
      let reads =
        match order with
        | `Label -> reads
        | `Constrained ->
            (* S15: the read with the fewest candidate writes first, and each
                 read's latest write first. A search for one relation finds it
                 sooner; the relations are the same. *)
            Hashtbl.filter_map_inplace
              (fun _ ws -> Some (List.sort (fun a b -> compare b a) ws))
              all_rf_inv_map;
            let choices r =
              List.length
                (try Hashtbl.find all_rf_inv_map r with Not_found -> [])
            in
              List.stable_sort
                (fun a b -> compare (choices a) (choices b))
                reads
      in
        (all_rf_inv_map, reads, check_partial)

  let fold_path_rf ?shuffle ?inspect ?prune structure path ~scope ~elided
      ~constraints statex ppo dp p_combined f init =
    let alternatives, reads, check_partial =
      rf_search ?shuffle ?inspect ?prune structure path ~scope ~elided
        ~constraints statex ppo dp p_combined
    in
      ListMapCombinationBuilder.fold_combinations alternatives ~check_partial
        reads f init

  (** [compute_path_rf structure path ~scope ~elided ~constraints statex ppo dp
       p_combined] is the list of relations {!fold_path_rf} folds over, in the
      order they were built in before it was depth-first. *)
  let compute_path_rf structure path ~scope ~elided ~constraints statex ppo dp
      p_combined =
    let rf_candidates =
      fold_path_rf structure path ~scope ~elided ~constraints statex ppo dp
        p_combined
        (fun acc indices rf -> (indices, rf) :: acc)
        []
      |> List.stable_sort (fun (a, _) (b, _) ->
          ListMapCombinationBuilder.compare_build_order a b
      )
      |> List.map snd
    in
      Logs_safe.debug (fun m ->
          m "[compute_path_rf] Generated %d RF combinations"
            (List.length rf_candidates)
      );

      rf_candidates

  (** [frame structure path dp ppo p_combined elided] is what every execution of
      one justification combination shares: its events, the path's less what the
      combination elides; [dp] and [ppo] restricted to them; its reads; and the
      rmw pairs whose condition [p_combined] entails. *)
  let frame (structure : symbolic_event_structure) path dp ppo p_combined elided
      =
    (* remove elided events from execution *)
    let e = USet.set_minus path.path elided in

    (* Filter dp and ppo to execution events only *)
    let dp = URelation.restrict e dp in
    let ppo = URelation.restrict e ppo in
    let read_events = USet.intersection structure.read_events e in

    (* Filter RMW relation to execution events and predicates only *)
    let rmw_filtered =
      USet.filter
        (fun (er, expr, ew) ->
          Solver.exeq ~state:p_combined expr (EBoolean true)
        )
        structure.rmw
    in
    let rmw = USet.map (fun (er, _, ew) -> (er, ew)) rmw_filtered in
      (e, dp, ppo, read_events, rmw)

  (** Whether {!freeze} drops a read-from relation, while it is being built,
      that every model its executions will be asked about rejects at one
      location ({!Coherence.rejected_by_one_location}). On by default;
      [MORDOR_RF_NO_COHERENCE_PRUNE] turns it off. *)
  let rf_prune_coherence =
    ref (Option.is_none (Sys.getenv_opt "MORDOR_RF_NO_COHERENCE_PRUNE"))

  (** [coherence_prune structure path dp ppo p_combined elided models] is the
      check {!fold_path_rf} prunes a partial read-from relation by, when there
      is one: that each of [models] rejects it at one location, whatever the
      reads still without a write read. There is none when a model is one a
      partial relation's rejection says nothing about the completions of
      ({!Coherence.rejects_partial_executions}).

      Locations are grouped by what the partial execution's predicates entail,
      so that a completion's, which include them, group at least as coarsely and
      the rejection carries over. What [p_combined] entails is asked of the
      solver once per combination. What the read-from edges add, that a read's
      value is its write's, is taken by substituting the one for the other in
      the locations and comparing them: on rcu-2 which locations are equal turns
      on the values pointers are read with, and grouping by [p_combined] alone
      let 113 of 114 sampled incoherent relations through. Asking the solver
      about every pair at every step cost 160ms a check (S10).

      The check sees [po] restricted to the execution's events. [po] is
      transitive, so no pair among them is lost, and on rcu-2 it is 12,135 pairs
      where an execution's events have at most a few thousand. *)
  let coherence_prune structure path dp ppo p_combined elided models =
    if
      (not !rf_prune_coherence)
      || models = []
      || not (List.for_all Coherence.rejects_partial_executions models)
    then None
    else
      let e, dp, ppo, _, rmw = frame structure path dp ppo p_combined elided in
      let structure =
        { structure with po = URelation.restrict e structure.po }
      in
      let execution rf =
        partial_execution ~e ~dp ~ppo ~rmw ~rf ~ex_p:p_combined
      in
      let entailed =
        Coherence.location_equality structure (execution (USet.create ()))
      in
      let located =
        USet.values e
        |> List.filter_map (fun ev ->
            Option.map (fun loc -> (ev, loc)) (get_loc structure ev)
        )
      in
      (* Classes of events whose locations are equal, by union-find: what
         [p_combined] entails, merged once; then, per relation, a read with its
         write, and locations equal once each read's value is replaced by its
         write's. *)
      let find parent x =
        let rec go x =
          match Hashtbl.find_opt parent x with
          | Some y when y <> x -> go y
          | _ -> x
        in
          go x
      in
      let union parent a b =
        let a = find parent a and b = find parent b in
          if a <> b then Hashtbl.replace parent (max a b) (min a b)
      in
      let entailed_classes = Hashtbl.create 64 in
        USet.iter (fun (a, b) -> union entailed_classes a b) entailed;
        let eqlocs rf_inv =
          let parent = Hashtbl.copy entailed_classes in
          let values = Hashtbl.create 16 in
            List.iter
              (fun (r, w) ->
                if w <> 0 then (
                  union parent r w;
                  match get_val structure r with
                  | Some (ESymbol s | EVar s) ->
                      Hashtbl.replace values s (vale structure w r)
                  | _ -> ()
                )
              )
              rf_inv;
            let rec normal fuel expr =
              let expr' = Expr.evaluate ~env:(Hashtbl.find_opt values) expr in
                if fuel = 0 || Expr.equal expr expr' then expr'
                else normal (fuel - 1) expr'
            in
            let by_location = Hashtbl.create 16 in
              List.iter
                (fun (ev, loc) ->
                  let key = Expr.to_string (normal 8 loc) in
                    match Hashtbl.find_opt by_location key with
                    | Some first -> union parent first ev
                    | None -> Hashtbl.replace by_location key ev
                )
                located;
              let classes = Hashtbl.create 16 in
                List.iter
                  (fun (ev, _) ->
                    let root = find parent ev in
                      Hashtbl.replace classes root
                        (ev
                        :: (Hashtbl.find_opt classes root
                           |> Option.value ~default:[]
                           )
                        )
                  )
                  located;
                let eqlocs = USet.clone entailed in
                  Hashtbl.iter
                    (fun _ evs ->
                      List.iter
                        (fun a ->
                          List.iter
                            (fun b -> ignore (USet.add eqlocs (a, b)))
                            evs
                        )
                        evs
                    )
                    classes;
                  eqlocs
        in
          Some
            (fun rf_inv ->
              let execution =
                execution
                  (List.map (fun (r, w) -> (w, r)) rf_inv |> USet.of_list)
              in
              let eqlocs = eqlocs rf_inv in
                List.for_all
                  (fun coherent ->
                    Coherence.rejected_by_one_location ~eqlocs structure
                      execution { Coherence.coherent }
                  )
                  models
            )

  (** [instantiate_execution structure path dp ppo j_list pp p_combined elided
       rf] creates execution from justifications and RF.

      Validates all consistency constraints and creates a freeze result if
      successful. This is the core validation step that checks:
      - RF respects PPO
      - RF is total and doesn't read elided writes
      - RHB (reads-happen-before) is acyclic
      - Atomicity of allocations
      - Satisfiability of all predicates

      @param structure The event structure.
      @param path Current path.
      @param dp Dependency relation.
      @param ppo Preserved program order.
      @param j_list List of justifications.
      @param pp Path predicates.
      @param p_combined All combined predicates.
      @param elided The events the combination elides.
      @param rf Read-from relation to validate.
      @return Promise of [Some freeze_result] if valid, [None] otherwise.

      Applied to everything but [rf], it does the work every read-from candidate
      of one justification combination shares, once: {!freeze} applies it so and
      maps the result over the candidates. That work used to be done per
      candidate, and on rcu-3-2t-trunc, with 138,000 candidates for 3
      combinations, it was half the run. *)
  let instantiate_execution (structure : symbolic_event_structure) path dp ppo
      j_list (pp : expr list) p_combined elided =
    let e, dp, ppo, read_events, rmw =
      frame structure path dp ppo p_combined elided
    in

    (* Check 1.1: Various consistency checks *)
    let delta =
      USet.union
        (List.fold_left
           (fun acc j -> USet.union acc j.fwd)
           (USet.create ()) j_list
        )
        (List.fold_left
           (fun acc j -> USet.union acc j.we)
           (USet.create ()) j_list
        )
    in
      fun rf ->
        Logs_safe.debug (fun m ->
            m
              "  [instantiate_execution] Starting validation for RF with %d \
               edges: %s"
              (USet.size rf)
              (String.concat ", "
                 (List.map
                    (fun (w, r) -> Printf.sprintf "(%d->%d)" w r)
                    (USet.values rf)
                 )
              )
        );

        let ( let*? ) (condition, msg) f =
          if condition then f ()
          else (
            Logs_safe.debug (fun m ->
                m "  [instantiate_execution] Rejected: %s" msg
            );

            None
          )
        in

        (* Check 3: All rf edges respect ppo_loc *)
        Logs_safe.debug (fun m ->
            m
              "  [instantiate_execution] Checking RF respects PPO (PPO has %d \
               edges)"
              (USet.size ppo)
        );
        let*? () =
          (Validation.rf_respects_ppo ~rf ~ppo, "RF edges do not respect PPO")
        in

        Logs_safe.debug (fun m ->
            m "  [instantiate_execution] Delta (fwd U we) has %d edges"
              (USet.size delta)
        );

        (* It is given by generation, and this never rejects. remap_just unions
       the combination's whole fwd and we into every justification it remaps,
       so delta here is exactly the combination's fwd U we, and pi_2 delta is
       exactly the elided set compute_path_rf was handed. That subtracts it
       from write_events before pairing anything, and event 0 is never a
       forwarding target, so pi_1 rf cannot meet pi_2 delta. Measured over 60
       programs on 2026-09-08: 67328 calls, 0 rejections.

       Kept as the invariant it now is rather than deleted, since it is the
       only thing standing between a future caller that builds rf some other
       way and a read observing an elided write. rf_total below is not
       in the same position: generation does not guarantee every read gets an
       edge. *)
        let*? () =
          (Validation.rf_not_elided ~rf ~delta, "RF fails RF elided check")
        in
          Logs_safe.debug (fun m ->
              m "  [instantiate_execution] RF elided check passed"
          );
          let*? () =
            ( Validation.rf_total ~rf ~reads:read_events ~delta,
              "RF fails RF total check"
            )
          in
            Logs_safe.debug (fun m ->
                m
                  "  [instantiate_execution] RF total check passed (reads: %d, \
                   RF edges: %d)"
                  (USet.size read_events) (USet.size rf)
            );

            let rhb = Validation.rhb ~dp ~ppo ~rf in
            let rhb_acyclic = Validation.rhb_acyclic rhb in
              Logs_safe.debug (fun m ->
                  m
                    "  [instantiate_execution] Checking RHB acyclicity (dp: \
                     %d, ppo: %d, rf: %d, rhb: %d)"
                    (USet.size dp) (USet.size ppo) (USet.size rf) (USet.size rhb)
              );
              if not rhb_acyclic then (
                Logs_safe.debug (fun m ->
                    m "dp = %s"
                      (USet.to_string
                         (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                         dp
                      )
                );
                Logs_safe.debug (fun m ->
                    m "ppo = %s"
                      (USet.to_string
                         (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                         ppo
                      )
                );
                Logs_safe.debug (fun m ->
                    m "rf = %s"
                      (USet.to_string
                         (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                         rf
                      )
                )
              );
              (* TODO discern memory model *)
              let*? () = (rhb_acyclic, "RHB is not acyclic") in
                Logs_safe.debug (fun m ->
                    m "  [instantiate_execution] RHB acyclicity check passed"
                );

                (* Create environment from RF *)
                let env_rf = ReadFromValidation.env_rf structure rf in
                let check_rf = ReadFromValidation.check_rf structure rf in

                (* atomicity constraint *)
                let af =
                  ReadFromValidation.adjacent_same_location_allocation_events
                    structure path rhb (USet.values env_rf)
                in

                (* Create disjointness predicates *)
                let disj =
                  USet.map
                    (fun (a, b) ->
                      match
                        ( Hashtbl.find_opt structure.events a,
                          Hashtbl.find_opt structure.events b
                        )
                      with
                      | None, _ ->
                          failwith
                            ("Event "
                            ^ string_of_int a
                            ^ " not found in structure!"
                            )
                      | _, None ->
                          failwith
                            ("Event "
                            ^ string_of_int b
                            ^ " not found in structure!"
                            )
                      | Some ea, Some eb -> (
                          match
                            ( get_loc structure a,
                              get_val structure a,
                              get_loc structure b,
                              get_val structure b
                            )
                          with
                          | None, _, _, _ ->
                              failwith
                                ("Event "
                                ^ string_of_int a
                                ^ " has no location!"
                                )
                          | _, None, _, _ ->
                              failwith
                                ("Event " ^ string_of_int a ^ " has no value!")
                          | _, _, None, _ ->
                              failwith
                                ("Event "
                                ^ string_of_int b
                                ^ " has no location!"
                                )
                          | _, _, _, None ->
                              failwith
                                ("Event " ^ string_of_int b ^ " has no value!")
                          | _ ->
                              let loc_a = get_loc structure a |> Option.get in
                              let val_a = get_val structure a |> Option.get in
                              let loc_b = get_loc structure b |> Option.get in
                              let val_b = get_val structure b |> Option.get in
                                (* disjoint only uses location *)
                                Expr.evaluate
                                  (disjoint (loc_a, val_a) (loc_b, val_b))
                        )
                    )
                    af
                in

                let execution_predicates =
                  USet.of_list p_combined
                  |> USet.union env_rf
                  |> USet.union check_rf
                  |> USet.union disj
                  |> USet.filter (fun e -> not (Expr.equal e (EBoolean true)))
                  |> USet.values
                  |> List.sort Expr.compare
                in

                Logs_safe.debug (fun m ->
                    m
                      "  [instantiate_execution] Checking satisfiability of %d \
                       predicates (env_rf: %d, check_rf: %d, disj: %d, \
                       p_combined: %d)"
                      (List.length execution_predicates)
                      (USet.size env_rf) (USet.size check_rf) (USet.size disj)
                      (List.length p_combined)
                );

                (* Check satisfiability of combined predicates *)
                let satisfiable = Solver.is_sat_cached execution_predicates in
                  Logs_safe.debug (fun m ->
                      m
                        "  [instantiate_execution] Satisfiability check \
                         result: %b"
                        satisfiable
                  );
                  let*? () =
                    (satisfiable, "unsatisfiable combined predicates")
                  in

                  (* Success! Return the freeze result *)
                  let freeze_result : FreezeResult.t =
                    (* Every candidate of the combination shares [e], [dp], [ppo] and
                       [rmw]. That once made the parallel pipeline pick a
                       different witnessing execution from the sequential one
                       (lb.lit): Base's hash sets wrote to themselves while
                       being read, and the hash of an execution read what they
                       wrote. USet's sets do neither. *)
                    {
                      e;
                      dp;
                      ppo;
                      rf;
                      rmw;
                      (* Filled in by the caller, which is what knows the
                     justification combination these came from. *)
                      fwd = USet.create ();
                      we = USet.create ();
                      justs = [];
                      pp = execution_predicates;
                      conds = [ EBoolean true ];
                    }
                  in
                    Logs_safe.debug (fun m ->
                        m
                          "  [instantiate_execution] SUCCESS! Created freeze \
                           result with %d events, %d RF edges"
                          (USet.size e) (USet.size rf)
                    );

                    Some freeze_result

  (** [freeze_dp structure just] freezes semantic dependency relations from
      justification.

      @param structure The symbolic event structure.
      @param just The justification to freeze.
      @return The semantic dependency relation for symbols in just. *)
  let freeze_dp structure just =
    (* take symbols from the justifications predicate and the d set *)
    let syms =
      List.map Expr.get_symbols just.p
      |> List.flatten
      |> USet.of_list
      |> USet.union just.d
    in
    let dp =
      USet.fold
        (fun (acc : (int * int) USet.t) (s : string) ->
          match origin structure s with
          | Some orig -> USet.add acc (orig, just.w.label)
          | None -> acc
        )
        syms (USet.create ())
    in

    dp

  (** [freeze_ppo structure path j_list fwd_ctx p_combined] computes PPO for
      justification list.

      @param structure The event structure.
      @param path Current path.
      @param j_list List of justifications.
      @param fwd_ctx Forwarding context.
      @param p_combined Combined predicates.
      @return Pair (PPO, PPO_loc) of ppo relations. *)
  let freeze_ppo structure path j_list fwd_ctx p_combined =
    let fwd_es_ctx = fwd_ctx.es_ctx in

    (* Compute PPO for each justification *)
    let ppos =
      List.map
        (fun just ->
          let just_con =
            ForwardingContext.create fwd_es_ctx ~fwd:just.fwd ~we:just.we ()
          in
          let ppo_j = ForwardingContext.ppo just_con just.p in

          (* TODO path should be po-downward closed *)
          (* Intersect with po pairs ending at or before this write *)
          let po_to_w =
            USet.filter (fun (_, t) -> t = just.w.label) structure.po
          in
          (* Include the write event itself in the cross product
                 so ppo edges TO the write are preserved *)
          let po_predecessors_and_w =
            USet.add (URelation.pi_1 po_to_w) just.w.label
          in
            URelation.restrict po_predecessors_and_w ppo_j
        )
        j_list
    in

    (* Compute ppo_loc *)
    let ppo_loc_base = ForwardingContext.ppo_loc fwd_ctx p_combined in
    let ppo_loc =
      USet.union ppo_loc_base fwd_es_ctx.ppo.ppo_init
      |> URelation.restrict path.path
      |> URelation.transitive_closure
    in

    let ppo =
      List.fold_left USet.union (USet.create ()) ppos
      |> USet.union (ForwardingContext.ppo_sync fwd_ctx)
      |> USet.union fwd_es_ctx.ppo.ppo_init
      |> USet.union ppo_loc
      |> URelation.restrict path.path
      |> URelation.transitive_closure
    in

    Logs_safe.debug (fun m ->
        m "[freeze] Computed PPO: %d edges, PPO_loc: %d edges" (USet.size ppo)
          (USet.size ppo_loc)
    );

    (ppo, ppo_loc)

  (** What {!enumerate} needs of a justification combination, and all it reads:
      two combinations with equal ones freeze to equal results. *)
  type prepared = {
    prep_path : path_info;
    prep_justs : justification list;
    prep_statex : expr list;
    prep_elided : int uset;
    prep_constraints : expr list;
    prep_dp : (int * int) uset;
    prep_ppo : (int * int) uset;
    prep_p_combined : expr list;
  }

  (** [prepare structure fwd_es_ctx path j_list statex ~elided ~constraints]
      computes a combination's dependencies, preserved program order and
      predicates, or [None] if the predicates are unsatisfiable and it has no
      executions. *)
  let prepare structure fwd_es_ctx path j_list statex ~elided ~constraints =
    Logs_safe.debug (fun m ->
        m
          "[freeze] Starting freeze for path with %d events, %d \
           justifications, %d elided events\n\
           %s"
          (USet.size path.path) (List.length j_list) (USet.size elided)
          (String.concat "\n\t" (List.map Justification.to_string j_list))
    );

    let ( let*? ) (condition, msg) f =
      if condition then f ()
      else (
        Logs_safe.debug (fun m -> m "[freeze] Early exit: %s" msg);

        None
      )
    in

    let justs = USet.of_list j_list in

    (* Compute combined fwd and we *)
    let fwd =
      USet.fold (fun acc just -> USet.union acc just.fwd) justs (USet.create ())
    in
    let we =
      USet.fold (fun acc just -> USet.union acc just.we) justs (USet.create ())
    in
    let delta = USet.union fwd we in

    (* Create forwarding context *)
    let fwd_ctx = ForwardingContext.create fwd_es_ctx ~fwd ~we () in

    (* Compute dependency relation *)
    let unelided_justs =
      USet.filter (fun j -> not (USet.mem elided j.w.label)) justs
    in

    let dp =
      USet.map (freeze_dp structure) unelided_justs
      |> USet.flatten
      (* Through the forwarding context, not straight to the restriction to the
         execution's events in [instantiate_execution].

         [freeze_dp] names the origin of each symbol a justification depends on,
         and the origin of a forwarded read is the read itself -- which [delta]
         has elided, so the edge points outside the execution and the
         intersection drops it.  The dependency has not gone anywhere: the value
         now comes from the write it was forwarded from, so the edge belongs on
         that write.  [remap] follows the chain to it and drops the self-edges
         that result.

         Without this, forwarding launders a dependency cycle.  In
         avoidoota/listing16.lit thread 2 is

           r2 := y; z := r2; r3 := z; x := r3

         and [R z] is forwarded from [W z r2], so [W x r3] recorded no
         dependency at all and the out-of-thin-air chain
         x -> r1 -> y -> r2 -> z -> r3 -> x was broken at that step. *)
      |> ForwardingContext.remap_rel fwd_ctx
    in

    Logs_safe.debug (fun m ->
        m "[freeze] Computed dependency relation dp with %d edges:\n %s"
          (USet.size dp)
          (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) dp)
    );

    (* Combine predicates *)
    let p_combined =
      USet.map (fun j -> USet.of_list j.p) justs
      |> USet.flatten
      |> USet.union (USet.of_list fwd_ctx.psi)
      |> USet.union (USet.of_list path.p)
      |> USet.union (USet.of_list statex)
      |> USet.values
      |> List.sort Expr.compare
    in

    (* Debug: Show all predicate sources *)
    Logs_safe.debug (fun m ->
        m "[freeze] Path predicates (%d): [%s]" (List.length path.p)
          (String.concat "; " (List.map Expr.to_string path.p))
    );
    List.iteri
      (fun i j ->
        Logs_safe.debug (fun m ->
            m "[freeze] Justification %d (event %d) predicates (%d): [%s]" i
              j.w.label (List.length j.p)
              (String.concat "; " (List.map Expr.to_string j.p))
        )
      )
      j_list;
    Logs_safe.debug (fun m ->
        m "[freeze] Forwarding context predicates (%d): [%s]"
          (List.length fwd_ctx.psi)
          (String.concat "; " (List.map Expr.to_string fwd_ctx.psi))
    );
    Logs_safe.debug (fun m ->
        m "[freeze] Statex predicates (%d): [%s]" (List.length statex)
          (String.concat "; " (List.map Expr.to_string statex))
    );
    Logs_safe.debug (fun m ->
        m "[freeze] Combined p_combined (%d total predicates): [%s]"
          (List.length p_combined)
          (String.concat "; " (List.map Expr.to_string p_combined))
    );

    (* Check if predicates are satisfiable *)
    let combined_p_sat = Solver.is_sat_cached p_combined in
      Logs_safe.debug (fun m ->
          m
            "[freeze] Combined predicates satisfiable: %b (checked %d \
             predicates)"
            combined_p_sat (List.length p_combined)
      );
      if S11.enabled && not combined_p_sat then Atomic.incr S11.unsatisfiable;
      let*? () = (combined_p_sat, "predicates unsatisfiable") in
      let ppo, _ = freeze_ppo structure path j_list fwd_ctx p_combined in
        Some
          {
            prep_path = path;
            prep_justs = j_list;
            prep_statex = statex;
            prep_elided = elided;
            prep_constraints = constraints;
            prep_dp = dp;
            prep_ppo = ppo;
            prep_p_combined = p_combined;
          }

  (** Whether the freeze stage freezes each kind of combination once
      ({!duplicate_key}). On by default; [MORDOR_FREEZE_NO_MERGE] turns it off.
  *)
  let merge_duplicates =
    ref (Option.is_none (Sys.getenv_opt "MORDOR_FREEZE_NO_MERGE"))

  (** [duplicate_key prepared] is equal for two combinations exactly when
      everything {!enumerate} reads of them is. They then freeze to the same
      results, and differ only in the forwarding and elision edges and the
      justifications attached to those afterwards, which deduplication merges in
      any case. *)
  let duplicate_key p =
    let sorted u = USet.values u |> List.sort compare in
    let strings l = List.map Expr.to_string l |> List.sort_uniq compare in
      Digest.string
        (Marshal.to_string
           ( sorted p.prep_path.path,
             strings p.prep_path.p,
             sorted p.prep_elided,
             strings p.prep_constraints,
             strings p.prep_statex,
             sorted p.prep_dp,
             sorted p.prep_ppo,
             strings p.prep_p_combined
           )
           [ Marshal.No_sharing ]
        )

  (** [enumerate structure prepared ~include_rf] is the combination's valid
      executions, one per read-from relation that passes. *)
  let enumerate ?(coherence_models = []) structure prep ~include_rf =
    let {
      prep_path = path;
      prep_justs = j_list;
      prep_statex = statex;
      prep_elided = elided;
      prep_constraints = constraints;
      prep_dp = dp;
      prep_ppo = ppo;
      prep_p_combined = p_combined;
    } =
      prep
    in
      if S11.enabled then (
        let e, dp_e, ppo_e, _, _ =
          frame structure path dp ppo p_combined elided
        in
        let alternatives, reads =
          try
            fold_path_rf
              ~inspect:(fun map reads ->
                raise (S11.Stop (Hashtbl.copy map, reads))
              )
              structure path
              ~scope:(path_scope structure path ~elided)
              ~elided ~constraints statex ppo dp p_combined
              (fun () _ _ -> ())
              ();
            (Hashtbl.create 1, [])
          with S11.Stop (map, reads) -> (map, reads)
        in
        let choices =
          List.map
            (fun r ->
              ( r,
                (try Hashtbl.find alternatives r with Not_found -> [])
                |> List.sort_uniq compare
              )
            )
            (List.sort compare reads)
        in
          S11.record
            {
              S11.e = USet.values e |> List.sort compare;
              dp = dp_e;
              ppo = ppo_e;
              preds =
                List.map Expr.to_string p_combined |> List.sort_uniq compare;
              choices;
              product =
                List.fold_left
                  (fun a (_, ws) -> a *. float_of_int (List.length ws))
                  1. choices;
            };
          []
      )
      else
        let instantiate =
          instantiate_execution structure path dp ppo j_list path.p p_combined
            elided
        in
        (* Each relation is instantiated as it is built, and only the executions
         kept: the relations were a list, and on rcu-2 one combination's ran to
         tens of GB before the first was instantiated. Sorted back into the
         order the list had, which the executions' ids follow. *)
        let candidates = ref 0 in
        let valid =
          if include_rf && Option.is_some S10.samples then (
            let k = Option.get S10.samples in
            let seen = Hashtbl.create k in
            let found = ref [] in
            let seed = Hashtbl.hash (List.map (fun j -> j.w.label) j_list) in
            let tries = ref 0 and over = ref 0 in
            let alternatives = ref [] in
              for i = 0 to (20 * k) - 1 do
                if List.length !found < k then
                  try
                    incr tries;
                    fold_path_rf
                      ~shuffle:(Random.State.make [| seed; i |])
                      ?inspect:
                        ( if i = 0 then
                            Some
                              (fun map reads ->
                                alternatives :=
                                  List.map
                                    (fun r ->
                                      List.length
                                        ( try Hashtbl.find map r
                                          with Not_found -> []
                                        )
                                    )
                                    reads;
                                S10.report_alternatives structure p_combined map
                                  reads
                              )
                          else None
                        )
                      structure path
                      ~scope:(path_scope structure path ~elided)
                      ~elided ~constraints statex ppo dp p_combined
                      (fun () _ fr ->
                        incr candidates;
                        match
                          instantiate
                            (List.map (fun (r, w) -> (w, r)) fr |> USet.of_list)
                        with
                        | Some result -> raise (S10.Found (fr, result))
                        | None -> ()
                      )
                      ()
                  with
                  | S10.Over_budget -> incr over
                  | S10.Found (fr, result) ->
                      let key = List.sort compare fr in
                        if not (Hashtbl.mem seen key) then (
                          Hashtbl.add seen key ();
                          if S10.locality then
                            S10.report_locality structure result p_combined fr
                              !alternatives;
                          found := ([], result) :: !found
                        )
              done;
              S10.print
                "S10 sampled distinct=%d of %d tries, %d complete, %d over \
                 budget"
                (Hashtbl.length seen) !tries !candidates !over;
              List.rev !found
          )
          else if include_rf && Option.is_some S13.probes then (
            let k = Option.get S13.probes in
            let alternatives, reads, check_partial =
              rf_search
                ~prune:(fun () ->
                  coherence_prune structure path dp ppo p_combined elided
                    coherence_models
                )
                structure path
                ~scope:(path_scope structure path ~elided)
                ~elided ~constraints statex ppo dp p_combined
            in
            let rng =
              Random.State.make
                [| Hashtbl.hash (List.map (fun j -> j.w.label) j_list) |]
            in
            let t = Unix.gettimeofday () in
            let results =
              List.init k (fun _ ->
                  S13.probe rng alternatives reads ~check_partial
                    ~valid:(fun fr ->
                      Option.is_some
                        (instantiate
                           (List.map (fun (r, w) -> (w, r)) fr |> USet.of_list)
                        )
                  )
              )
            in
            let leaves = List.map fst results
            and nodes = List.map snd results in
            let mean l = List.fold_left ( +. ) 0. l /. float_of_int k in
              S10.print
                "S13 reads=%d probes=%d reached=%d leaves_mean=%.4g \
                 leaves_max=%.4g nodes_mean=%.4g secs=%.1f"
                (List.length reads) k
                (List.length (List.filter (fun x -> x > 0.) leaves))
                (mean leaves)
                (List.fold_left max 0. leaves)
                (mean nodes)
                (Unix.gettimeofday () -. t);
              []
          )
          else if include_rf then
            let s12_found = ref [] in
              try
                fold_path_rf
                  ~prune:(fun () ->
                    coherence_prune structure path dp ppo p_combined elided
                      coherence_models
                  )
                  structure path
                  ~scope:(path_scope structure path ~elided)
                  ~elided ~constraints statex ppo dp p_combined
                  (fun acc indices fr ->
                    incr candidates;
                    match
                      instantiate
                        (List.map (fun (r, w) -> (w, r)) fr |> USet.of_list)
                    with
                    | Some result ->
                        Progress.found ~unit:"executions" 1;
                        let acc = (indices, result) :: acc in
                          s12_found := acc;
                          ( match S12.freeze_cap with
                          | Some cap when List.length acc >= cap ->
                              raise (S12.Capped acc)
                          | _ -> ()
                          );
                          acc
                    | None -> acc
                  )
                  []
              with
              | S12.Capped acc -> acc
              | S12.Out_of_steps -> !s12_found
          else (
            incr candidates;
            Option.to_list (instantiate (USet.create ()))
            |> List.map (fun r -> ([], r))
          )
        in
        let filtered_results =
          List.stable_sort
            (fun (a, _) (b, _) ->
              ListMapCombinationBuilder.compare_build_order a b
            )
            valid
          |> List.map snd
        in
          Logs_safe.debug (fun m ->
              m
                "[freeze] instantiate_execution produced %d valid results from \
                 %d RF combos"
                (List.length filtered_results)
                !candidates
          );

          filtered_results

  (** {2 Witnesses}

      What the futures need of a combination is not its executions but one of
      them, or the knowledge that it has none: every execution of a combination
      has the same future (S14, #91). *)

  type witness =
    | Witness of FreezeResult.t
        (** A result {!enumerate} would return, which the model admits. *)
    | No_witness  (** The combination has no such result. *)
    | Undecided  (** Neither was established within the budgets. *)

  let env_int name default =
    Option.bind (Sys.getenv_opt name) int_of_string_opt |> Option.value ~default

  (** How many read-from relations the solver may propose for one combination
      before it is left to the search: [MORDOR_WITNESS_ROUNDS], 50 by default.
  *)
  let witness_rounds = ref (env_int "MORDOR_WITNESS_ROUNDS" 50)

  (** Seconds the search may spend on one combination: [MORDOR_WITNESS_SECS], 60
      by default. *)
  let witness_seconds =
    ref
      (Option.bind (Sys.getenv_opt "MORDOR_WITNESS_SECS") float_of_string_opt
      |> Option.value ~default:60.
      )

  let instantiator structure prep =
    instantiate_execution structure prep.prep_path prep.prep_dp prep.prep_ppo
      prep.prep_justs prep.prep_path.p prep.prep_p_combined prep.prep_elided

  (** [frame_of structure prep] is the combination's events, [dp] and [ppo]:
      what its future, and minimality, compare it by. *)
  let frame_of structure prep =
    let e, dp, ppo, _, _ =
      frame structure prep.prep_path prep.prep_dp prep.prep_ppo
        prep.prep_p_combined prep.prep_elided
    in
      (e, dp, ppo)

  (* The search {!enumerate} runs, as candidate writes per read, the order it
     decides reads in, and its check of a partial relation. *)
  let search_space ?order ~coherence_models structure prep =
    let path = prep.prep_path and elided = prep.prep_elided in
      rf_search ?order
        ~prune:(fun () ->
          coherence_prune structure path prep.prep_dp prep.prep_ppo
            prep.prep_p_combined elided coherence_models
        )
        structure path
        ~scope:(path_scope structure path ~elided)
        ~elided ~constraints:prep.prep_constraints prep.prep_statex
        prep.prep_ppo prep.prep_dp prep.prep_p_combined

  (** [valid_rf ~coherence_models structure prep] is a test of whether a
      read-from relation, as [(write, read)] pairs, is one {!enumerate} with
      [coherence_models] returns a result for: the search reaches it, every
      prefix passing its checks in its order, and it instantiates. The search is
      set up once, by the call. *)
  let valid_rf ~coherence_models structure prep =
    let alternatives, reads, check_partial =
      search_space ~coherence_models structure prep
    in
    let instantiate = instantiator structure prep in
      fun rf ->
        let write = Hashtbl.create 16 in
          USet.iter (fun (w, r) -> Hashtbl.replace write r w) rf;
          let rec reached combo = function
            | [] -> true
            | r :: rest -> (
                match Hashtbl.find_opt write r with
                | None -> false
                | Some w ->
                    let alternatives =
                      try Hashtbl.find alternatives r with Not_found -> []
                    in
                      List.mem w alternatives
                      && check_partial combo ~alternatives (r, w)
                      && reached ((r, w) :: combo) rest
              )
          in
            Hashtbl.length write = List.length reads
            && reached [] reads
            && Option.is_some (instantiate rf)

  exception Found of FreezeResult.t
  exception Out_of_time

  (** [search_witness ~coherence_models ~check structure prep] searches the
      combination's read-from relations, most constrained read first, for a
      result [check] accepts, within {!witness_seconds}. *)
  let search_witness ~coherence_models ~check structure prep =
    let alternatives, reads, check_partial =
      search_space ~order:`Constrained ~coherence_models structure prep
    in
    let instantiate = instantiator structure prep in
    let deadline = Unix.gettimeofday () +. !witness_seconds in
    let steps = ref 0 in
    let check_partial combo ?alternatives pair =
      incr steps;
      if !steps land 1023 = 0 && Unix.gettimeofday () > deadline then
        raise Out_of_time;
      check_partial combo ?alternatives pair
    in
      try
        ListMapCombinationBuilder.fold_combinations alternatives reads
          ~check_partial
          (fun () _ fr ->
            match
              instantiate (List.map (fun (r, w) -> (w, r)) fr |> USet.of_list)
            with
            | Some result when check result -> raise (Found result)
            | _ -> ()
          )
          ();
        No_witness
      with
      | Found result -> Witness result
      | Out_of_time -> Undecided

  (** [solver_witness ~model ~check structure prep] asks the solver for a
      read-from relation of the combination that [model] could admit, and checks
      each it proposes exactly -- [instantiate_execution], then [check] --
      blocking those that fail, up to {!witness_rounds} times.

      The constraints are a necessary condition for such a result (S19, #96): a
      selector per read ranges over its candidate writes (Init only where it is
      the only one); the chosen edge implies the read's value and location equal
      the write's; the combination's predicates hold; [rhb] is acyclic, by
      ranks; each write has a place in the coherence order at its location,
      distinct from the others there, and a read has its write's. The model adds
      its own, in levels, from the cheapest statement to the fullest
      ({!Coherence.SYMBOLIC_MODEL}); the first that decides the combination is
      the answer, and what one level ruled out the next keeps.

      Unsatisfiable therefore means the combination has no result the model
      admits. A model with no symbolic form leaves it {!Undecided}, for the
      search. *)
  let solver_witness ~model ~check structure prep =
    match Coherence.ModelRegistry.lookup_symbolic model with
    | None -> Undecided
    | Some symbolic ->
        let module M = (val symbolic : Coherence.SYMBOLIC_MODEL) in
        let alternatives, reads, _ =
          search_space ~coherence_models:[] structure prep
        in
        let instantiate = instantiator structure prep in
        let e, dp, ppo = frame_of structure prep in
        let _, _, _, _, rmw =
          frame structure prep.prep_path prep.prep_dp prep.prep_ppo
            prep.prep_p_combined prep.prep_elided
        in
        let var fmt = Printf.ksprintf (fun s -> ESymbol s) fmt in
        let sel r = var "witness_sel%d" r
        and rank x = var "witness_rank%d" x
        and pos x = var "witness_pos%d" x in
        let num n = ENum (Z.of_int n) in
        let eq a b = EBinOp (a, "=", b)
        and lt a b = EBinOp (a, "<", b)
        and imp a b = EBinOp (a, "=>", b)
        and neg a = EUnOp ("!", a) in
        let conj = function
          | [] -> EBoolean true
          | x :: xs -> List.fold_left (fun a b -> EBinOp (a, "&&", b)) x xs
        in
        let disj = function
          | [] -> EBoolean false
          | [ x ] -> x
          | l -> EOr l
        in
        let alts r =
          let ws = try Hashtbl.find alternatives r with Not_found -> [] in
            if List.length ws > 1 then List.filter (fun w -> w <> 0) ws else ws
        in
        let chosen r w = eq (sel r) (num w) in
        let writes =
          USet.values e
          |> List.filter (fun x ->
              x <> 0
              &&
              match Hashtbl.find_opt structure.events x with
              | Some (ev : event) -> ev.typ = Write && Option.is_some ev.loc
              | None -> false
          )
        in
        let sameloc a b =
          match (get_loc structure a, get_loc structure b) with
          | Some la, Some lb -> Some (eq la lb)
          | _ -> None
        in
        let edge f w r = USet.values (f structure (USet.singleton (w, r))) in
        let for_edges f =
          List.concat_map
            (fun r ->
              List.filter_map (fun w -> if w = 0 then None else f r w) (alts r)
            )
            reads
        in
        let static = USet.union dp ppo |> URelation.restrict e in
        let closure = URelation.transitive_closure static in
        let encoding =
          {
            Coherence.enc_events = USet.values e;
            enc_reads = reads;
            enc_writes = writes;
            enc_candidates = alts;
            enc_rmw = rmw;
            enc_reaches = (fun a b -> a = b || USet.mem closure (a, b));
            enc_chosen = chosen;
            enc_position = pos;
            enc_sameloc = sameloc;
            enc_fresh = (fun name -> var "witness_%s" name);
            enc_structure = structure;
          }
        in
        (* What every execution of the combination satisfies, whatever the
           model: the choices, what they mean for values and locations, the
           combination's predicates, an acyclic [rhb], and a coherence order
           per location. *)
        let common =
          prep.prep_p_combined
          @ List.map (fun r -> disj (List.map (chosen r) (alts r))) reads
          @ for_edges (fun r w ->
              Some
                (imp (chosen r w)
                   (conj
                      (edge ReadFromValidation.env_rf w r
                      @ edge ReadFromValidation.check_rf w r
                      )
                   )
                )
          )
          @ List.map (fun (a, b) -> lt (rank a) (rank b)) (USet.values static)
          @ for_edges (fun r w -> Some (imp (chosen r w) (lt (rank w) (rank r))))
          @ List.map (fun x -> lt (num 0) (pos x)) writes
          @ List.concat_map
              (fun x ->
                List.filter_map
                  (fun y ->
                    if x >= y then None
                    else
                      Option.map
                        (fun same -> imp same (neg (eq (pos x) (pos y))))
                        (sameloc x y)
                  )
                  writes
              )
              writes
          @ List.concat_map
              (fun r ->
                List.map
                  (fun w ->
                    imp (chosen r w)
                      (eq (pos r) (if w = 0 then num 0 else pos w))
                  )
                  (alts r)
              )
              reads
        in
        let decode model =
          List.map
            (fun r ->
              match
                Hashtbl.find_opt model (Printf.sprintf "witness_sel%d" r)
              with
              | Some (VNumber n) -> (r, Z.to_int n)
              | _ -> (r, List.hd (alts r @ [ 0 ]))
            )
            reads
        in
        let rec ask constraints blocks n =
          if n > !witness_rounds then (Undecided, blocks)
          else
            match Solver.quick_solve (constraints @ blocks) with
            | None -> (No_witness, blocks)
            | Some model -> (
                let rf = decode model in
                let blocked =
                  neg (conj (List.map (fun (r, w) -> chosen r w) rf)) :: blocks
                in
                let result =
                  instantiate
                    (List.map (fun (r, w) -> (w, r)) rf |> USet.of_list)
                in
                  match result with
                  | Some result when check result -> (Witness result, blocked)
                  | _ -> ask constraints blocked (n + 1)
              )
        in
        let rec by_level levels blocks =
          match levels with
          | [] -> Undecided
          | level :: rest -> (
              match ask (common @ level encoding) blocks 1 with
              | Undecided, blocks -> by_level rest blocks
              | decided, _ -> decided
            )
        in
          if List.exists (fun r -> alts r = []) reads then No_witness
          else by_level M.levels []

  (** [witness ~model ~coherence_models ~admits ~reject structure prep] is a
      witness for the combination: a result {!enumerate} would return, that
      [admits] (the model's coherence check) holds of and [reject] does not. For
      smrd the solver is asked first ({!solver_witness}); for any other model,
      and where the solver is undecided, the search is ({!search_witness}),
      pruning by [coherence_models]. *)
  let witness ~model ~coherence_models ~admits ~reject structure prep =
    let check result = admits result && not (reject result) in
    let from_solver = solver_witness ~model ~check structure prep in
      match from_solver with
      | Undecided -> search_witness ~coherence_models ~check structure prep
      | decided -> decided

  (** [freeze structure path j_list statex ~elided ~constraints ~include_rf]
      creates executions from justifications.

      The "freeze" operation converts a list of justifications for a path into
      concrete executions by: 1. Computing dependency and PPO relations 2.
      Generating valid read-from combinations 3. Validating each combination 4.
      Creating freeze results for valid combinations

      @param structure The event structure.
      @param path Current path.
      @param j_list List of justifications for writes on path.
      @param statex Static constraints.
      @param elided Set of elided events.
      @param constraints Additional constraints.
      @param include_rf Whether to compute RF relations (false for testing).
      @return Promise of list of valid freeze results.

      It is {!enumerate} of {!prepare}. The freeze stage calls the two
      separately, to freeze each kind of combination once. *)
  let freeze ?coherence_models structure fwd_es_ctx path j_list statex ~elided
      ~constraints ~include_rf =
    match
      prepare structure fwd_es_ctx path j_list statex ~elided ~constraints
    with
    | None -> []
    | Some prep -> enumerate ?coherence_models structure prep ~include_rf
end

let justifiable structure path =
  USet.union structure.write_events structure.malloc_events
  |> USet.union structure.free_events
  |> USet.intersection path.path

(** [compute_justification_combinations compute structure paths ~scope justmap]
    computes justification combinations for all paths.

    For each path, builds all valid combinations of justifications for the
    events [scope path]. Returns a stream of [(path, justifications)] pairs.

    @param structure The event structure.
    @param paths List of all paths through the structure.
    @param scope The events of a path to choose a justification for.
    @param justmap Hash table mapping write event IDs to justification lists.
    @return Stream of [(path, justification list)] pairs. *)
let compute_justification_combinations compute structure paths ~scope
    (justmap : (int, justification list) Hashtbl.t) =
  (* Given a path, combine justifications for each write on the path. *)
  let combine_justifications_for_path path =
    Logs_safe.debug (fun m ->
        m "Building justification combinations for path [%s]"
          (String.concat ", "
             (List.map (Printf.sprintf "%d")
                (List.sort compare (USet.values path.path))
             )
          )
    );

    (* In label order. The partial check prunes a justification as superseded
       by what the combination built so far already forwards, so which
       combinations survive depends on the order the writes come in, and the
       order a set gives is its own. *)
    let path_writes =
      USet.intersection path.path (scope path)
      |> USet.values
      |> List.sort (fun a b -> compare b a)
    in

    (* Selecting justifications for events the combination will elide is
       waste, but not removable here: build_combinations produces total
       combinations over a fixed key list, and check_partial can reject a
       binding, never skip a key. Which events are elided is a property of the
       combination being built, so the builder would have to let a partial
       combination drop a key it has already elided. That is a change to
       ListMapCombinationBuilder, not to this call. *)
    let js_combinations =
      ListMapCombinationBuilder.build_combinations justmap path_writes
        ~check_partial:(fun combo ?alternatives just ->
          JustValidation.check_partial structure path combo ?alternatives just
        )
        ~check_final:(fun combo ->
          JustValidation.check_final structure path combo
          &&
          ( Progress.found ~unit:"combinations" 1;
            true
          )
        )
        ()
    in

    Logs_safe.debug (fun m ->
        m "  Found %d justification combinations" (List.length js_combinations)
    );

    List.map (fun combo -> (path, List.map snd combo)) js_combinations
  in

  let* results =
    compute.run
      ~stage:("justification combinations", "paths")
      combine_justifications_for_path paths
  in
    List.flatten results |> Lwt.return

(** {1 Generate executions} *)

(** S4: identity on an Lwt stream, logging its length under [name] when
    [s4_counters] (shared with {!Coherence}) is enabled. Explicitly polymorphic
    so it can sit between pipeline stages of differing element types. *)
let count_stage : 'a. string -> 'a list Lwt.t -> 'a list Lwt.t =
 fun name stream ->
  if not !s4_counters then stream
  else
    Lwt.bind stream (fun s ->
        Logs_safe.info (fun m -> m "[S4] %s: %d" name (List.length s));
        Lwt.return s
    )

(** [execution_of_freeze_result structure ~include_rf ~id fr] is the execution a
    freeze result becomes: its relations, the read values resolved through its
    read-from, and the final register environment. *)
let execution_of_freeze_result (structure : symbolic_event_structure)
    ~include_rf ~id (freeze_res : FreezeResult.t) : symbolic_execution =
  (* Fixed point computation for RF mapping *)
  let fix_rf_map = Hashtbl.create 16 in

  (* Build initial mapping from RF *)
  if include_rf then
    USet.iter
      (fun (w, r) ->
        (* TODO look up logic is contrived *)
        let w_val = vale structure w r in
          match get_val structure r with
          | None -> failwith ("Read event " ^ string_of_int r ^ " has no value!")
          | Some r_val ->
              (* Store mapping *)
              Hashtbl.replace fix_rf_map (Expr.to_string r_val) w_val
      )
      freeze_res.rf;

  (* Compute fixed point *)
  let rec compute_fixed_point map =
    let changed = ref false in
    let new_map = Hashtbl.create (Hashtbl.length map) in

    Hashtbl.iter
      (fun key value ->
        (* Evaluate value with current map *)
        let new_value =
          match value with
          | EVar v -> (
              try
                let replacement = Hashtbl.find map v in
                  changed := true;
                  replacement
              with Not_found -> value
            )
          | _ -> value
        in
          Hashtbl.replace new_map key new_value
      )
      map;

    if !changed then compute_fixed_point new_map else new_map
  in

  let final_map = compute_fixed_point fix_rf_map in

  (* produce final register environment by merging register environment at
       all terminal events. There are multiple terminal events across
       multiple threads. *)
  let final_env = Hashtbl.create 16 in
    USet.iter
      (fun lbl ->
        let evt = Hashtbl.find_opt structure.events lbl |> Option.get in
          if evt.typ = Terminal then
            let reg_env =
              Hashtbl.find_opt structure.p lbl
              |> Option.value ~default:(Hashtbl.create 0)
            in
              Hashtbl.iter
                (fun reg expr ->
                  (* The register environment also carries the path's UB
                       assumptions, keyed by a prefix no register can have
                       (see [Interpret.ub_fact_prefix]). They are facts for
                       elaboration, not part of the observable state. *)
                  if not (String.starts_with ~prefix:"%ub:" reg) then
                    Hashtbl.add final_env reg expr
                )
                reg_env
      )
      freeze_res.e;

    (* Create execution *)
    let exec =
      {
        id;
        e = freeze_res.e;
        rf = freeze_res.rf;
        dp = freeze_res.dp;
        ppo = freeze_res.ppo;
        rmw = freeze_res.rmw;
        fwd = freeze_res.fwd;
        we = freeze_res.we;
        ex_p = freeze_res.pp;
        justifications = freeze_res.justs;
        co = None;
        fix_rf_map = final_map;
        pointer_map = None;
        final_env;
      }
    in
      exec

(** [generate_executions ?include_rf structure justs statex ~restrictions]
    generates all valid executions.

    This is the main entry point for execution generation. The algorithm: 1.
    Generates all maximal conflict-free paths 2. For each path, combines
    justifications for writes 3. Freezes each combination to create executions
    4. Deduplicates and minimizes results 5. Filters for memory model coherence

    Uses streaming processing to handle large result sets efficiently.

    @param include_rf Whether to compute read-from relations (default: true).
    @param structure The symbolic event structure.
    @param justs Set of justifications from elaboration.
    @param statex Static constraints.
    @param restrictions Coherence restrictions to check.
    @param compare_models
      Further coherence models to check every execution against (default: none).
      They do not filter anything.
    @param admissions
      Filled with, for each execution reaching the coherence stage, the models
      of [compare_models] that admit it -- executions [restrictions] rejects
      included.
    @param model_executions
      Filled with, for each model of [compare_models], the executions it admits,
      each a copy carrying the coherence order that model admitted it under.
    @return Promise of list of valid coherent executions. *)
let generate_executions ?(include_rf = true) ?(compute = sequential_compute)
    ?(witnesses = false) ?(compare_models = []) ?admissions ?model_executions
    (structure : symbolic_event_structure)
    (fwd_es_ctx : Forwarding.event_structure_context)
    (justs : justification list) statex ~restrictions =
  (* let* _ = Lwt.return_unit in *)
  Logs_safe.debug (fun m ->
      m "Generating executions for structure with %d events:\n%s"
        (USet.size structure.e)
        (Hashtbl.fold
           (fun _ evt acc -> acc ^ "  " ^ show_event evt ^ "\n")
           structure.events ""
        )
  );

  (* Generate all paths through the control flow *)
  let paths = generate_max_conflictfree_sets structure in
  (* Have short paths first to see results through the streaming pipeline
     earlier *)
  let paths =
    List.sort
      (fun p1 p2 -> compare (USet.size p1.path) (USet.size p2.path))
      paths
  in

  Logs_safe.debug (fun m ->
      m "Generated %d paths through the structure" (List.length paths)
  );

  (* S4 (measure the waste ratio): count the stream size at each pipeline seam
     so the built-then-discarded ratio per test is visible. Enabled via
     [MORDOR_S4_COUNTERS]. Pure instrumentation — [count_stage] is the identity
     on the stream. *)
  if !s4_counters then
    Logs_safe.info (fun m -> m "[S4] paths: %d" (List.length paths));

  (* Build justification map: write event label -> list of justifications *)
  (* Not filtered for elided origins here, and it cannot be: whether a
     justification's symbol origins are elided depends on the fwd edges of the
     combination it ends up in, and no combination exists yet. The filtering
     happens where the information does -- JustValidation.check_partial calls
     check_origins_elided on each binding as the combination is built. *)
  let justmap = Hashtbl.create 16 in
    List.iter
      (fun (just : justification) ->
        let label = just.w.label in
        let existing = try Hashtbl.find justmap label with Not_found -> [] in
          Hashtbl.replace justmap label (just :: existing)
      )
      justs;

    let stream_freeze input_stream =
      let* input_stream = input_stream in
      let input_stream =
        if Option.is_none S10.samples && Option.is_none S12.stride then
          input_stream
        else
          let kept =
            List.filteri (fun i _ -> i mod S10.combo_stride = 0) input_stream
          in
            S10.print "S10 combos=%d frozen=%d" (List.length input_stream)
              (List.length kept);
            kept
      in
      (* Every model an execution will be asked about, so that a relation is
         dropped early only if each of them would reject it. *)
      let coherence_models =
        List.sort_uniq String.compare
          ((restrictions : Coherence.restrictions).coherent :: compare_models)
      in
      (* R13 (#99): instead of every result of every combination, one
         witness per future. Each combination has one future (S14, #91), so
         the futures need, per future, one combination with a result the
         model admits -- and one minimality would not remove: a result is
         removed when a combination with the same events and smaller [dp] and
         [ppo] has one with the same read-from, so a witness must not have a
         read-from valid for a combination that dominates its own. That rule
         gives the enumerated futures exactly (S14). *)
      let witness_stage prepared =
        let digest x =
          Digest.string (Marshal.to_string x [ Marshal.No_sharing ])
        in
        let sorted s = USet.values s |> List.sort compare in
        let kinds =
          let seen = Hashtbl.create 64 in
            List.filter_map
              (fun (_, _, _, prepared) ->
                match prepared with
                | Some (key, p) when not (Hashtbl.mem seen key) ->
                    Hashtbl.replace seen key ();
                    Some (key, p)
                | _ -> None
              )
              prepared
            |> Array.of_list
        in
        let frames =
          Array.map (fun (_, p) -> Freeze.frame_of structure p) kinds
        in
        let by_events = Hashtbl.create 64 in
          Array.iteri
            (fun i (e, _, _) ->
              let k = digest (sorted e) in
                Hashtbl.replace by_events k
                  (i
                  :: (Hashtbl.find_opt by_events k |> Option.value ~default:[])
                  )
            )
            frames;
          let dominators i =
            let e, dp, ppo = frames.(i) in
              List.filter
                (fun j ->
                  let _, dp', ppo' = frames.(j) in
                    j <> i
                    && USet.subset dp' dp
                    && USet.subset ppo' ppo
                    && not (USet.equal dp' dp && USet.equal ppo' ppo)
                )
                (Hashtbl.find by_events (digest (sorted e)))
          in
          (* Kinds with the same future, in order: the first with a witness
             stands for all of them. *)
          let groups =
            let order = ref [] and members = Hashtbl.create 64 in
              Array.iteri
                (fun i (e, dp, ppo) ->
                  let k =
                    digest
                      ( sorted e,
                        sorted (URelation.restrict e (USet.union dp ppo))
                      )
                  in
                    match Hashtbl.find_opt members k with
                    | Some l -> Hashtbl.replace members k (i :: l)
                    | None ->
                        order := k :: !order;
                        Hashtbl.replace members k [ i ]
                )
                frames;
              List.rev_map (fun k -> List.rev (Hashtbl.find members k)) !order
          in
          let model = (restrictions : Coherence.restrictions).coherent in
          let admits fr =
            Option.is_some
              (check_for_coherence structure
                 (execution_of_freeze_result structure ~include_rf ~id:0 fr)
                 restrictions
              )
          in
          let decide group =
            let rec go tried undecided = function
              | [] -> (None, tried, undecided)
              | i :: rest -> (
                  let key, p = kinds.(i) in
                  (* A dominating combination's results are what {!enumerate}
                     gives it, so its read-froms are tested as it would find
                     them, with the models it prunes by. *)
                  let valid_in =
                    List.map
                      (fun j ->
                        Freeze.valid_rf ~coherence_models structure
                          (snd kinds.(j))
                      )
                      (dominators i)
                  in
                  let reject (fr : FreezeResult.t) =
                    List.exists (fun valid -> valid fr.rf) valid_in
                  in
                    match
                      Freeze.witness ~model ~coherence_models:[ model ] ~admits
                        ~reject structure p
                    with
                    | Freeze.Witness fr -> (Some (key, fr), tried + 1, undecided)
                    | Freeze.No_witness -> go (tried + 1) undecided rest
                    | Freeze.Undecided -> go (tried + 1) (undecided + 1) rest
                )
            in
              go 0 0 group
          in
            let* decided =
              compute.run ~stage:("witnesses", "futures") decide groups
            in
            let witnessed = Hashtbl.create 64 in
              List.iter
                (fun (found, _, _) ->
                  Option.iter
                    (fun (key, fr) -> Hashtbl.replace witnessed key fr)
                    found
                )
                decided;
              let tried = List.fold_left (fun n (_, t, _) -> n + t) 0 decided in
              let open_futures =
                List.length
                  (List.filter
                     (fun (found, _, u) -> found = None && u > 0)
                     decided
                  )
              in
                Logs_safe.info (fun m ->
                    m
                      "Futures from witnesses: %d combinations, %d kinds, %d \
                       futures to decide; %d witnessed; %d kinds searched, %d \
                       skipped for a future already witnessed"
                      (List.length prepared) (Array.length kinds)
                      (List.length groups) (Hashtbl.length witnessed) tried
                      (Array.length kinds - tried)
                );
                if open_futures > 0 then
                  Logs_safe.warn (fun m ->
                      m
                        "Futures may be incomplete: for %d of %d possible \
                         futures no witness was found and some combination was \
                         undecided within the budgets (MORDOR_WITNESS_ROUNDS, \
                         MORDOR_WITNESS_SECS)"
                        open_futures (List.length groups)
                  );
                List.concat_map
                  (fun (fwd, we, just_combo, prepared) ->
                    match prepared with
                    | Some (key, _) -> (
                        match Hashtbl.find_opt witnessed key with
                        | Some (fr : FreezeResult.t) ->
                            [
                              {
                                fr with
                                fwd = USet.clone fwd;
                                we = USet.clone we;
                                justs = just_combo;
                              };
                            ]
                        | None -> []
                      )
                    | None -> []
                  )
                  prepared
                |> Lwt.return
      in
      let prepare_combo (path, just_combo) =
        let fwd =
          List.fold_left
            (fun acc j -> USet.union acc j.fwd)
            (USet.create ()) just_combo
        in
        let we =
          List.fold_left
            (fun acc j -> USet.union acc j.we)
            (USet.create ()) just_combo
        in
        let con = ForwardingContext.create fwd_es_ctx ~fwd ~we () in
        let j_remapped =
          List.map (fun j -> ForwardingContext.remap_just con j) just_combo
        in
        let elided = URelation.pi_2 (USet.union fwd we) in
        let constraints =
          List.flatten (List.map (fun (j : justification) -> j.p) just_combo)
        in
        let prepared =
          Freeze.prepare structure fwd_es_ctx path j_remapped statex ~elided
            ~constraints
        in
          ( fwd,
            we,
            just_combo,
            Option.map (fun p -> (Freeze.duplicate_key p, p)) prepared
          )
      in
        let* prepared =
          compute.run
            ~stage:("prepare", "combinations")
            prepare_combo input_stream
        in
          if witnesses && include_rf then witness_stage prepared
          else
            (* Combinations that differ only in their forwarding and elision edges
         freeze to the same results, and deduplication merged those results
         afterwards. Each is frozen once, the first of its kind, and its
         results are given to every combination of the kind. On the litmus
         corpus that is more than half of all combinations (S11). *)
            (* S11 measures duplicates, so it sees every combination. *)
            let merge = !Freeze.merge_duplicates && not S11.enabled in
            let distinct =
              let seen = Hashtbl.create 64 in
                List.filter_map
                  (fun (_, _, _, prepared) ->
                    match prepared with
                    | Some (key, p) when merge && not (Hashtbl.mem seen key) ->
                        Hashtbl.replace seen key ();
                        Some (key, p)
                    | Some (key, p) when not merge -> Some (key, p)
                    | _ -> None
                  )
                  prepared
            in
              if !s4_counters then
                Logs_safe.info (fun m ->
                    m "[S4] combinations frozen: %d of %d"
                      (List.length distinct) (List.length prepared)
                );
              let* frozen =
                compute.run
                  ~stage:("freeze", "kinds of combination")
                  (fun (key, p) ->
                    ( key,
                      Freeze.enumerate ~coherence_models structure p ~include_rf
                    )
                  )
                  distinct
              in
              let by_key = Hashtbl.create 64 in
                List.iter
                  (fun (key, results) -> Hashtbl.replace by_key key results)
                  frozen;
                (* Without merging, keys still repeat; each combination then takes its
           own results, in order. *)
                let own = ref frozen in
                let results_of key =
                  if merge then Hashtbl.find by_key key
                  else
                    match !own with
                    | (_, results) :: rest ->
                        own := rest;
                        results
                    | [] -> assert false
                in
                let results =
                  List.map
                    (fun (fwd, we, just_combo, prepared) ->
                      match prepared with
                      | None -> []
                      | Some (key, _) ->
                          let freeze_results = results_of key in
                            Logs_safe.debug (fun m ->
                                m
                                  "Computed %d freeze results with %d \
                                   justifications"
                                  (List.length freeze_results)
                                  (List.length just_combo)
                            );
                            (* The forwarding context is the combination's, not the
                       freeze's, so it is attached here.  Each result gets its
                       own copy: deduplication unions into whichever it keeps,
                       and sharing would make that union visible to results it
                       never applied to. *)
                            List.map
                              (fun (fr : FreezeResult.t) ->
                                {
                                  fr with
                                  fwd = USet.clone fwd;
                                  we = USet.clone we;
                                  justs = just_combo;
                                }
                              )
                              freeze_results
                    )
                    prepared
                in
                  if S11.enabled then S11.report ();
                  List.flatten results |> Lwt.return
    in

    let stream_freeze_to_execution input_stream =
      let* input_stream = input_stream in
      let id = ref 0 in
      let freeze_to_execution (freeze_res : FreezeResult.t) =
        let exec =
          execution_of_freeze_result structure ~include_rf ~id:!id freeze_res
        in

        (* Increment executiion counter *)
        id := !id + 1;

        Logs_safe.debug (fun m ->
            m "Generated execution with %d events, %d RF edges:\n%s"
              (USet.size exec.e) (USet.size exec.rf)
              (show_symbolic_execution exec)
        );

        exec
      in

      let compute input_stream =
        List.map freeze_to_execution input_stream |> Lwt.return
      in

      compute input_stream
    in

    let dedup_freeze_results stream =
      Logs_safe.debug (fun m -> m "Deduplicating freeze results...");
      (* Duplicates are the same execution reached through different forwarding
         contexts.  Keeping the first and dropping the rest loses every context
         but one, so the kept result absorbs theirs. *)
      let seen = FreezeResultCache.create 1024 in
        let* stream = stream in
          List.filter_map
            (fun (fr : FreezeResult.t) ->
              match FreezeResultCache.find_opt seen fr with
              | Some (kept : FreezeResult.t) ->
                  ignore (USet.inplace_union ~into:kept.fwd fr.fwd);
                  ignore (USet.inplace_union ~into:kept.we fr.we);
                  FreezeResult.merge_justs kept fr;
                  None
              | None ->
                  FreezeResultCache.add seen fr fr;
                  Some fr
            )
            stream
          |> Lwt.return
    in

    (* The minimality passes compared every result with every other, and on
       rcu-3-2t-trunc, with 19,000 freeze results, that was minutes each.
       Only results with the same events can contain one another, and so they
       are compared within buckets of equal keys. A key is a string: a list
       would be hashed on its first few elements alone, and these share long
       prefixes. *)
    let sorted u = USet.values u |> List.sort compare in
    let key_of l = Marshal.to_string l [ Marshal.No_sharing ] in
    let buckets key xs =
      let tbl = Hashtbl.create 64 in
        List.iteri
          (fun i x ->
            let k = key x in
              Hashtbl.replace tbl k
                ((i, x) :: (Hashtbl.find_opt tbl k |> Option.value ~default:[]))
          )
          xs;
        tbl
    in

    (* A freeze result contains another only if the two have the same events
       and the same read-from ([FreezeResult.contains]). *)
    let keep_minimal_freeze_results fr_list =
      Logs_safe.debug (fun m -> m "Keeping minimal freeze results...");
      let* fr_list = fr_list in
      let key (fr : FreezeResult.t) = key_of (sorted fr.e, sorted fr.rf) in
      let by_key = buckets key fr_list in
        List.filteri
          (fun i (fr1 : FreezeResult.t) ->
            (* Is fr1 contained by another? Keep it if not. *)
            not
              (List.exists
                 (fun (j, fr2) -> i <> j && FreezeResult.contains fr1 fr2)
                 (Hashtbl.find by_key (key fr1))
              )
          )
          fr_list
        |> Lwt.return
    in

    (* An execution contains another only if the two have the same events and
       its read-from includes the other's ([Execution.contains]). Within a
       bucket of equal events the candidates are those with the same
       read-from, and those whose read-from is strictly larger and includes
       it. *)
    let keep_minimal_executions exec_list =
      Logs_safe.debug (fun m -> m "Keeping minimal executions...");
      let* exec_list = exec_list in
      let events_key (ex : symbolic_execution) = key_of (sorted ex.e) in
      let by_events = buckets events_key exec_list in
      (* Per bucket of events: its members by read-from, each sub-bucket with
         its read-from, and the size of the largest. *)
      let by_rf = Hashtbl.create (Hashtbl.length by_events) in
        Hashtbl.iter
          (fun events members ->
            let sub = Hashtbl.create 16 in
              List.iter
                (fun ((_, (ex : symbolic_execution)) as m) ->
                  let rf = sorted ex.rf in
                  let k = key_of rf in
                  let _, ms =
                    Hashtbl.find_opt sub k |> Option.value ~default:(rf, [])
                  in
                    Hashtbl.replace sub k (rf, m :: ms)
                )
                members;
              let largest =
                Hashtbl.fold (fun _ (rf, _) n -> max n (List.length rf)) sub 0
              in
                Hashtbl.replace by_rf events (sub, largest)
          )
          by_events;
        List.filteri
          (fun i (exec1 : symbolic_execution) ->
            let sub, largest = Hashtbl.find by_rf (events_key exec1) in
            let rf1 = sorted exec1.rf in
            let contained_in members =
              List.exists
                (fun (j, exec2) -> i <> j && Execution.contains exec2 exec1)
                members
            in
              not
                (contained_in (snd (Hashtbl.find sub (key_of rf1)))
                || List.length rf1 < largest
                   && Hashtbl.fold
                        (fun _ (rf2, members) found ->
                          found
                          || List.compare_lengths rf2 rf1 > 0
                             && List.for_all (fun p -> List.mem p rf2) rf1
                             && contained_in members
                        )
                        sub false
                )
          )
          exec_list
        |> Lwt.return
    in

    let dedup_executions stream =
      Logs_safe.debug (fun m -> m "Deduplicating executions...");
      let* stream = stream in
      let seen = ExecutionCache.create 1024 in
      let predicates (ex : symbolic_execution) =
        List.map Expr.to_string ex.ex_p
      in

      (* As in dedup_freeze_results: merge the forwarding contexts of executions
         that collapse together instead of keeping one arbitrarily.

         Duplicates agree on events and relations but not always on how their
         predicates are written: equivalent predicates reached along different
         justifications come out in different forms. The survivor takes the
         least in rendering, so which form it reports does not depend on the
         order duplicates arrive in -- which is the order some set happened to
         be iterated in. It keeps the id of the first. *)
      let kept =
        List.filter_map
          (fun (ex : symbolic_execution) ->
            match ExecutionCache.find_opt seen ex with
            | Some kept ->
                let (k : symbolic_execution) = !kept in
                  ignore (USet.inplace_union ~into:k.fwd ex.fwd);
                  ignore (USet.inplace_union ~into:k.we ex.we);
                  (* Same reason the forwarding contexts are merged: the
                     duplicate is this execution reached from a different
                     justification combination, and keeping only the
                     survivor's would under-report what justified it. *)
                  let seen = Hashtbl.create (List.length k.justifications) in
                    List.iter
                      (fun j ->
                        Hashtbl.replace seen (Justification.to_string j) ()
                      )
                      k.justifications;
                    k.justifications <-
                      k.justifications
                      @ List.filter
                          (fun j ->
                            let key = Justification.to_string j in
                              if Hashtbl.mem seen key then false
                              else (
                                Hashtbl.replace seen key ();
                                true
                              )
                          )
                          ex.justifications;
                    if compare (predicates ex) (predicates k) < 0 then
                      kept := { k with ex_p = ex.ex_p };
                    None
            | None ->
                let kept = ref ex in
                  ExecutionCache.add seen ex kept;
                  Some kept
          )
          stream
      in
        List.map ( ! ) kept |> Lwt.return
    in

    let stream_filter_coherent_executions input_stream =
      let* input_stream = input_stream in
      (* Every execution is checked against the compared models too, whether or
         not the primary admits it. Enumeration up to here does not depend on
         the coherence model, so this is each model's own execution set -- as
         long as the models agree on everything decided before coherence, which
         for the UB fold they need not (see [Context.select_models]). *)
      let check_exec exec =
        let admitted_by =
          List.filter_map
            (fun coherent ->
              check_for_coherence structure exec { Coherence.coherent }
              |> Option.map (fun co -> (coherent, co))
            )
            compare_models
        in
          if Option.is_none S10.samples && not S10.locality then (
            let co = check_for_coherence structure exec restrictions in
              if Option.is_some co then Progress.found ~unit:"admitted" 1;
              (exec, co, admitted_by)
          )
          else
            let t = Unix.gettimeofday () in
            let co = check_for_coherence structure exec restrictions in
              if Option.is_some S10.samples then
                S10.print
                  "S10 coherence id=%d events=%d rf=%d admitted=%b ms=%.0f"
                  exec.id (USet.size exec.e) (USet.size exec.rf)
                  (Option.is_some co)
                  ((Unix.gettimeofday () -. t) *. 1000.);
              (* The per-location check must never reject what the model
                 admits. *)
              if S10.locality then
                S10.print "S10 soundness model=%s admitted=%b local=%b"
                  restrictions.coherent (Option.is_some co)
                  (Coherence.rejected_by_one_location structure exec
                     restrictions
                  );
              (exec, co, admitted_by)
      in
        let* results =
          compute.run ~stage:("coherence", "executions") check_exec input_stream
        in
          Option.iter
            (fun tbl ->
              List.iter
                (fun ((exec : symbolic_execution), _, admitted_by) ->
                  List.iter
                    (fun (coherent, co) ->
                      let kept =
                        Hashtbl.find_opt tbl coherent
                        |> Option.value ~default:[]
                      in
                        Hashtbl.replace tbl coherent
                          ({ exec with co = Some co } :: kept)
                    )
                    admitted_by
                )
                (List.rev results)
            )
            model_executions;
          List.filter_map
            (fun (exec, co, admitted_by) ->
              Option.iter
                (fun tbl ->
                  Hashtbl.replace tbl exec.id (List.map fst admitted_by)
                )
                admissions;
              match co with
              | Some co ->
                  (* Keep the order that admitted it, so the export and any
                     [.co] assertion can be read against the same witness. *)
                  exec.co <- Some co;
                  Some exec
              | None -> None
            )
            results
          |> Lwt.return
    in

    (* Build justcombos for all paths *)
    let* executions =
      compute_justification_combinations compute structure paths
        ~scope:(justifiable structure) justmap
      |> count_stage "justification-combos"
      |> stream_freeze
      |> count_stage "freeze-results (rf-combos)"
      |> dedup_freeze_results
      |> keep_minimal_freeze_results
      |> count_stage "freeze-results after dedup+minimality"
      |> stream_freeze_to_execution
      |> dedup_executions
      |> keep_minimal_executions
      |> count_stage "executions before coherence"
      |> stream_filter_coherent_executions
      |> count_stage "executions after coherence"
    in
      Logs_safe.debug (fun m ->
          m "Minimized to %d executions" (List.length executions)
      );

      Lwt.return executions

(** Calculate dependencies and justifications *)

(** [calculate_dependencies ?include_rf structure final_justs fwd_es_ctx
     ~exhaustive ~restrictions] is the main function to calculate dependencies
    and generate executions.

    This function orchestrates the entire execution generation process by: 1.
    Computing constraints for disjointness of memory allocations 2. Generating
    executions 3. Applying coherence restrictions

    The dependency relations are generated as part of the executions.

    @param include_rf Whether to compute read-from relations (default: true).
    @param structure The symbolic event structure.
    @param final_justs Set of justifications from elaboration.
    @param fwd_es_ctx Forwarding event structure context for PPO computation.
    @param exhaustive
      Whether to exhaustively explore all combinations (default: false).
    @param restrictions Coherence restrictions to check.
    @return Promise of list of valid coherent executions. *)
let calculate_dependencies ?(include_rf = true) ?(num_threads = 1) ?witnesses
    ?compare_models ?admissions ?model_executions
    (structure : symbolic_event_structure) (final_justs : justification list)
    (fwd_es_ctx : Forwarding.event_structure_context) ~(exhaustive : bool)
    ~(restrictions : Coherence.restrictions) : symbolic_execution list Lwt.t =
  Logs_safe.debug (fun m -> m "Generating executions...");

  (* Compute statex: allocation disjointness constraints *)

  (* 1. Extract static/global locations from all events *)
  let static_locs =
    USet.values structure.e
    |> List.filter_map (Events.get_loc structure)
    |> List.filter Expr.is_var
    |> List.sort_uniq compare (* Remove duplicates and sort *)
  in

  (* 2. Extract malloc locations *)
  let malloc_locs =
    (* In label order: each pair below is written in the order the two come
       in, and a set's own order would decide which way round. *)
    USet.values structure.malloc_events
    |> List.sort compare
    |> List.filter_map (fun eid ->
        match Hashtbl.find_opt structure.events eid with
        | Some evt -> Option.map Expr.of_value evt.rval
        | None -> None
    )
  in

  (* 3. Combine both sets *)
  let all_locs = static_locs @ malloc_locs in

  (* 4. Create pairwise disjointness for ALL distinct locations, save two
     allocations one of which may be freed before the other is made: the
     allocator may hand the freed address straight back out. *)
  let statex =
    let may_reuse = may_reuse structure in
    let pairs = ref [] in
      for i = 0 to List.length all_locs - 1 do
        for j = i + 1 to List.length all_locs - 1 do
          let loc1 = List.nth all_locs i in
          let loc2 = List.nth all_locs j in
            if not (may_reuse loc1 loc2) then
              pairs := Expr.binop loc1 "!=" loc2 :: !pairs
        done
      done;
      !pairs @ structure.constraints
  in

  (* Build compute_fn: sequential for 1 thread, otherwise the process's pool,
     the same one the elaboration phase dispatched on. *)
  let compute =
    match Parallel.acquire ~num_threads with
    | Some pool -> parallel_compute pool
    | None -> sequential_compute
  in

  (* Build executions if not just structure *)
  let* executions =
    generate_executions ~include_rf ~compute ?witnesses ?compare_models
      ?admissions ?model_executions structure fwd_es_ctx final_justs statex
      ~restrictions
  in

  Logs_safe.debug (fun m ->
      m "Executions generated: %d" (List.length executions)
  );

  Lwt.return executions

(** [step_calculate_dependencies lwt_ctx] is the main entry point for the
    dependency calculation step. It checks for necessary data, sets up coherence
    restrictions, and calls [calculate_dependencies] to produce executions.

    @param lwt_ctx Promise of current Mordor context.
    @return Promise of updated Mordor context with executions. *)
let step_calculate_dependencies (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t
    =
  let* ctx = lwt_ctx in
    Progress.stage ~unit:"" "executions" @@ fun () ->
    (* Create restrictions for coherence checking *)
    let coherence_restrictions =
      { Coherence.coherent = ctx.options.coherent }
    in
      match (ctx.structure, ctx.justifications, ctx.num_threads) with
      | Some structure, Some final_justs, num_threads ->
          (* The models the assertions name, besides the primary, are checked
           as compared models are: every execution, once enumerated. *)
          let assertion_models =
            List.filter
              (fun m -> m <> ctx.options.coherent)
              ctx.assertion_models
            |> List.sort_uniq String.compare
          in
          let checked_models =
            List.sort_uniq String.compare (ctx.compare_models @ assertion_models)
          in
            List.iter
              (Coherence.check_model_program structure)
              (ctx.options.coherent :: checked_models);
            let* fwd_es_ctx =
              match ctx.fwd_es_ctx with
              | Some fwd_es_ctx -> Lwt.return fwd_es_ctx
              | None ->
                  let fwd_es_ctx =
                    Forwarding.EventStructureContext.create structure
                  in
                    ctx.fwd_es_ctx <- Some fwd_es_ctx;
                    let* () =
                      Forwarding.EventStructureContext.init fwd_es_ctx
                    in
                      Lwt.return fwd_es_ctx
            in
            let admissions =
              match ctx.compare_models with
              | [] -> None
              | _ -> Some (Hashtbl.create 64)
            in
            let model_executions =
              match assertion_models with
              | [] -> None
              | _ -> Some (Hashtbl.create 8)
            in
              let* executions =
                calculate_dependencies ~num_threads
                  ~witnesses:ctx.options.futures_by_witness
                  ~compare_models:checked_models ?admissions ?model_executions
                  structure final_justs fwd_es_ctx
                  ~exhaustive:(ctx.options.exhaustive || false)
                  ~restrictions:coherence_restrictions
              in
                (* Admissions report the models asked to be compared, not those
               checked only for an assertion. *)
                Option.iter
                  (fun tbl ->
                    Hashtbl.filter_map_inplace
                      (fun _ models ->
                        Some
                          (List.filter
                             (fun m -> List.mem m ctx.compare_models)
                             models
                          )
                      )
                      tbl
                  )
                  admissions;
                ctx.executions <- Some (USet.of_list executions);
                ctx.model_admissions <- admissions;
                ctx.model_executions <- model_executions;
                Lwt.return ctx
      | _ ->
          Logs_safe.err (fun m ->
              m
                "Program statements or litmus constraints not available, \
                 orjustifications not available"
          );
          Lwt.return ctx
