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

(** {1 Basic Types} *)

(** Operations on symbolic executions.

    Provides comparison, hashing, and subsumption checking for executions.
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
      names: [".ppo"], [".po"], [".rf"], [".dp"], [".rmw"].

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
    | _ ->
        Logs.warn (fun m ->
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
    pp : expr list;  (** Path predicates that must be satisfied. *)
    conds : expr list;  (** Additional conditions. *)
  }

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
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

(** {1 RF Validation} *)

(** Read-from relation validation.

    Validates that read-from relations satisfy various consistency requirements
    including PPO respect, totality, and semantic correctness. *)
module ReadFromValidation = struct
  (** [rf_respects_ppo rf ppo_loc] checks RF respects preserved program order.

      For each RF edge [(w,r)], if [(w,r)] is in [ppo_loc], then [r] must be
      reachable from [w] in the PPO relation (i.e., the edge must be direct).

      @param rf Read-from relation.
      @param ppo_loc Location-based PPO.
      @return [true] if all RF edges respect PPO. *)
  let rf_respects_ppo rf ppo_loc =
    let ppo_loc_tree = URelation.adjacency_map ppo_loc in
      USet.for_all
        (fun (w, r) ->
          if USet.mem ppo_loc (w, r) then
            (* If (w,r) in ppo_loc, check that r is reachable from w *)
            try
              let successors = Hashtbl.find ppo_loc_tree w in
                USet.mem successors r
            with Not_found -> false
          else true
        )
        rf

  (** [check_rf_elided rf delta] checks reads don't observe elided writes.

      Verifies that no read in RF reads from a write that has been elided
      (overwritten) by write-exclusion edges in delta.

      @param rf Read-from relation.
      @param delta Combined forwarding and write-exclusion edges.
      @return [true] if no elided writes are read. *)
  let check_rf_elided rf delta =
    USet.size (USet.intersection (URelation.pi_2 delta) (URelation.pi_1 rf)) = 0

  (** [check_rf_total rf read_events delta] checks RF is total.

      Verifies that every non-elided read has a read-from edge.

      @param rf Read-from relation.
      @param read_events Set of all read events.
      @param delta Combined forwarding and write-exclusion edges.
      @return [true] if RF covers all non-elided reads. *)
  let check_rf_total rf read_events delta =
    USet.subset
      (USet.set_minus read_events (URelation.pi_2 delta))
      (URelation.pi_2 rf)

  (** [env_rf structure rf] computes value equality constraints from RF.

      For each RF edge [(w,r)], creates constraint that the value read equals
      the value written (after accounting for forwarding).

      @param structure The event structure.
      @param rf Read-from relation.
      @return Set of value equality expressions. *)
  let env_rf structure rf =
    USet.map
      (fun (w, r) ->
        if w = 0 then None
        else
          (* TODO w_val should be retrieved from justification to account for
           elaborations *)
          let w_val = vale structure w r in
            match get_val structure r with
            | Some r_val -> Some (Expr.evaluate (Expr.binop w_val "=" r_val))
            | None ->
                failwith ("Read event " ^ string_of_int r ^ " has no value!")
      )
      rf
    (* TODO replace with filter_map *)
    |> fun constraints ->
    USet.fold
      (fun (acc : expr uset) (expr_opt : expr option) ->
        match expr_opt with
        | Some expr -> USet.add acc expr
        | None -> acc
      )
      constraints (USet.create ())

  (** [check_rf structure rf] computes location equality constraints.

      For each RF edge [(w,r)], creates constraint that locations match.

      @param structure The event structure.
      @param rf Read-from relation.
      @return Set of location equality expressions. *)
  let check_rf structure rf =
    USet.map
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
    (* TODO replace with filter_map *)
    |> fun constraints ->
    USet.fold
      (fun (acc : expr uset) (expr_opt : expr option) ->
        match expr_opt with
        | Some expr -> USet.add acc expr
        | None -> acc
      )
      constraints (USet.create ())

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

    USet.async_filter
      (fun (e_1, e_2) ->
        (* Check if there's no intermediate FREE event between e_1 and e_2 *)
        let* has_intermediate =
          USet.async_exists
            (fun ep ->
              if not (USet.mem rhb (e_1, ep) && USet.mem rhb (ep, e_2)) then
                Lwt.return_false
              else
                (* Check if loc(e_1) = loc(ep) under env_rf using semeq *)
                match (get_loc structure e_1, get_loc structure ep) with
                | None, _ | _, None -> Lwt.return_false
                | Some loc_e1, Some loc_ep -> Solver.exeq ~state:p loc_e1 loc_ep
            )
            free_events
        in
          Lwt.return (not has_intermediate)
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

    let ( let*? ) (condition, msg) f =
      if condition then f () else Lwt.return false
    in

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

          Lwt.return true

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

    let ( let*? ) (condition, msg) f =
      if condition then f () else Lwt.return false
    in

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

    let* satisfiable =
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

      Logs.debug (fun m ->
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

      Lwt.return true
end

(** {1 Freezing} *)

(** [instantiate_execution structure path dp ppo j_list pp p_combined rf]
    creates execution from justifications and RF.

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
    @param rf Read-from relation to validate.
    @return Promise of [Some freeze_result] if valid, [None] otherwise. *)
let instantiate_execution (structure : symbolic_event_structure) path dp ppo
    j_list (pp : expr list) p_combined rf elided =
  let landmark = Landmark.register "instantiate_execution" in
    Landmark.enter landmark;

    Logs.debug (fun m ->
        m
          "  [instantiate_execution] Starting validation for RF with %d edges: \
           %s"
          (USet.size rf)
          (String.concat ", "
             (List.map
                (fun (w, r) -> Printf.sprintf "(%d->%d)" w r)
                (USet.values rf)
             )
          )
    );

    (* let* _ = Lwt.return_unit in *)
    let ( let*? ) (condition, msg) f =
      if condition then f ()
      else (
        Logs.debug (fun m -> m "  [instantiate_execution] Rejected: %s" msg);
        Landmark.exit landmark;
        Lwt.return_none
      )
    in

    (* remove elided events from execution *)
    let e = USet.set_minus path.path elided in
    let e_squared = URelation.cross e e in

    (* Filter dp and ppo to execution events only *)
    let dp = USet.intersection dp e_squared in
    let ppo = USet.intersection ppo e_squared in

    let po = USet.intersection structure.po (URelation.cross e e) in
    let read_events = USet.intersection structure.read_events e in
    let write_events = USet.intersection structure.write_events e in

    (* Check 3: All rf edges respect ppo_loc *)
    Logs.debug (fun m ->
        m
          "  [instantiate_execution] Checking RF respects PPO (PPO has %d \
           edges)"
          (USet.size ppo)
    );
    let*? () =
      (ReadFromValidation.rf_respects_ppo rf ppo, "RF edges do not respect PPO")
    in

    (* Filter RMW relation to execution events and predicates only *)
    let* rmw_filtered =
      USet.async_filter
        (fun (er, expr, ew) ->
          Solver.exeq ~state:p_combined expr (EBoolean true)
        )
        structure.rmw
    in
    let rmw = USet.map (fun (er, _, ew) -> (er, ew)) rmw_filtered in

    (* Check 1.1: Various consistency checks *)
    let delta =
      USet.inplace_union
        (List.fold_left
           (fun acc j -> USet.inplace_union acc j.fwd)
           (USet.create ()) j_list
        )
        (List.fold_left
           (fun acc j -> USet.inplace_union acc j.we)
           (USet.create ()) j_list
        )
    in

    Logs.debug (fun m ->
        m "  [instantiate_execution] Delta (fwd U we) has %d edges"
          (USet.size delta)
    );

    (* TODO this should be given by generation *)
    let*? () =
      (ReadFromValidation.check_rf_elided rf delta, "RF fails RF elided check")
    in
      Logs.debug (fun m -> m "  [instantiate_execution] RF elided check passed");
      let*? () =
        ( ReadFromValidation.check_rf_total rf read_events delta,
          "RF fails RF total check"
        )
      in
        Logs.debug (fun m ->
            m
              "  [instantiate_execution] RF total check passed (reads: %d, RF \
               edges: %d)"
              (USet.size read_events) (USet.size rf)
        );

        (* Check acyclicity of rhb = dp_ppo ∪ rf *)
        let dp_ppo = USet.union dp ppo in
        let rhb = USet.union dp_ppo rf in
          Logs.debug (fun m ->
              m
                "  [instantiate_execution] Checking RHB acyclicity (dp: %d, \
                 ppo: %d, rf: %d, rhb: %d)"
                (USet.size dp) (USet.size ppo) (USet.size rf) (USet.size rhb)
          );
          if not (URelation.acyclic rhb) then (
            Logs.debug (fun m ->
                m "dp = %s"
                  (USet.to_string
                     (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                     dp
                  )
            );
            Logs.debug (fun m ->
                m "ppo = %s"
                  (USet.to_string
                     (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                     ppo
                  )
            );
            Logs.debug (fun m ->
                m "rf = %s"
                  (USet.to_string
                     (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
                     rf
                  )
            )
          );
          (* TODO discern memory model *)
          let*? () = (URelation.acyclic rhb, "RHB is not acyclic") in
            Logs.debug (fun m ->
                m "  [instantiate_execution] RHB acyclicity check passed"
            );

            (* Create environment from RF *)
            let env_rf = ReadFromValidation.env_rf structure rf in
            let check_rf = ReadFromValidation.check_rf structure rf in

            (* atomicity constraint *)
            let* af =
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
                        ("Event " ^ string_of_int a ^ " not found in structure!")
                  | _, None ->
                      failwith
                        ("Event " ^ string_of_int b ^ " not found in structure!")
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
                            ("Event " ^ string_of_int a ^ " has no location!")
                      | _, None, _, _ ->
                          failwith
                            ("Event " ^ string_of_int a ^ " has no value!")
                      | _, _, None, _ ->
                          failwith
                            ("Event " ^ string_of_int b ^ " has no location!")
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
              |> USet.inplace_union env_rf
              |> USet.inplace_union check_rf
              |> USet.inplace_union disj
              |> USet.filter (fun e -> not (Expr.equal e (EBoolean true)))
              |> USet.values
              |> List.sort Expr.compare
            in

            Logs.debug (fun m ->
                m
                  "  [instantiate_execution] Checking satisfiability of %d \
                   predicates (env_rf: %d, check_rf: %d, disj: %d, p_combined: \
                   %d)"
                  (List.length execution_predicates)
                  (USet.size env_rf) (USet.size check_rf) (USet.size disj)
                  (List.length p_combined)
            );

            (* Check satisfiability of combined predicates *)
            let* satisfiable = Solver.is_sat_cached execution_predicates in
              Logs.debug (fun m ->
                  m "  [instantiate_execution] Satisfiability check result: %b"
                    satisfiable
              );
              let*? () = (satisfiable, "unsatisfiable combined predicates") in

              (* Success! Return the freeze result *)
              let freeze_result : FreezeResult.t =
                {
                  e;
                  dp;
                  ppo;
                  rf;
                  rmw;
                  pp = execution_predicates;
                  conds = [ EBoolean true ];
                }
              in
                Logs.debug (fun m ->
                    m
                      "  [instantiate_execution] SUCCESS! Created freeze \
                       result with %d events, %d RF edges"
                      (USet.size e) (USet.size rf)
                );
                Landmark.exit landmark;
                Lwt.return_some freeze_result

(** [compute_path_rf structure path ~elided ~constraints statex ppo dp
     p_combined] computes candidate read-from relations.

    Generates all valid read-from combinations for the given path by: 1.
    Filtering potential RF edges by location equality 2. Checking edges don't
    violate program order 3. Verifying writes aren't shadowed 4. Building
    combinations incrementally with satisfiability checking

    @param structure The event structure.
    @param path Current path.
    @param elided Set of elided events.
    @param constraints Additional constraints.
    @param statex Static constraints.
    @param ppo Preserved program order.
    @param dp Dependency relation.
    @param p_combined Combined predicates.
    @return
      Promise of list of RF combinations (as lists of [(read, write)] pairs). *)
let compute_path_rf structure path ~elided ~constraints statex ppo dp p_combined
    =
  let landmark = Landmark.register "compute_path_rf" in
    Landmark.enter landmark;
    let write_events =
      USet.intersection structure.write_events path.path |> fun e ->
      USet.set_minus e elided |> fun e -> USet.add e 0 (* include init write *)
    in
    let read_events =
      USet.set_minus (USet.intersection structure.read_events path.path) elided
    in
    let w_with_init = USet.union write_events (USet.singleton 0) in
    let w_cross_r = URelation.cross w_with_init read_events in

    Logs.debug (fun m ->
        m
          "[compute_path_rf] Starting RF computation: %d writes (+ init), %d \
           reads, %d potential edges"
          (USet.size write_events) (USet.size read_events) (USet.size w_cross_r)
    );

    let preds = path.p @ constraints @ statex |> USet.of_list |> USet.values in

    (* w must not be po-after r *)
    let po =
      USet.intersection structure.po (URelation.cross path.path path.path)
    in
    let po_inv = URelation.inverse po in
    let w_cross_r_minus_po = USet.set_minus w_cross_r po_inv in
      Logs.debug (fun m ->
          m
            "[compute_path_rf] After PO filtering: %d edges (removed %d edges \
             where w po-after r)"
            (USet.size w_cross_r_minus_po)
            (USet.size w_cross_r - USet.size w_cross_r_minus_po)
      );
      let* all_rf =
        USet.async_filter
          (fun rf_edge ->
            let landmark = Landmark.register "compute_path_rf_edge_filter" in
              Landmark.enter landmark;
              let ( let*? ) (condition, msg) f =
                if condition then f ()
                else (
                  Landmark.exit landmark;
                  Lwt.return false
                )
              in
              let w, r = rf_edge in
              let r_restrict =
                Hashtbl.find_opt structure.restrict r
                |> Option.value ~default:[]
              in
                (* Check that loc(w) = loc(r) is satisfiable *)
                let* loc_eq =
                  if w = 0 then
                    (* init write: skip location check *)
                    Lwt.return true
                  else
                    match (get_loc structure w, get_loc structure r) with
                    | Some loc_w, Some loc_r ->
                        Solver.expoteq ~state:preds loc_w loc_r
                    | _ -> Lwt.return false
                in
                  let*? () = (loc_eq, "RF locs not equal") in
                    (* Check that writes are not shadowed for read-from *)
                    let* has_dslwb = dslwb structure w r in
                      let*? () =
                        (not has_dslwb, "RF edge is shadowed (dslwb)")
                      in
                        Landmark.exit landmark;
                        Lwt.return true
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
        let* rf_candidates =
          ListMapCombinationBuilder.build_combinations all_rf_inv_map
            ~check_partial:(fun combo ?alternatives pair ->
              let r, w = pair in
                (* discard the combination if we have alternatives to reading
                   from init *)
                if
                  w = 0
                  && Option.map (fun alts -> List.length alts > 1) alternatives
                     |> Option.value ~default:false
                then Lwt.return false
                else
                  let new_combo_inv =
                    URelation.inverse (USet.of_list (pair :: combo))
                  in
                  let env_rf =
                    ReadFromValidation.env_rf structure new_combo_inv
                  in
                  let check_rf =
                    ReadFromValidation.check_rf structure new_combo_inv
                  in
                  let combined_preds =
                    USet.of_list p_combined
                    |> USet.inplace_union env_rf
                    |> USet.inplace_union check_rf
                    |> USet.values
                  in
                    Solver.is_sat_cached combined_preds
            )
            (USet.values read_events) ()
        in
          Logs.debug (fun m ->
              m "[compute_path_rf] Generated %d RF combinations"
                (List.length rf_candidates)
          );
          Landmark.exit landmark;
          Lwt.return rf_candidates

module Freeze = struct
  (** [freeze_dp structure just] freezes semantic dependency relations from
      justification.

      @param structure The symbolic event structure.
      @param just The justification to freeze.
      @return The semantic dependency relation for symbols in just. *)
  let freeze_dp structure just =
    let landmark = Landmark.register "freeze_dp" in
      Landmark.enter landmark;
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
        Landmark.exit landmark;
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
    let landmark = Landmark.register "freeze_ppo" in
      Landmark.enter landmark;
      let fwd_es_ctx = fwd_ctx.es_ctx in
      let e_squared = URelation.cross path.path path.path in

      (* Compute PPO for each justification *)
      let* ppos =
        Lwt_list.map_s
          (fun just ->
            let just_con =
              ForwardingContext.create fwd_es_ctx ~fwd:just.fwd ~we:just.we ()
            in
              let* ppo_j = ForwardingContext.ppo just_con just.p in

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
              let po_to_w_squared =
                URelation.cross po_predecessors_and_w po_predecessors_and_w
              in
                Lwt.return (USet.intersection ppo_j po_to_w_squared)
          )
          j_list
      in

      (* Compute ppo_loc *)
      let* ppo_loc_base = ForwardingContext.ppo_loc fwd_ctx p_combined in
      let ppo_loc =
        USet.union ppo_loc_base fwd_es_ctx.ppo.ppo_init
        |> USet.intersection e_squared
        |> (fun rel ->
        USet.set_minus rel
          (URelation.cross structure.read_events structure.read_events)
        )
        |> URelation.transitive_closure
      in

      let ppo =
        List.fold_left USet.inplace_union (USet.create ()) ppos
        |> USet.inplace_union (ForwardingContext.ppo_sync fwd_ctx)
        |> USet.inplace_union fwd_es_ctx.ppo.ppo_init
        |> USet.inplace_union ppo_loc
        |> USet.intersection e_squared
        |> URelation.transitive_closure
      in

      Logs.debug (fun m ->
          m "[freeze] Computed PPO: %d edges, PPO_loc: %d edges" (USet.size ppo)
            (USet.size ppo_loc)
      );
      Landmark.exit landmark;
      Lwt.return (ppo, ppo_loc)

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
      @return Promise of list of valid freeze results. *)
  let freeze structure fwd_es_ctx path j_list statex ~elided ~constraints
      ~include_rf =
    let landmark = Landmark.register "Executions.freeze" in
      Landmark.enter landmark;

      Logs.debug (fun m ->
          m
            "[freeze] Starting freeze for path with %d events, %d \
             justifications, %d elided events\n\
             %s"
            (USet.size path.path) (List.length j_list) (USet.size elided)
            (String.concat "\n\t" (List.map Justification.to_string j_list))
      );

      (* let* _ = Lwt.return_unit in *)
      let ( let*? ) (condition, msg) f =
        if condition then f ()
        else (
          Logs.debug (fun m -> m "[freeze] Early exit: %s" msg);
          Landmark.exit landmark;
          Lwt.return []
        )
      in

      let e = path.path in
      let e_squared = URelation.cross e e in

      let read_events = USet.intersection structure.read_events e in
      let write_events = USet.intersection structure.write_events e in
      let malloc_events = USet.intersection structure.malloc_events e in
      let free_events = USet.intersection structure.free_events e in

      let justs = USet.of_list j_list in

      (* Compute combined fwd and we *)
      let fwd =
        USet.fold
          (fun acc just -> USet.inplace_union acc just.fwd)
          justs (USet.create ())
      in
      let we =
        USet.fold
          (fun acc just -> USet.inplace_union acc just.we)
          justs (USet.create ())
      in
      let delta = USet.union fwd we in

      (* Compute dependency relation *)
      let unelided_justs =
        USet.filter (fun j -> not (USet.mem elided j.w.label)) justs
      in

      let dp = USet.map (freeze_dp structure) unelided_justs |> USet.flatten in

      Logs.debug (fun m ->
          m "[freeze] Computed dependency relation dp with %d edges:\n %s"
            (USet.size dp)
            (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) dp)
      );

      (* Create forwarding context *)
      let fwd_ctx = ForwardingContext.create fwd_es_ctx ~fwd ~we () in

      (* Combine predicates *)
      let p_combined =
        USet.map (fun j -> USet.of_list j.p) justs
        |> USet.flatten
        |> USet.inplace_union (USet.of_list fwd_ctx.psi)
        |> USet.inplace_union (USet.of_list path.p)
        |> USet.inplace_union (USet.of_list statex)
        |> USet.values
        |> List.sort Expr.compare
      in

      (* Debug: Show all predicate sources *)
      Logs.debug (fun m ->
          m "[freeze] Path predicates (%d): [%s]" (List.length path.p)
            (String.concat "; " (List.map Expr.to_string path.p))
      );
      List.iteri
        (fun i j ->
          Logs.debug (fun m ->
              m "[freeze] Justification %d (event %d) predicates (%d): [%s]" i
                j.w.label (List.length j.p)
                (String.concat "; " (List.map Expr.to_string j.p))
          )
        )
        j_list;
      Logs.debug (fun m ->
          m "[freeze] Forwarding context predicates (%d): [%s]"
            (List.length fwd_ctx.psi)
            (String.concat "; " (List.map Expr.to_string fwd_ctx.psi))
      );
      Logs.debug (fun m ->
          m "[freeze] Statex predicates (%d): [%s]" (List.length statex)
            (String.concat "; " (List.map Expr.to_string statex))
      );
      Logs.debug (fun m ->
          m "[freeze] Combined p_combined (%d total predicates): [%s]"
            (List.length p_combined)
            (String.concat "; " (List.map Expr.to_string p_combined))
      );

      (* Check if predicates are satisfiable *)
      let* combined_p_sat = Solver.is_sat_cached p_combined in
        Logs.debug (fun m ->
            m
              "[freeze] Combined predicates satisfiable: %b (checked %d \
               predicates)"
              combined_p_sat (List.length p_combined)
        );
        let*? () = (combined_p_sat, "predicates unsatisfiable") in
          let* ppo, ppo_loc =
            freeze_ppo structure path j_list fwd_ctx p_combined
          in

          let* all_fr =
            if include_rf then
              compute_path_rf structure path ~elided ~constraints statex ppo dp
                p_combined
            else Lwt.return [ [] ]
          in
          let all_rf =
            List.map
              (fun fr -> List.map (fun (r, w) -> (w, r)) fr |> USet.of_list)
              all_fr
          in
            Logs.debug (fun m ->
                m "[freeze] Computed %d RF combination for path"
                  (List.length all_rf)
            );
            Logs.debug (fun m ->
                m
                  "[freeze] Starting instantiate_execution for %d RF \
                   combinations"
                  (List.length all_rf)
            );
            let all_validations =
              List.map
                (fun rf ->
                  instantiate_execution structure path dp ppo j_list path.p
                    p_combined rf elided
                )
                all_rf
            in
              let* results = Lwt.all all_validations in
              let filtered_results = List.filter_map Fun.id results in
                Logs.debug (fun m ->
                    m
                      "[freeze] instantiate_execution produced %d valid \
                       results from %d RF combos"
                      (List.length filtered_results)
                      (List.length all_rf)
                );
                Landmark.exit landmark;
                Lwt.return filtered_results
end

(** [compute_justification_combinations fwd_es_ctx structure paths statex
     justmap] computes justification combinations for all paths.

    For each path, builds all valid combinations of justifications for the write
    events on that path. Returns a stream of [(path, justifications)] pairs.

    @param fwd_es_ctx Forwarding event structure context for PPO computation.
    @param structure The event structure.
    @param paths List of all paths through the structure.
    @param statex Static constraints.
    @param justmap Hash table mapping write event IDs to justification lists.
    @return Stream of [(path, justification list)] pairs. *)
let compute_justification_combinations fwd_es_ctx structure paths statex
    (justmap : (int, justification list) Hashtbl.t) =
  (* Given a path, combine justifications for each write on the path. *)
  let combine_justifications_for_path path =
    let landmark = Landmark.register "combine_justifications_for_path" in
      Landmark.enter landmark;

      Logs.debug (fun m ->
          m "Building justification combinations for path [%s]"
            (String.concat ", "
               (List.map (Printf.sprintf "%d")
                  (List.sort compare (USet.values path.path))
               )
            )
      );

      let justifiable_events =
        USet.union structure.write_events structure.malloc_events
        |> USet.union structure.free_events
        |> USet.intersection path.path
      in

      let path_writes =
        USet.intersection path.path justifiable_events |> USet.values
      in

      (* TODO no need to select justifications for elided events *)
      let%lwt js_combinations =
        ListMapCombinationBuilder.build_combinations justmap path_writes
          ~check_partial:(fun combo ?alternatives just ->
            JustValidation.check_partial structure path combo ?alternatives just
          )
          ~check_final:(fun combo ->
            JustValidation.check_final structure path combo
          )
          ()
      in

      Logs.debug (fun m ->
          m "  Found %d justification combinations" (List.length js_combinations)
      );

      let result =
        List.map (fun combo -> (path, List.map snd combo)) js_combinations
      in
        Landmark.exit landmark;
        Lwt.return result
  in

  Lwt_stream.of_list paths
  |> Lwt_stream.map_list_s combine_justifications_for_path

(** {1 Generate executions} *)

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
    @return Promise of list of valid coherent executions. *)
let generate_executions ?(include_rf = true)
    (structure : symbolic_event_structure)
    (fwd_es_ctx : Forwarding.event_structure_context)
    (justs : justification uset) statex ~restrictions =
  let landmark = Landmark.register "generate_executions" in
    Landmark.enter landmark;

    (* let* _ = Lwt.return_unit in *)
    Logs.debug (fun m ->
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

    Logs.debug (fun m ->
        m "Generated %d paths through the structure" (List.length paths)
    );

    (* Build justification map: write event label -> list of justifications *)
    (* TODO remove justifications with elided origins *)
    let justmap = Hashtbl.create 16 in
      USet.iter
        (fun (just : justification) ->
          let label = just.w.label in
          let existing =
            try Hashtbl.find justmap label with Not_found -> []
          in
            Hashtbl.replace justmap label (just :: existing)
        )
        justs;

      let stream_freeze input_stream =
        let freeze_just_combo (path, just_combo) =
          let fwd =
            List.fold_left
              (fun acc j -> USet.inplace_union acc j.fwd)
              (USet.create ()) just_combo
          in
          let we =
            List.fold_left
              (fun acc j -> USet.inplace_union acc j.we)
              (USet.create ()) just_combo
          in
          let con = ForwardingContext.create fwd_es_ctx ~fwd ~we () in
          let j_remapped =
            List.map (fun j -> ForwardingContext.remap_just con j) just_combo
          in
          let elided = URelation.pi_2 (USet.inplace_union fwd we) in
          let constraints =
            List.flatten (List.map (fun (j : justification) -> j.p) just_combo)
          in

          let* freeze_results =
            Freeze.freeze structure fwd_es_ctx path j_remapped statex ~elided
              ~constraints ~include_rf
          in
            Logs.debug (fun m ->
                m
                  "Computed %d freeze results with %d justifications over path \
                   with %d events"
                  (List.length freeze_results)
                  (List.length just_combo) (USet.size path.path)
            );
            Lwt.return freeze_results
        in

        (* Use map_list_s to handle the list results and flatten them into the stream *)
        Lwt_stream.map_list_s freeze_just_combo input_stream
      in

      let stream_freeze_to_execution input_stream =
        let id = ref 0 in
        let freeze_to_execution (freeze_res : FreezeResult.t) =
          let landmark = Landmark.register "freeze_to_execution" in
            Landmark.enter landmark;
            (* Fixed point computation for RF mapping *)
            let fix_rf_map = Hashtbl.create 16 in

            (* Build initial mapping from RF *)
            if include_rf then
              USet.iter
                (fun (w, r) ->
                  (* TODO look up logic is contrived *)
                  let w_val = vale structure w r in
                    match get_val structure r with
                    | None ->
                        failwith
                          ("Read event " ^ string_of_int r ^ " has no value!")
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
                  let evt =
                    Hashtbl.find_opt structure.events lbl |> Option.get
                  in
                    if evt.typ = Terminal then
                      let reg_env =
                        Hashtbl.find_opt structure.p lbl
                        |> Option.value ~default:(Hashtbl.create 0)
                      in
                        Hashtbl.iter
                          (fun reg expr -> Hashtbl.add final_env reg expr)
                          reg_env
                )
                freeze_res.e;

              (* Create execution *)
              let exec =
                {
                  id = !id;
                  e = freeze_res.e;
                  rf = freeze_res.rf;
                  dp = freeze_res.dp;
                  ppo = freeze_res.ppo;
                  rmw = freeze_res.rmw;
                  ex_p = freeze_res.pp;
                  fix_rf_map = final_map;
                  pointer_map = None;
                  final_env;
                }
              in

              (* Increment executiion counter *)
              id := !id + 1;

              Logs.debug (fun m ->
                  m "Generated execution with %d events, %d RF edges:\n%s"
                    (USet.size exec.e) (USet.size exec.rf)
                    (show_symbolic_execution exec)
              );

              Landmark.exit landmark;
              Lwt.return exec
        in

        Lwt_stream.map_s freeze_to_execution input_stream
      in

      let stream_filter_coherent_executions input_stream =
        Lwt_stream.filter_s
          (fun exec -> check_for_coherence structure exec restrictions)
          input_stream
      in

      let dedup_freeze_results stream =
        let seen = FreezeResultCache.create 1024 in

        Lwt_stream.filter_map
          (fun fr ->
            if FreezeResultCache.mem seen fr then None
            else begin
              FreezeResultCache.add seen fr ();
              Some fr
            end
          )
          stream
      in

      let dedup_executions stream =
        let seen = ExecutionCache.create 1024 in

        Lwt_stream.filter_map
          (fun ex ->
            if ExecutionCache.mem seen ex then None
            else begin
              ExecutionCache.add seen ex ();
              Some ex
            end
          )
          stream
      in

      let keep_minimal_freeze_results fr_list =
        let indexed_list = List.mapi (fun i fr -> (i, fr)) fr_list in
          List.filter_map
            (fun (i, fr1) ->
              let is_contained =
                List.exists
                  (fun (j, fr2) -> i <> j && FreezeResult.contains fr1 fr2
                  ) (* Is fr1 contained by fr2? *)
                  indexed_list
              in
                if is_contained then None
                else Some fr1 (* Keep if NOT contained by any other *)
            )
            indexed_list
      in

      let keep_minimal_executions exec_list =
        let indexed_list = List.mapi (fun i exec -> (i, exec)) exec_list in
          List.filter_map
            (fun (i, exec1) ->
              let is_contained =
                List.exists
                  (fun (j, exec2) -> i <> j && Execution.contains exec2 exec1
                  ) (* Is exec1 contained by exec2? *)
                  indexed_list
              in
                if is_contained then None
                else Some exec1 (* Keep if NOT contained by any other *)
            )
            indexed_list
      in

      (* Build justcombos for all paths *)
      let* freeze_results =
        compute_justification_combinations fwd_es_ctx structure paths statex
          justmap
        |> stream_freeze
        |> dedup_freeze_results
        |> Lwt_stream.to_list
      in

      Logs.debug (fun m ->
          m "Generated %d freeze results before minimization"
            (List.length freeze_results)
      );

      let minimal_freeze_results = keep_minimal_freeze_results freeze_results in
        Logs.debug (fun m ->
            m "Minimized to %d freeze results"
              (List.length minimal_freeze_results)
        );

        let* executions =
          Lwt_stream.of_list minimal_freeze_results
          |> stream_freeze_to_execution
          |> dedup_executions
          |> stream_filter_coherent_executions
          |> Lwt_stream.to_list
        in

        Logs.debug (fun m ->
            m "Generated %d executions after coherence filtering"
              (List.length executions)
        );

        let minimal_executions = keep_minimal_executions executions in
          Logs.debug (fun m ->
              m "Minimized to %d executions" (List.length minimal_executions)
          );

          Landmark.exit landmark;
          Lwt.return minimal_executions

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
let calculate_dependencies ?(include_rf = true)
    (structure : symbolic_event_structure) (final_justs : justification uset)
    (fwd_es_ctx : Forwarding.event_structure_context) ~(exhaustive : bool)
    ~(restrictions : Coherence.restrictions) : symbolic_execution list Lwt.t =
  Logs.debug (fun m -> m "Generating executions...");

  (* Compute statex: allocation disjointness constraints *)

  (* 1. Extract static/global locations from all events *)
  let static_locs =
    USet.values structure.e
    |> List.filter_map (Events.get_loc structure)
    |> List.filter Expr.is_var
    |> List.sort_uniq compare (* Remove duplicates and sort *)
  in

  (* 2. Extract malloc locations *)
  (* TODO these constraints do not account for intermediate deallocation:

    • enforces the disjointness of symbolic memory locations introduced by
    consecutive allocation events, i.e. without an intermediate deallocation
    event.
    *)
  let malloc_locs =
    USet.values structure.malloc_events
    |> List.filter_map (fun eid ->
        match Hashtbl.find_opt structure.events eid with
        | Some evt -> Option.map Expr.of_value evt.rval
        | None -> None
    )
  in

  (* 3. Combine both sets *)
  let all_locs = static_locs @ malloc_locs in

  (* 4. Create pairwise disjointness for ALL distinct locations *)
  let statex =
    let pairs = ref [] in
      for i = 0 to List.length all_locs - 1 do
        for j = i + 1 to List.length all_locs - 1 do
          let loc1 = List.nth all_locs i in
          let loc2 = List.nth all_locs j in
            pairs := Expr.binop loc1 "!=" loc2 :: !pairs
        done
      done;
      !pairs @ structure.constraints
  in

  (* Build executions if not just structure *)
  let* executions =
    generate_executions ~include_rf structure fwd_es_ctx final_justs statex
      ~restrictions
  in

  Logs.debug (fun m -> m "Executions generated: %d" (List.length executions));

  Lwt.return executions

(** [step_calculate_dependencies lwt_ctx] is the main entry point for the
    dependency calculation step. It checks for necessary data, sets up coherence
    restrictions, and calls [calculate_dependencies] to produce executions.

    @param lwt_ctx Promise of current Mordor context.
    @return Promise of updated Mordor context with executions. *)
let step_calculate_dependencies (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t
    =
  let* ctx = lwt_ctx in

  (* Create restrictions for coherence checking *)
  Logs.debug (fun m ->
      m "Setting up coherence restrictions...%s" ctx.options.coherent
  );
  let coherence_restrictions =
    {
      Coherence.coherent =
        ( try ctx.options.coherent with _ -> "imm"
        )
        (* default to IMM if not specified *);
    }
  in
    match (ctx.structure, ctx.justifications) with
    | Some structure, Some final_justs ->
        let* fwd_es_ctx =
          match ctx.fwd_es_ctx with
          | Some fwd_es_ctx -> Lwt.return fwd_es_ctx
          | None ->
              let fwd_es_ctx =
                Forwarding.EventStructureContext.create structure
              in
                ctx.fwd_es_ctx <- Some fwd_es_ctx;
                let* () = Forwarding.EventStructureContext.init fwd_es_ctx in
                  Lwt.return fwd_es_ctx
        in
          let* executions =
            calculate_dependencies structure final_justs fwd_es_ctx
              ~exhaustive:(ctx.options.exhaustive || false)
              ~restrictions:coherence_restrictions
          in
            ctx.executions <- Some (USet.of_list executions);
            Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m
              "Program statements or litmus constraints not available, \
               orjustifications not available"
        );
        Lwt.return ctx
