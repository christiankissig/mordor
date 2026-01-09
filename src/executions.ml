open Algorithms
open Coherence
open Events
open Eventstructures
open Expr
open Lwt.Syntax
open Types
open Uset

(** {1 Basic Types} *)

module Execution = struct
  type t = symbolic_execution

  let equal ex1 ex2 =
    USet.equal ex1.ex_e ex2.ex_e
    && USet.equal ex1.dp ex2.dp
    && USet.equal ex1.ppo ex2.ppo
    && USet.equal ex1.rf ex2.rf

  let hash ex =
    let hash_list lst =
      List.fold_left (fun acc e -> Hashtbl.hash (acc, e)) 0 lst
    in
    let hash_uset uset = USet.values uset |> List.sort compare |> hash_list in
      Hashtbl.hash
        (hash_uset ex.ex_e, hash_uset ex.dp, hash_uset ex.ppo, hash_uset ex.rf)

  (** [exec1 exec2] Check whether exec1 subsumes exec2.

      @param exec1 First symbolic execution
      @param exec2 Second symbolic execution
      @return true if exec1 contains exec2, false otherwise *)
  let contains exec1 exec2 =
    USet.equal exec2.ex_e exec1.ex_e
    && USet.subset exec2.dp exec1.dp
    && USet.subset exec2.ppo exec1.ppo
    && USet.subset exec2.rf exec1.rf
    && not
         (USet.equal exec1.rf exec2.rf
         && USet.equal exec1.ppo exec2.ppo
         && USet.equal exec1.dp exec2.dp
         )

  let to_string exec = show_symbolic_execution exec

  (** Get relation by name from structure/execution *)
  let get_relation name (structure : symbolic_event_structure)
      (execution : symbolic_execution) =
    match name with
    | ".ppo" -> execution.ppo
    | ".po" -> structure.po
    | ".rf" -> execution.rf
    | ".dp" -> execution.dp
    | ".rmw" -> execution.ex_rmw
    | _ ->
        Logs.warn (fun m ->
            m "Unknown or unsupported relation: %s, returning empty" name
        );
        USet.create ()
end

module ExecutionCacheKey = struct
  type t = symbolic_execution

  let equal = Execution.equal
  let hash = Execution.hash
end

module ExecutionCache = Hashtbl.Make (ExecutionCacheKey)

module FreezeResult = struct
  (** Type for a freeze function - validates an RF set for a justification
      combination *)
  type t = {
    e : int uset;
    dp : (int * int) uset;
    ppo : (int * int) uset;
    rf : (int * int) uset;
    rmw : (int * int) uset;
    pp : expr list;
    conds : expr list;
  }

  let equal fr1 fr2 =
    USet.equal fr1.e fr2.e
    && USet.equal fr1.dp fr2.dp
    && USet.equal fr1.ppo fr2.ppo
    && USet.equal fr1.rf fr2.rf
    && USet.equal fr1.rmw fr2.rmw
    && List.equal Expr.equal fr1.pp fr2.pp
    && List.equal Expr.equal fr1.conds fr2.conds

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

  (** [fr1 fr2] Check whether fr1 subsumes fr2. *)
  let contains fr1 fr2 =
    USet.equal fr2.e fr1.e
    && USet.subset fr2.dp fr1.dp
    && USet.subset fr2.ppo fr1.ppo
    && USet.subset fr2.rf fr1.rf
    && not
         (USet.equal fr1.rf fr2.rf
         && USet.equal fr1.ppo fr2.ppo
         && USet.equal fr1.dp fr2.dp
         )
end

module FreezeResultCacheKey = struct
  type t = FreezeResult.t

  let equal = FreezeResult.equal
  let hash = FreezeResult.hash
end

module FreezeResultCache = Hashtbl.Make (FreezeResultCacheKey)

(** {1 Utilities} *)

(** Create disjoint predicate for two (location, value) pairs *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

(** {1 RF Validation} *)

module ReadFromValidation = struct
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

  let check_rf_elided rf delta =
    USet.size (USet.intersection (URelation.pi_2 delta) (URelation.pi_1 rf)) = 0

  let check_rf_total rf read_events delta =
    USet.subset
      (USet.set_minus read_events (URelation.pi_2 delta))
      (URelation.pi_2 rf)

  let env_rf structure rf =
    USet.map
      (fun (w, r) ->
        (* TODO this look-up logic is contrived *)
        let w_val = vale structure w r in
          match get_val structure r with
          | Some r_val ->
              Expr.evaluate (Expr.binop w_val "=" r_val) (fun _ -> None)
          | None -> failwith ("Read event " ^ string_of_int r ^ " has no value!")
      )
      rf

  let check_rf structure rf =
    USet.map
      (fun (w, r) ->
        (* TODO this look-up logic is contrived *)
        let w_loc = loce structure w r in
          match get_loc structure r with
          | Some r_loc ->
              Expr.evaluate (Expr.binop w_loc "=" r_loc) (fun _ -> None)
          | None ->
              failwith ("Read event " ^ string_of_int r ^ " has no location!")
      )
      rf

  (** Compute pairs of allocation events at same location without intermediate
      free events given read-from environment *)
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

module JustValidation = struct
  (** Check if any origins of symbols in justification D are elided by fwd
      edges. Consider fwd edges, and not we edges, as origins are read events.
  *)
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

  (** Whether if any edges in delta are not on the path *)
  let check_delta_not_on_path just path =
    let just_delta = USet.union just.fwd just.we in
    let just_delta_events =
      USet.union (URelation.pi_1 just_delta) (URelation.pi_2 just_delta)
    in
      USet.subset just_delta_events path.path

  (** Check partial combination of justifications for early pruning. Used in
      Algorithms.ListMapCombinationBuilder. *)
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
               alt != just
               && just.w = alt.w (*given*)
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
                 alt != just
                 && just.w = alt.w (*given*)
                 && USet.subset alt.fwd fwd
                 && USet.subset alt.we we
                 && USet.subset alt.d just.d
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

  (** Check final combination of justifications. Used in
      ListMapCombinationBuilder. *)
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

    let*? () = (URelation.acyclic delta, "cyclic delta relation") in

    let*? () =
      ( URelation.is_function (URelation.exhaustive_closure delta),
        "non-functional delta relation"
      )
    in

    let* satisfiable =
      List.map (fun (just : justification) -> just.p) combo
      |> List.flatten
      |> List.append path.p
      |> List.map (fun expr -> Expr.evaluate expr (fun _ -> None))
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
                      (show_justification just)
                  )
                  combo
               )
            )
      );

      Lwt.return true
end

(** {1 Freezing} *)

(** Instantiate execution from justification list and read-from relation. If
    successful returns optional freeze result. *)
let instantiate_execution (structure : symbolic_event_structure) path dp ppo
    j_list (pp : expr list) p_combined rf =
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

    let e = path.path in
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
    (* Filter RMW pairs *)
    let rmw_filtered =
      (* TODO does this make sense if RMW pair lies out side of execution? *)
      USet.filter (fun (f, t) -> USet.mem e f || USet.mem e t) structure.rmw
    in

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
                              (fun _ -> None)
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
                  rmw = rmw_filtered;
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

(** [structure path elided constraints statex ppo dp p_combined] Compute
    candidate read-from relations for given path.

    @param structure Symbolic Event Structure
    @param path Path information
    @param elided Set of elided events
    @param constraints Additional constraints
    @param statex State expressions
    @param ppo
      Preserved program order relation implied by justifications on path
    @param dp Dependency relation implied by justifications on path
    @param p_combined Combined predicates from justifications on path *)
let compute_path_rf structure path ~elided ~constraints statex ppo dp p_combined
    =
  let landmark = Landmark.register "compute_path_rf" in
    Landmark.enter landmark;
    let write_events =
      USet.set_minus (USet.intersection structure.write_events path.path) elided
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

    let ( let*? ) (condition, msg) f =
      if condition then f () else Lwt.return false
    in

    let preds = path.p @ constraints @ statex |> USet.of_list |> USet.values in

    (* w must not be po-after r *)
    let po =
      USet.intersection structure.po (URelation.cross path.path path.path)
    in
    let po_inv = URelation.inverse_relation po in
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
            let w, r = rf_edge in
            let r_restrict =
              Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
            in
              (* Check that loc(w) = loc(r) is satisfiable *)
              let* loc_eq =
                match (get_loc structure w, get_loc structure r) with
                | Some loc_w, Some loc_r ->
                    Solver.expoteq ~state:preds loc_w loc_r
                | _ ->
                    Logs.debug (fun m ->
                        m
                          "[compute_path_rf] Edge (%d->%d) rejected: missing \
                           location"
                          w r
                    );
                    Lwt.return false
              in
                let*? () =
                  if not loc_eq then
                    Logs.debug (fun m ->
                        m
                          "[compute_path_rf] Edge (%d->%d) rejected: locations \
                           not equal"
                          w r
                    );
                  (loc_eq, "RF locs not equal")
                in
                  (* Check that writes are not shadowed for read-from *)
                  let* has_dslwb = dslwb structure w r in
                    let*? () =
                      if has_dslwb then
                        Logs.debug (fun m ->
                            m
                              "[compute_path_rf] Edge (%d->%d) rejected: \
                               shadowed (dslwb)"
                              w r
                        );
                      (not has_dslwb, "RF edge is shadowed (dslwb)")
                    in
                      Lwt.return true
          )
          w_cross_r_minus_po
      in

      Logs.debug (fun m ->
          m "[compute_path_rf] After loc/shadow filtering: %d valid RF edges"
            (USet.size all_rf)
      );

      let dp_ppo = USet.union dp ppo in
      let dp_ppo_tc = URelation.transitive_closure dp_ppo in

      (* exclude rf edges that form immediate cycles with ppo and dp *)
      let all_rf_inv = URelation.inverse_relation all_rf in
      let all_rf_inv_before_cycle = URelation.inverse_relation all_rf in
      let all_rf_inv =
        USet.filter (fun (r, w) -> not (USet.mem dp_ppo_tc (r, w))) all_rf_inv
      in

      Logs.debug (fun m ->
          m
            "[compute_path_rf] After cycle filtering: %d edges (removed %d \
             that would create immediate cycles)"
            (USet.size all_rf_inv)
            (USet.size all_rf_inv_before_cycle - USet.size all_rf_inv)
      );

      Logs.debug (fun m ->
          m "  Found %d initial RF edges for path: %s" (USet.size all_rf_inv)
            (String.concat ", "
               (List.map
                  (fun (r, w) -> Printf.sprintf "(%d->%d)" r w)
                  (USet.values all_rf_inv)
               )
            )
      );

      let all_rf_inv_map = URelation.adjacency_list_map all_rf_inv in
        Logs.debug (fun m ->
            m "[compute_path_rf] Building combinations for %d reads"
              (Hashtbl.length all_rf_inv_map)
        );
        let* rf_candidates =
          ListMapCombinationBuilder.build_combinations all_rf_inv_map
            ~check_partial:(fun combo ?alternatives pair ->
              let r, w = pair in
                Logs.debug (fun m ->
                    m
                      "[compute_path_rf] Testing partial combo: edge (%d->%d), \
                       combo size %d"
                      r w (List.length combo)
                );
                let new_combo_inv =
                  URelation.inverse_relation (USet.of_list (pair :: combo))
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
                  let* result = Solver.is_sat_cached combined_preds in
                    if not result then begin
                      Logs.debug (fun m ->
                          m
                            "[compute_path_rf] Partial combo rejected (unsat): \
                             edge (%d->%d), combo size %d"
                            r w (List.length combo)
                      );
                      (* Log the problematic constraints *)
                      let r_val = get_val structure r in
                      let w_val = get_val structure w in
                      let w_val_for_r = vale structure w r in
                        Logs.debug (fun m ->
                            m
                              "  Read %d expects value: %s, Write %d has \
                               value: %s, vale(w,r): %s"
                              r
                              ( match r_val with
                              | Some v -> Expr.to_string v
                              | None -> "None"
                              )
                              w
                              ( match w_val with
                              | Some v -> Expr.to_string v
                              | None -> "None"
                              )
                              (Expr.to_string w_val_for_r)
                        );
                        Logs.debug (fun m ->
                            m "  env_rf constraints: [%s]"
                              (String.concat "; "
                                 (List.map Expr.to_string (USet.values env_rf))
                              )
                        );
                        let p_combined_sample =
                          let rec take n lst =
                            match (n, lst) with
                            | 0, _ | _, [] -> []
                            | n, x :: xs -> x :: take (n - 1) xs
                          in
                            take 5 p_combined
                        in
                          Logs.debug (fun m ->
                              m "  p_combined constraints (first 5): [%s]"
                                (String.concat "; "
                                   (List.map Expr.to_string p_combined_sample)
                                )
                          )
                    end;
                    Logs.debug (fun m ->
                        m
                          "[compute_path_rf] Partial combo %s: edge (%d->%d), \
                           combo size %d"
                          (if result then "accepted" else "rejected")
                          r w (List.length combo)
                    );
                    Lwt.return result
            )
            (USet.values read_events) ()
        in
          Logs.debug (fun m ->
              m "[compute_path_rf] Generated %d RF combinations"
                (List.length rf_candidates)
          );
          Landmark.exit landmark;
          Lwt.return rf_candidates

(** Creates executions from a list of justifications for a given path. *)
let freeze (structure : symbolic_event_structure) path j_list init_ppo statex
    ~elided ~constraints ~include_rf =
  let landmark = Landmark.register "freeze" in
    Landmark.enter landmark;

    Logs.debug (fun m ->
        m
          "[freeze] Starting freeze for path with %d events, %d \
           justifications, %d elided events"
          (USet.size path.path) (List.length j_list) (USet.size elided)
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

    (* Compute dependency relation *)
    let dp =
      List.concat_map
        (fun just ->
          (* take symbols from the justifications predicate and the d set *)
          let syms =
            List.map Expr.get_symbols just.p
            |> List.flatten
            |> USet.of_list
            |> USet.union just.d
            |> USet.values
          in
            List.concat_map
              (fun sym ->
                match origin structure sym with
                | Some orig -> [ (orig, just.w.label) ]
                | None -> []
              )
              syms
        )
        j_list
      |> USet.of_list
    in

    Logs.debug (fun m ->
        m "[freeze] Computed dependency relation dp with %d edges:\n %s"
          (USet.size dp)
          (USet.to_string (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) dp)
    );

    (* Compute combined fwd and we *)
    let f = List.map (fun j -> j.fwd) j_list |> USet.of_list |> USet.flatten in
    let we = List.map (fun j -> j.we) j_list |> USet.of_list |> USet.flatten in

    (* Create forwarding context *)
    let con = Forwardingcontext.create ~fwd:f ~we () in

    (* Combine predicates *)
    let p_combined =
      List.concat_map (fun (j : justification) -> j.p) j_list
      @ con.psi
      @ path.p
      @ statex
      |> USet.of_list
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
          (List.length con.psi)
          (String.concat "; " (List.map Expr.to_string con.psi))
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
        (* Compute PPO for each justification *)
        let* ppos =
          Lwt_list.map_s
            (fun just ->
              let just_con =
                Forwardingcontext.create ~fwd:just.fwd ~we:just.we ()
              in
                let* ppo_j = Forwardingcontext.ppo just_con just.p in

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
        let* ppo_loc_base = Forwardingcontext.ppo_loc con p_combined in
        let ppo_loc =
          USet.union ppo_loc_base init_ppo
          (* Filter out read-read pairs *)
          |> USet.filter (fun (a, b) ->
              not
                (USet.mem structure.read_events a
                && USet.mem structure.read_events b
                )
          )
          |> USet.intersection e_squared
          |> URelation.transitive_closure
        in

        let ppo =
          List.fold_left USet.inplace_union (USet.create ()) ppos
          |> USet.inplace_union (Forwardingcontext.ppo_sync con)
          |> USet.inplace_union init_ppo
          |> USet.inplace_union ppo_loc
          |> USet.intersection e_squared
          |> URelation.transitive_closure
        in

        Logs.debug (fun m ->
            m "[freeze] Computed PPO: %d edges, PPO_loc: %d edges"
              (USet.size ppo) (USet.size ppo_loc)
        );

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
              m "[freeze] Starting instantiate_execution for %d RF combinations"
                (List.length all_rf)
          );
          let all_validations =
            List.map
              (fun rf ->
                instantiate_execution structure path dp ppo j_list path.p
                  p_combined rf
              )
              all_rf
          in
            let* results = Lwt.all all_validations in
            let filtered_results = List.filter_map Fun.id results in
              Logs.debug (fun m ->
                  m
                    "[freeze] instantiate_execution produced %d valid results \
                     from %d RF combos"
                    (List.length filtered_results)
                    (List.length all_rf)
              );
              Landmark.exit landmark;
              Lwt.return filtered_results

(** Compute justification combinations for write events on path. *)
let compute_justification_combinations structure paths init_ppo statex
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

(** Main execution generation - replaces the stub in calculate_dependencies.

    @param structure Symbolic Event Structure
    @param justs Set of justifications
    @param statex State expressions
    @param init_ppo Initial preserved program order relation
    @param restrictions Restrictions on execution generation
    @param include_rf Whether to include read-from relations in the executions.

 *)
let generate_executions ?(include_rf = true)
    (structure : symbolic_event_structure) (justs : justification uset) statex
    init_ppo ~restrictions =
  let landmark = Landmark.register "generate_executions" in
    Landmark.enter landmark;

    (* let* _ = Lwt.return_unit in *)
    Logs.info (fun m ->
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

    Logs.info (fun m ->
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

      Logs.info (fun m -> m "Built justification map");

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
          let con = Forwardingcontext.create ~fwd ~we () in
          let j_remapped =
            List.map
              (fun j -> Forwardingcontext.remap_just con j None)
              just_combo
          in
          let elided = URelation.pi_2 (USet.inplace_union fwd we) in
          let constraints =
            List.flatten (List.map (fun (j : justification) -> j.p) just_combo)
          in

          let* freeze_results =
            freeze structure path j_remapped init_ppo statex ~elided
              ~constraints ~include_rf
          in
            Logs.info (fun m ->
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
                  ex_e = freeze_res.e;
                  rf = freeze_res.rf;
                  dp = freeze_res.dp;
                  ppo = freeze_res.ppo;
                  ex_rmw = freeze_res.rmw;
                  ex_p = freeze_res.pp;
                  fix_rf_map = final_map;
                  pointer_map = None;
                  final_env;
                }
              in

              (* Increment executiion counter *)
              id := !id + 1;

              Logs.info (fun m ->
                  m "Generated execution with %d events, %d RF edges"
                    (USet.size exec.ex_e) (USet.size exec.rf)
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
            if FreezeResultCache.mem seen fr then (
              Logs.debug (fun m -> m "Deduplicated freeze result");
              None
            )
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
            if ExecutionCache.mem seen ex then (
              Logs.debug (fun m -> m "Deduplicated execution");
              None
            )
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
                  (fun (j, fr2) -> i <> j && FreezeResult.contains fr2 fr1
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
        compute_justification_combinations structure paths init_ppo statex
          justmap
        |> stream_freeze
        |> dedup_freeze_results
        |> Lwt_stream.to_list
      in

      Logs.info (fun m ->
          m "Generated %d freeze results before minimization"
            (List.length freeze_results)
      );

      let minimal_freeze_results = keep_minimal_freeze_results freeze_results in
        Logs.info (fun m ->
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
