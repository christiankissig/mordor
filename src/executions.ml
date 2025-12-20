open Lwt.Syntax
open Algorithms
open Coherence
open Events
open Expr
open Eventstructures
open Types
open Uset

let execution_equal ex1 ex2 =
  USet.equal ex1.ex_e ex2.ex_e
  && USet.equal ex1.dp ex2.dp
  && USet.equal ex1.ppo ex2.ppo
  && USet.equal ex1.rf ex2.rf

let execution_hash ex =
  let hash_list lst =
    List.fold_left (fun acc e -> Hashtbl.hash (acc, e)) 0 lst
  in
  let hash_uset uset = USet.values uset |> List.sort compare |> hash_list in
    Hashtbl.hash
      (hash_uset ex.ex_e, hash_uset ex.dp, hash_uset ex.ppo, hash_uset ex.rf)

module ExecutionCacheKey = struct
  type t = symbolic_execution

  let equal = execution_equal
  let hash = execution_hash
end

module ExecutionCache = Hashtbl.Make (ExecutionCacheKey)

module Execution = struct
  type t = symbolic_execution

  (** [exec1 exec2] Check if exec1 contains exec2, i.e. exec1 is a refinement of
      exec2.

      @param exec1 First symbolic execution
      @param exec2 Second symbolic execution
      @return true if exec1 contains exec2, false otherwise *)
  let contains exec1 exec2 =
    (* subset suffices as executions are over maximally consistent sets of
       events *)
    USet.subset exec2.ex_e exec1.ex_e
    && USet.subset exec2.dp exec1.dp
    && USet.subset exec2.ppo exec1.ppo
    && USet.subset exec2.rf exec1.rf
    && not
         (USet.equal exec1.rf exec2.rf
         && USet.equal exec1.ppo exec2.ppo
         && USet.equal exec1.dp exec2.dp
         )

  let to_string exec =
    let pp_uset_pair uset =
      let pairs =
        USet.values uset
        |> List.map (fun (a, b) -> Printf.sprintf "(%d, %d)" a b)
      in
        "{" ^ String.concat ", " pairs ^ "}"
    in
      Printf.sprintf
        "E: {%s}\n\
         DP: %s\n\
         PPO: %s\n\
         RF: %s\n\
         RMW: %s\n\
         PP: [%s]\n\
         FixRFMap: %s\n\
         PointerMap: %s\n"
        (String.concat ", " (List.map string_of_int (USet.values exec.ex_e)))
        (pp_uset_pair exec.dp) (pp_uset_pair exec.ppo) (pp_uset_pair exec.rf)
        (pp_uset_pair exec.ex_rmw)
        (String.concat ", " (List.map Expr.to_string exec.ex_p))
        (Hashtbl.fold
           (fun k v acc -> acc ^ k ^ " -> " ^ Expr.to_string v ^ "; ")
           exec.fix_rf_map ""
        )
        ( match exec.pointer_map with
        | Some pm ->
            Hashtbl.fold
              (fun k v acc ->
                acc ^ string_of_int k ^ " -> " ^ Value.to_string v ^ "; "
              )
              pm ""
        | None -> "None"
        )
end

(** Create disjoint predicate for two (location, value) pairs *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

module RFValidation = struct
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
end

module JustValidation = struct
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

  let check_delta_not_on_path just path =
    let just_delta = USet.union just.fwd just.we in
    let just_delta_events =
      USet.union (URelation.pi_1 just_delta) (URelation.pi_2 just_delta)
    in
      USet.subset just_delta_events path.path

  (* Check partial combination of justifications for early pruning. *)
  let check_partial_combo structure (path : path_info)
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

  (* Check final combination of justifications for validity. *)
  let check_final_combo structure (path : path_info)
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
      |> USet.of_list
      |> USet.values
      |> Solver.is_sat_cached
    in
      let*? () = (satisfiable, "unsatisfiable path predicates") in

      Lwt.return true
end

(** Freezing **)

(** Type for a freeze function - validates an RF set for a justification
    combination *)
type freeze_result = {
  justs : justification list;
  e : int uset;
  dp : (int * int) uset;
  ppo : (int * int) uset;
  rf : (int * int) uset;
  rmw : (int * int) uset;
  pp : expr list;
  conds : expr list;
}

let freeze_result_equal fr1 fr2 =
  USet.equal fr1.e fr2.e
  && USet.equal fr1.dp fr2.dp
  && USet.equal fr1.ppo fr2.ppo
  && USet.equal fr1.rf fr2.rf
  && USet.equal fr1.rmw fr2.rmw
  && List.equal Expr.equal fr1.pp fr2.pp
  && List.equal Expr.equal fr1.conds fr2.conds
  && List.equal
       (fun j1 j2 ->
         j1.w = j2.w
         && USet.equal j1.fwd j2.fwd
         && USet.equal j1.we j2.we
         && USet.equal j1.d j2.d
         && List.equal Expr.equal j1.p j2.p
       )
       fr1.justs fr2.justs

let freeze_result_hash fr =
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

module FreezeResultCacheKey = struct
  type t = freeze_result

  let equal = freeze_result_equal
  let hash = freeze_result_hash
end

module FreezeResultCache = Hashtbl.Make (FreezeResultCacheKey)

(** Compute atomicity pairs for a path given rhb and env_rf *)
let atomicity_pairs structure path rhb p =
  (* Compute atomicity pairs AF - matching JS implementation *)
  let e_set = path.path in
  let malloc_events = USet.intersection structure.malloc_events e_set in
  let free_events = USet.intersection structure.free_events e_set in
  (* Only compute pairs from malloc events, not reads *)
  let a = malloc_events in
  let a_squared = URelation.cross a a in

  USet.async_filter
    (fun (e_1, e_2) ->
      (* Match JS: e_1 < e_2 instead of checking po *)
      if e_1 >= e_2 then Lwt.return_false
      else
        (* Check if there's no intermediate FREE event between e_1 and e_2 *)
        let* has_intermediate =
          USet.async_exists
            (fun ep ->
              if not (USet.mem rhb (e_1, ep) && USet.mem rhb (ep, e_2)) then
                Lwt.return_false
              else
                (* Check if loc(e_1) = loc(ep) under env_rf using semeq *)
                match
                  (get_loc structure.events e_1, get_loc structure.events ep)
                with
                | None, _ | _, None -> Lwt.return_false
                | Some loc_e1, Some loc_ep -> Solver.exeq ~state:p loc_e1 loc_ep
            )
            free_events
        in
          Lwt.return (not has_intermediate)
    )
    a_squared

let validate_rf (structure : symbolic_event_structure) path ppo_loc dp ppo
    j_list (pp : expr list) p_combined rf =
  Logs.debug (fun m ->
      m
        "Validating RF with %d edges for justification combination with %d \
         justs"
        (USet.size rf) (List.length j_list)
  );

  (* Combine dp and ppo *)
  let dp_ppo = USet.union dp ppo in

  (* let* _ = Lwt.return_unit in *)
  let ( let*? ) (condition, msg) f =
    if condition then f ()
    else (
      Logs.debug (fun m -> m "  Rejected: %s" msg);
      Lwt.return_none
    )
  in

  let e = path.path in
  let po = USet.intersection structure.po (URelation.cross e e) in
  let read_events = USet.intersection structure.read_events e in
  let write_events = USet.intersection structure.write_events e in

  (* Check 3: All rf edges respect ppo_loc *)
  let*? () =
    (RFValidation.rf_respects_ppo rf ppo_loc, "RF edges do not respect PPO")
  in
  (* Filter RMW pairs *)
  let rmw_filtered =
    USet.filter (fun (f, t) -> USet.mem e f || USet.mem e t) structure.rmw
  in

  (* Create environment from RF *)
  let env_rf =
    USet.values rf
    |> List.map (fun (w, r) ->
        let just_w = List.find_opt (fun j -> j.w.label = w) j_list in
        let w_val =
          match just_w with
          | Some j -> vale structure.events j.w.label r
          | None -> vale structure.events w r
        in
          match get_val structure.events r with
          | Some r_val -> Expr.binop w_val "=" r_val
          | None -> failwith ("Read event " ^ string_of_int r ^ " has no value!")
    )
  in

  (* Check 1.1: Various consistency checks *)
  let delta =
    USet.union
      (List.fold_left
         (fun acc j -> USet.union acc j.fwd)
         (USet.create ()) j_list
      )
      (List.fold_left (fun acc j -> USet.union acc j.we) (USet.create ()) j_list)
  in

  Logs.debug (fun m -> m "  Delta has %d edges" (USet.size delta));
  Logs.debug (fun m ->
      m "  RF has %d edges: %s" (USet.size rf)
        (String.concat ", "
           (List.map
              (fun (w, r) -> Printf.sprintf "(%d -> %d)" w r)
              (USet.values rf)
           )
        )
  );
  Logs.debug (fun m ->
      m "  Read events %s"
        (String.concat ", " (List.map string_of_int (USet.values read_events)))
  );

  let*? () =
    (RFValidation.check_rf_elided rf delta, "RF fails RF elided check")
  in
    let*? () =
      ( RFValidation.check_rf_total rf read_events delta,
        "RF fails RF total check"
      )
    in
    (* Check acyclicity of rhb = dp_ppo ∪ rf *)
    let rhb = USet.union dp_ppo rf in

    let*? () = (URelation.acyclic rhb, "RHB is not acyclic") in

    (* Check 1.2: No downward-closed same-location writes before reads *)

    (* Rewrite predicates *)
    let check_rf =
      USet.values rf
      |> List.map (fun (w, r) ->
          let just_w = List.find_opt (fun j -> j.w.label = w) j_list in
          let w_loc =
            match just_w with
            | Some j -> loce structure.events j.w.label r
            | None -> loce structure.events w r
          in
            match get_loc structure.events r with
            | Some r_loc ->
                if Expr.compare w_loc r_loc < 0 then Expr.binop w_loc "=" r_loc
                else Expr.binop r_loc "=" w_loc
            | None ->
                failwith
                  ("Read event "
                  ^ string_of_int r
                  ^ " has no\n          location!"
                  )
      )
    in
    let big_p_exprs = p_combined @ env_rf @ check_rf in
      Logs.debug (fun m ->
          m
            "  Evaluating %d combined\n\
            \          predicates\n\
             \tp_combined=%s\n\
             \tenv_rf=%s\n\
             \tcheck_rf=%s"
            (List.length big_p_exprs)
            (String.concat ", " (List.map Expr.to_string p_combined))
            (String.concat ", " (List.map Expr.to_string env_rf))
            (String.concat ", " (List.map Expr.to_string check_rf))
      );
      let big_p =
        List.map (fun e -> Expr.evaluate e (fun _ -> None)) big_p_exprs
        |> List.filter (fun e -> not (Expr.equal e (EBoolean true)))
        |> USet.of_list
        |> USet.values
      in
        Logs.debug (fun m ->
            m "  Evaluated predicates:\n\t%s"
              (String.concat "\n\t" (List.map Expr.to_string big_p))
        );
        (* atomicity constraint *)
        let* af = atomicity_pairs structure path rhb env_rf in
          Logs.debug (fun m ->
              m "  Found %d atomicity pairs\n%s" (USet.size af)
                (String.concat "\n\t"
                   (List.map
                      (fun (a, b) -> Printf.sprintf "(%d, %d)" a b)
                      (USet.values af)
                   )
                )
          );

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
                    Logs.debug (fun m ->
                        m
                          "  Creating disjointness predicate for events %s and \
                           %s"
                          (show_event ea) (show_event eb)
                    );
                    match
                      ( get_loc structure.events a,
                        get_val structure.events a,
                        get_loc structure.events b,
                        get_val structure.events b
                      )
                    with
                    | None, _, _, _ ->
                        failwith
                          ("Event " ^ string_of_int a ^ " has no location!")
                    | _, None, _, _ ->
                        failwith ("Event " ^ string_of_int a ^ " has no value!")
                    | _, _, None, _ ->
                        failwith
                          ("Event " ^ string_of_int b ^ " has no location!")
                    | _, _, _, None ->
                        failwith ("Event " ^ string_of_int b ^ " has no value!")
                    | _ ->
                        let loc_a = get_loc structure.events a |> Option.get in
                        let val_a = get_val structure.events a |> Option.get in
                        let loc_b = get_loc structure.events b |> Option.get in
                        let val_b = get_val structure.events b |> Option.get in
                          (* disjoint only uses location *)
                          disjoint (loc_a, val_a) (loc_b, val_b)
                  )
              )
              af
            |> USet.values
          in
            Logs.debug (fun m ->
                m "  Created %d disjointness predicates\n\t%s" (List.length disj)
                  (String.concat "\n\t" (List.map Expr.to_string disj))
            );

            let bigger_p =
              List.map
                (fun expr -> Expr.evaluate expr (fun _ -> None))
                (big_p @ disj)
            in

            Logs.debug (fun m ->
                m "  Evaluating %d combined predicates with disjointness\n\t%s"
                  (List.length bigger_p)
                  (String.concat "\n\t" (List.map Expr.to_string bigger_p))
            );

            (* Check satisfiability of combined predicates *)

            (* Success! Return the freeze result *)
            let freeze_result =
              {
                justs = j_list;
                e;
                dp;
                ppo = dp_ppo;
                rf;
                rmw = rmw_filtered;
                pp = bigger_p;
                conds = [ EBoolean true ];
              }
            in
              Logs.debug (fun m -> m "  Freeze successful");
              Lwt.return_some freeze_result

(** Create a freeze function that validates RF sets for a justification
    combination *)
let create_freeze (structure : symbolic_event_structure) path j_list init_ppo
    statex =
  (* let* _ = Lwt.return_unit in *)
  let ( let*? ) (condition, msg) f =
    if condition then f () else Lwt.return_none
  in

  let e = path.path in
  let e_squared = URelation.cross e e in
  let pp = path.p in

  let read_events = USet.intersection structure.read_events e in
  let write_events = USet.intersection structure.write_events e in
  let malloc_events = USet.intersection structure.malloc_events e in

  (* Compute dependency relation *)
  let dp =
    List.concat_map
      (fun just ->
        let syms = USet.values just.d in
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

  (* Compute combined fwd and we *)
  let f = List.map (fun j -> j.fwd) j_list |> USet.of_list |> USet.flatten in
  let we = List.map (fun j -> j.we) j_list |> USet.of_list |> USet.flatten in

  (* Create forwarding context *)
  let con = Forwardingcontext.create ~fwd:f ~we () in

  (* Combine predicates *)
  let p_combined =
    List.concat_map (fun (j : justification) -> j.p) j_list
    @ con.psi
    @ pp
    @ statex
    |> USet.of_list
    |> USet.values
  in

  (* Check if predicates are satisfiable *)
  let* combined_p_sat = Solver.is_sat_cached p_combined in
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
              (* Intersect with po pairs ending at this write *)
              let po_to_w =
                USet.filter (fun (_, t) -> t = just.w.label) structure.po
              in
              let po_to_w_squared =
                URelation.cross (URelation.pi_1 po_to_w) (URelation.pi_1 po_to_w)
              in
                Lwt.return (USet.intersection ppo_j po_to_w_squared)
          )
          j_list
      in

      let ppo = List.fold_left USet.union (USet.create ()) ppos in
      let ppo = USet.union ppo (Forwardingcontext.ppo_sync con) in
      let ppo = USet.intersection ppo e_squared in

      (* Compute ppo_loc *)
      let* ppo_loc_base = Forwardingcontext.ppo_loc con p_combined in
      let ppo_loc = USet.union ppo_loc_base init_ppo in

      (* Filter out read-read pairs *)
      let ppo_loc =
        USet.filter
          (fun (a, b) -> not (USet.mem read_events a && USet.mem read_events b))
          ppo_loc
      in

      (* Compute transitive closure *)
      let ppo_loc = USet.intersection ppo_loc e_squared in
      let ppo_loc = URelation.transitive_closure ppo_loc in

      (* Return the freeze validation function *)
      Lwt.return_some (fun rf ->
          validate_rf structure path ppo_loc dp ppo j_list pp p_combined rf
      )

(** Build justification combinations for all paths with caching *)
let build_justcombos structure paths init_ppo statex
    (justmap : (int, justification list) Hashtbl.t) =
  (* Given a path, combine justifications for each write on the path. *)
  let combine_justifications_for_path path =
    Logs.debug (fun m ->
        m "Building justification combinations for path [%s]"
          (String.concat ", "
             (List.map (Printf.sprintf "%d")
                (List.sort compare (USet.values path.path))
             )
          )
    );

    let path_writes =
      USet.intersection path.path structure.write_events |> USet.values
    in

    let%lwt js_combinations =
      ListMapCombinationBuilder.build_combinations justmap path_writes
        (fun combo ?alternatives just ->
          JustValidation.check_partial_combo structure path combo ?alternatives
            just
        )
        (fun combo -> JustValidation.check_final_combo structure path combo)
    in

    Logs.debug (fun m ->
        m "  Found %d justification combinations" (List.length js_combinations)
    );

    Lwt.return
      (List.map (fun combo -> (path, List.map snd combo)) js_combinations)
  in

  Lwt_stream.of_list paths
  |> Lwt_stream.map_list_s combine_justifications_for_path

(** Generate executions **)

(* Compute initial RF relation: writes × reads that are not in po^-1 *)
let compute_path_rf structure path ~elided ~constraints statex =
  let write_events =
    USet.set_minus (USet.intersection structure.write_events path.path) elided
  in
  let read_events =
    USet.set_minus (USet.intersection structure.read_events path.path) elided
  in
  let w_with_init = USet.union write_events (USet.singleton 0) in
  let w_cross_r = URelation.cross w_with_init read_events in

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
    let* all_rf =
      USet.async_filter
        (fun rf_edge ->
          let w, r = rf_edge in
          let r_restrict =
            Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
          in
            (* Check that loc(w) = loc(r) is satisfiable *)
            let* loc_eq =
              match
                (get_loc structure.events w, get_loc structure.events r)
              with
              | Some loc_w, Some loc_r ->
                  Solver.expoteq ~state:preds loc_w loc_r
              | _ -> Lwt.return false
            in
              let*? () = (loc_eq, "RF locs not equal") in
                (* Check that writes are not shadowed for read-from *)
                let* has_dslwb = dslwb structure w r in
                  let*? () = (not has_dslwb, "RF edge is shadowed (dslwb)") in
                    Lwt.return true
        )
        w_cross_r_minus_po
    in

    Logs.debug (fun m ->
        m "  Found %d initial RF edges for path" (USet.size all_rf)
    );

    let all_rf_inv = URelation.inverse_relation all_rf in
    let all_rf_inv_map = URelation.adjacency_list_map all_rf_inv in
      ListMapCombinationBuilder.build_combinations all_rf_inv_map
        (USet.values read_events)
        (fun _ ?alternatives:_ _ -> Lwt.return true)
        (fun _ -> Lwt.return true)

(** Main execution generation - replaces the stub in calculate_dependencies *)
let generate_executions (structure : symbolic_event_structure)
    (justs : justification uset) statex init_ppo ~include_dependencies
    ~restrictions =
  (* let* _ = Lwt.return_unit in *)
  Logs.info (fun m ->
      m "Generating executions for structure with %d events"
        (USet.size structure.e)
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

  (* Build justification map: write event label -> list of justifications *)
  (* TODO remove justifications with elided origins *)
  let justmap = Hashtbl.create 16 in
    USet.iter
      (fun (just : justification) ->
        let label = just.w.label in
        let existing = try Hashtbl.find justmap label with Not_found -> [] in
          Hashtbl.replace justmap label (just :: existing)
      )
      justs;

    Logs.info (fun m -> m "Built justification map");

    let stream_freeze input_stream =
      let freeze_just_combo (path, just_combo) =
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
        let con = Forwardingcontext.create ~fwd ~we () in
        let j_remapped =
          List.map (fun j -> Forwardingcontext.remap_just con j None) just_combo
        in
        let elided = URelation.pi_2 (USet.union fwd we) in
        let constraints =
          List.flatten (List.map (fun (j : justification) -> j.p) just_combo)
        in

        let* all_rf =
          compute_path_rf structure path ~elided ~constraints statex
        in
        let all_rf = List.map (List.map (fun (r, w) -> (w, r))) all_rf in
        let all_rf = List.map USet.of_list all_rf in

        let* freeze_fn_opt =
          create_freeze structure path j_remapped init_ppo statex
        in
          Logs.debug (fun m ->
              m
                "Freezing justification combination with %d justifications \
                 over path with %d events, exploring %d RF combinations"
                (List.length just_combo) (USet.size path.path)
                (List.length all_rf)
          );
          match freeze_fn_opt with
          | None -> Lwt.return []
          | Some freeze_fn ->
              (* Process each RF combination and collect successful freezes *)
              Lwt_list.filter_map_s
                (fun rf_combo ->
                  let* freeze_res_opt = freeze_fn rf_combo in
                    Lwt.return freeze_res_opt
                )
                all_rf
      in

      (* Use map_list_s to handle the list results and flatten them into the stream *)
      Lwt_stream.map_list_s freeze_just_combo input_stream
    in

    let stream_freeze_to_execution input_stream =
      let freeze_to_execution freeze_res =
        (* Fixed point computation for RF mapping *)
        let fix_rf_map = Hashtbl.create 16 in

        (* Build initial mapping from RF *)
        USet.iter
          (fun (w, r) ->
            let just_w =
              List.find_opt (fun j -> j.w.label = w) freeze_res.justs
            in
            let w_val =
              match just_w with
              | Some j -> vale structure.events j.w.label r
              | None -> vale structure.events w r
            in
              match get_val structure.events r with
              | None ->
                  failwith ("Read event " ^ string_of_int r ^ " has no value!")
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
                      (fun reg expr -> Hashtbl.add final_env reg expr)
                      reg_env
            )
            freeze_res.e;

          (* Create execution *)
          let exec =
            {
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

          Lwt.return exec
      in

      Lwt_stream.map_s freeze_to_execution input_stream
    in

    let stream_filter_coherent_executions input_stream =
      Lwt_stream.filter_s
        (fun exec ->
          check_for_coherence structure exec restrictions include_dependencies
        )
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
    let* executions =
      build_justcombos structure paths init_ppo statex justmap
      |> stream_freeze
      |> dedup_freeze_results
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

      Lwt.return minimal_executions
