open Lwt.Syntax
open Coherence
open Events
open Expr
open Trees
open Types
open Utils
open Uset

(** Utils **)

let to_string (exec : symbolic_execution) : string =
  Printf.sprintf "{\nex_e=%s,\nrf=%s\ndp=%s\nppo=%s\n}"
    (String.concat ", " (List.map (Printf.sprintf "%d") (USet.values exec.ex_e)))
    (String.concat ", "
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values exec.rf)
       )
    )
    (String.concat ", "
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values exec.dp)
       )
    )
    (String.concat ", "
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values exec.ppo)
       )
    )

(* TODO values are not tested *)

(** Create disjoint predicate for two (location, value) pairs *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

let origin (events : (int, event) Hashtbl.t) (e_set : int uset) (s : string) =
  let read_events = filter_events events e_set Read () in
  let malloc_events = filter_events events e_set Malloc () in

  (* Try to find in reads *)
  let in_reads =
    USet.filter
      (fun x ->
        match get_val events x with
        | Some (ESymbol sym) -> sym = s
        | _ -> false
      )
      read_events
  in
  let in_reads_vals = USet.values in_reads in
    match in_reads_vals with
    | e :: _ -> Some e
    | [] -> (
        (* Try to find in mallocs by symbol *)
        let in_mallocs =
          USet.filter
            (fun x ->
              try
                let event = Hashtbl.find events x in
                  match event.rval with
                  (* Changed from event.id *)
                  | Some (VSymbol sym) -> sym = s
                  | _ -> false
              with Not_found -> false
            )
            malloc_events
        in
        let in_mallocs_vals = USet.values in_mallocs in
          match in_mallocs_vals with
          | e :: _ -> Some e
          | [] -> None
      )

(* Check if write w is downward-closed same-location write before read r. This
   prevents r reading from shadowed writes w.*)
(* TODO optimize *)
let dslwb structure events w r =
  let write_events = filter_events events structure.e Write () in
  let r_restrict =
    Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
  in
    USet.async_exists
      (fun (w2, r2) ->
        if
          r2 = r (* w2 po bfore r *)
          && w2 <> w (* w2 is not w *)
          && USet.mem write_events w2 (* w2 is a write *)
          && USet.mem structure.po (w, w2)
          (* w2 po after w, thus in between w and r *)
        then
          (* w2 potentially shadows w *)
          (* TODO use semantic equivalence relative to valres *)
          match (get_loc events w, get_loc events w2) with
          | Some loc, Some loc2 -> Solver.exeq ~state:r_restrict loc loc2
          | _ -> Lwt.return false
        else Lwt.return false
      )
      structure.po

(** Generate Paths **)

(** Path type *)
type path_info = {
  path : int uset;
  p : expr list; (* List of predicate lists, serves as conjunction *)
}

(** Generate all paths through the control flow structure *)
let gen_paths events (structure : symbolic_event_structure) restrict =
  let po_intransitive = URelation.transitive_reduction structure.po in
  let po_tree = build_tree structure.e po_intransitive in
  (* subsequently assuming that multiple successors are in conflict *)

  (* DFS search for all paths. Each path is a uset event IDs. Search produces list
   of such paths. *)
  let rec dfs current =
    let neighbours =
      Hashtbl.find_opt po_tree current |> Option.value ~default:(USet.create ())
    in
      if USet.size neighbours == 0 then [ USet.singleton current ]
      else
        USet.values neighbours
        |> List.map dfs
        |> List.flatten
        |> List.map (fun path -> USet.add path current)
  in

  (* Find root events (events with no predecessors in po) *)
  let roots =
    let all_events = structure.e in
    let has_predecessor = pi_2 structure.po in
      USet.set_minus all_events has_predecessor
  in

  Logs.debug (fun m ->
      m "Generating paths from roots: %s"
        (String.concat ", " (USet.values (USet.map (Printf.sprintf "%d") roots)))
  );

  (* Generate p from value restrictions along path and compose path_info. TODO
     need to filter paths by satisfiability? *)
  let paths = USet.values roots |> List.map dfs |> List.flatten in
    List.map
      (fun path ->
        let p =
          USet.values path
          |> List.map (fun e ->
              Hashtbl.find_opt restrict e |> Option.value ~default:[]
          )
          |> List.flatten
          |> USet.of_list
          |> USet.values
        in
          { path; p }
      )
      paths

(** Freezing **)

(** Choose compatible justifications for a path *)
let choose justmap path_events =
  let path_list = USet.values path_events in

  let rec choose_rec list i items fwdwe =
    if i = 0 then [ items ]
    else
      let i = i - 1 in

      (* Skip if already covered by fwdwe *)
      if List.length items > 0 && USet.mem (pi_2 fwdwe) list.(i) then
        choose_rec list i items fwdwe
      else
        (* Get justifications for this event *)
        let justs_for_event =
          try Hashtbl.find justmap list.(i) with Not_found -> []
        in

        (* Filter compatible justifications *)
        let compatible =
          List.filter
            (fun just ->
              let x = USet.union just.fwd just.we in
              (* Check no conflicts with existing fwdwe *)
              let pi1_x = pi_1 x in
              let pi2_x = pi_2 x in
              let pi1_fwdwe = pi_1 fwdwe in
              let pi2_fwdwe = pi_2 fwdwe in

              USet.size (USet.intersection pi1_x pi2_fwdwe) = 0
              && USet.size (USet.intersection pi2_x pi1_fwdwe) = 0
            )
            justs_for_event
        in

        (* Recursively choose for each compatible justification *)
        List.concat_map
          (fun just ->
            let new_fwdwe = USet.union fwdwe (USet.union just.fwd just.we) in
              choose_rec list i (items @ [ just ]) new_fwdwe
          )
          compatible
  in

  choose_rec (Array.of_list path_list) (List.length path_list) []
    (USet.create ())

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

let rec validate_rf events (structure : symbolic_event_structure) e elided
    elided_rf ppo_loc ppo_loc_tree dp dp_ppo j_list (pp : expr list) p_combined
    rf write_events read_events po =
  let* _ = Lwt.return_unit in

  (* Filter po to only include events in e *)
  let po_filtered =
    USet.filter (fun (f, t) -> USet.mem e f && USet.mem e t) po
  in

  (* Remove elided RF edges *)
  let rf_m = USet.set_minus rf elided_rf in
  let rf_e = USet.union (pi_1 rf_m) (pi_2 rf_m) in

  (* Check 1: elided_rf must be subset of rf *)
  if not (USet.subset elided_rf rf) then Lwt.return_none
    (* Check 2: rf_e should not overlap with elided *)
  else if USet.exists (fun e -> USet.mem elided e) rf_e then Lwt.return_none
  else
    (* Check 3: All rf edges respect ppo_loc *)
    let rf_respects_ppo =
      USet.for_all
        (fun (w, r) ->
          if USet.mem ppo_loc (w, r) then
            (* If (w,r) in ppo_loc, check that r is reachable from w *)
            let reachable =
              try
                let successors = Hashtbl.find ppo_loc_tree w in
                  USet.mem successors r
              with Not_found -> false
            in
              reachable
          else true
        )
        rf_m
    in

    if not rf_respects_ppo then Lwt.return_none
    else
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
              | Some j -> vale events j.w.label r
              | None -> vale events w r
            in
            let r_val =
              match get_val events r with
              | Some v -> v
              | None -> EVar "?"
            in
              Expr.binop w_val "=" r_val
        )
      in

      let check_rf =
        USet.values rf
        |> List.map (fun (w, r) ->
            let just_w = List.find_opt (fun j -> j.w.label = w) j_list in
            let w_loc =
              match just_w with
              | Some j -> loce events j.w.label r
              | None -> loce events w r
            in
            let r_loc =
              match get_loc events r with
              | Some l -> l
              | None -> EVar "?"
            in
              Expr.binop w_loc "=" r_loc
        )
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
      let check_1_1 =
        USet.size (USet.intersection (pi_2 delta) (pi_1 rf_m)) = 0
        && USet.equal (USet.intersection e read_events) (pi_2 rf)
      in

      if not check_1_1 then Lwt.return_none
      else
        (* Check acyclicity of rhb = dp_ppo ∪ rf *)
        let rhb = USet.union dp_ppo rf in
          if not (URelation.acyclic rhb) then Lwt.return_none
          else
            (* Rewrite predicates *)
            let big_p_exprs = p_combined @ env_rf @ check_rf in
              let* big_p_opt = Rewrite.rewrite_pred big_p_exprs in

              match big_p_opt with
              | None -> Lwt.return_none
              | Some big_p -> (
                  (* Compute atomicity pairs AF *)
                  let malloc_events = USet.create () in
                  (* TODO: get from structure *)
                  let a = USet.union read_events malloc_events in
                  let a_squared = URelation.cross a a in

                  let* af =
                    USet.async_filter
                      (fun (e_1, e_2) ->
                        if e_1 >= e_2 then Lwt.return_false
                        else
                          (* Check if there's no intermediate event between e_1 and e_2 *)
                          let* has_intermediate =
                            USet.async_exists
                              (fun ep ->
                                if
                                  not
                                    (USet.mem rhb (e_1, ep)
                                    && USet.mem rhb (ep, e_2)
                                    )
                                then Lwt.return_false
                                else
                                  (* Check if loc(e_1) = loc(ep) under env_rf using semeq *)
                                  let loc_e1 =
                                    match get_loc events e_1 with
                                    | Some l -> l
                                    | None -> EVar "?"
                                  in
                                  let loc_ep =
                                    match get_loc events ep with
                                    | Some l -> l
                                    | None -> EVar "?"
                                  in

                                  Solver.exeq ~state:env_rf loc_e1 loc_ep
                              )
                              e
                          in
                            Lwt.return (not has_intermediate)
                      )
                      a_squared
                  in

                  (* Create disjointness predicates *)
                  let disj =
                    USet.values af
                    |> List.map (fun (a, b) ->
                        let loc_a =
                          match get_loc events a with
                          | Some l -> l
                          | None -> EVar "?"
                        in
                        let val_a =
                          match get_val events a with
                          | Some v -> v
                          | None -> EVar "?"
                        in
                        let loc_b =
                          match get_loc events b with
                          | Some l -> l
                          | None -> EVar "?"
                        in
                        let val_b =
                          match get_val events b with
                          | Some v -> v
                          | None -> EVar "?"
                        in
                          disjoint (loc_a, val_a) (loc_b, val_b)
                    )
                  in

                  let* bigger_p_opt = Rewrite.rewrite_pred (big_p @ disj) in

                  match bigger_p_opt with
                  | None -> Lwt.return_none
                  | Some bigger_p ->
                      (* Check dslwb (downward-closed same-location write before) *)
                      (* Filter po to only include events in e *)
                      let po_filtered =
                        USet.filter
                          (fun (f, t) -> USet.mem e f && USet.mem e t)
                          po
                      in
                      let inv_po_tree =
                        build_tree e (URelation.inverse_relation po_filtered)
                      in

                      let* has_dslwb =
                        USet.async_exists
                          (fun (w, r) -> dslwb structure events w r)
                          rf
                      in

                      if has_dslwb then Lwt.return_none
                      else
                        (* Success! Return the freeze result *)
                        Lwt.return_some
                          {
                            justs = j_list;
                            e;
                            dp;
                            ppo = dp_ppo;
                            rf;
                            rmw = rmw_filtered;
                            pp;
                            conds = bigger_p;
                          }
                )

(** Create a freeze function that validates RF sets for a justification
    combination *)
and create_freeze events (structure : symbolic_event_structure) path j_list
    write_events read_events init_ppo statex =
  let* _ = Lwt.return_unit in

  let e = path.path in
  let e_squared = URelation.cross e e in
  let pp = path.p in

  (* Compute dependency relation *)
  let dp_pairs =
    List.concat_map
      (fun just ->
        let syms = USet.values just.d in
          List.concat_map
            (fun sym ->
              let malloc_events = USet.create () in
                (* TODO *)
                match origin events structure.e sym with
                | Some orig -> [ (orig, just.w.label) ]
                | None -> []
            )
            syms
      )
      j_list
  in
  let dp = USet.of_list dp_pairs in

  (* Compute combined fwd and we *)
  let f =
    List.fold_left (fun acc j -> USet.union acc j.fwd) (USet.create ()) j_list
  in
  let we =
    List.fold_left (fun acc j -> USet.union acc j.we) (USet.create ()) j_list
  in

  let delta = USet.union f we in
  let elided = pi_2 delta in

  (* elided_rf: Delta ∩ (W × R) ∩ E² *)
  let w_cross_r = URelation.cross write_events read_events in
  let elided_rf =
    USet.intersection delta w_cross_r |> fun s -> USet.intersection s e_squared
  in

  let _e = USet.set_minus e elided in

  (* Create forwarding context *)
  let con = Forwardingcontext.create ~fwd:f ~we () in

  (* Combine predicates *)
  let p_combined =
    List.concat_map (fun (j : justification) -> j.p) j_list
    @ con.psi
    @ pp
    @ statex
  in

  (* Check if predicates are satisfiable *)
  let solver = Solver.create p_combined in
    let* sat = Solver.check solver in
      match sat with
      | Some false -> Lwt.return_none
      | _ ->
          (* Check that all writes in E are either elided or have justifications *)
          let e_writes = USet.intersection e write_events in
          let check_3 =
            USet.for_all
              (fun w ->
                USet.mem elided w || List.exists (fun j -> j.w.label = w) j_list
              )
              e_writes
          in

          if not check_3 then Lwt.return_none
          else
            (* Compute PPO for each justification *)
            let* ppos =
              Lwt_list.map_p
                (fun just ->
                  let just_con =
                    Forwardingcontext.create ~fwd:just.fwd ~we:just.we ()
                  in
                    let* ppo_j = Forwardingcontext.ppo just_con just.p in

                    (* Intersect with po pairs ending at this write *)
                    let po_to_w =
                      USet.filter (fun (_, t) -> t = just.w.label) structure.po
                    in
                    let po_to_w_squared =
                      URelation.cross (pi_1 po_to_w) (pi_1 po_to_w)
                    in
                      Lwt.return (USet.intersection ppo_j po_to_w_squared)
                )
                j_list
            in

            let ppo = List.fold_left USet.union (USet.create ()) ppos in
            let ppo = USet.union ppo (Forwardingcontext.ppo_sync con) in

            (* Compute ppo_loc *)
            let* ppo_loc_base = Forwardingcontext.ppo_loc con p_combined in
            let ppo_loc = USet.union ppo_loc_base init_ppo in

            (* Filter out read-read pairs *)
            let ppo_loc =
              USet.filter
                (fun (a, b) ->
                  not (USet.mem read_events a && USet.mem read_events b)
                )
                ppo_loc
            in

            (* Compute transitive closure *)
            let ppo_loc = URelation.transitive_closure ppo_loc in
            let ppo_loc_tree = build_tree e ppo_loc in

            let dp_ppo = USet.union dp ppo in

            (* Return the freeze validation function *)
            let freeze_fn rf =
              validate_rf events
                (structure : symbolic_event_structure)
                e elided elided_rf ppo_loc ppo_loc_tree dp dp_ppo j_list pp
                p_combined rf write_events read_events structure.po
            in

            Lwt.return_some freeze_fn

(** Build justification combinations for all paths *)
and build_justcombos events structure paths write_events read_events init_ppo
    statex justmap =
  let* justcombos_list =
    Lwt_list.map_p
      (fun path ->
        (* Filter path to only write events *)
        let path_writes =
          USet.filter (fun e -> USet.mem write_events e) path.path
        in

        (* Get compatible justification combinations *)
        let js_combinations = choose justmap path_writes in

        (* For each combination, create remapped justifications *)
        let* freeze_fns =
          Lwt_list.map_p
            (fun j_list ->
              (* Compute combined fwd and we *)
              let fwd =
                List.fold_left
                  (fun acc j -> USet.union acc j.fwd)
                  (USet.create ()) j_list
              in
              let we =
                List.fold_left
                  (fun acc j -> USet.union acc j.we)
                  (USet.create ()) j_list
              in

              (* Create forwarding context *)
              let con = Forwardingcontext.create ~fwd ~we () in

              (* Remap all justifications *)
              let j_remapped =
                List.map
                  (fun j -> Forwardingcontext.remap_just con j None)
                  j_list
              in

              (* Create freeze function for this J *)
              let* freeze_opt =
                create_freeze events structure path j_remapped write_events
                  read_events init_ppo statex
              in
                Lwt.return freeze_opt
            )
            js_combinations
        in

        let freeze_fns_filtered = List.filter_map Fun.id freeze_fns in
          Lwt.return (path.path, freeze_fns_filtered)
      )
      paths
  in

  (* Convert to hashtable *)
  let justcombos = Hashtbl.create 16 in
    List.iter
      (fun (path_uset, freezes) -> Hashtbl.add justcombos path_uset freezes)
      justcombos_list;

    Lwt.return justcombos

(** Generate executions **)

(** Main execution generation - replaces the stub in calculate_dependencies *)
let generate_executions (events : (int, event) Hashtbl.t)
    (structure : symbolic_event_structure) (justs : justification uset) statex
    init_ppo ~include_dependencies ~restrictions =
  let* _ = Lwt.return_unit in

  Logs.debug (fun m ->
      m "Generating executions for structure with %d events"
        (Hashtbl.length events)
  );

  let e_set = structure.e in
  let read_events = filter_events events e_set Read () in
  let write_events = filter_events events e_set Write () in
  let po = structure.po in

  (* Build adjacency relations *)
  let po_intransitive = URelation.transitive_reduction po in
  let po_tree = build_tree structure.e po_intransitive in
  let inv_po_tree =
    build_tree structure.e (URelation.inverse_relation po_intransitive)
  in

  (* Generate all paths through the control flow *)
  let paths = gen_paths events structure structure.restrict in

  Logs.debug (fun m ->
      m "Generated %d paths through the control flow\n%s" (List.length paths)
        (String.concat "\n"
           (List.map
              (fun p ->
                Printf.sprintf "Path: [%s] - P = [%s]"
                  (String.concat ", "
                     (List.map string_of_int
                        (List.sort compare (USet.values p.path))
                     )
                  )
                  (String.concat ", " (List.map Expr.to_string p.p))
              )
              paths
           )
        )
  );

  (* Compute initial RF relation: writes × reads that are not in po^-1 and not dslwb *)
  let inv_po = URelation.inverse_relation po in
  let w_with_init = USet.union write_events (USet.singleton 0) in
  let w_cross_r = URelation.cross w_with_init read_events in
  (* remove pairs where write po after read *)
  (* TODO differs from JS which had w_cross_r_minus_inv_po *)
  let w_cross_r_and_po = USet.intersection w_cross_r po in

  let* _rf_pairs =
    USet.async_filter
      (fun (w, r) ->
        let r_restrict =
          Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
        in
          match (get_loc events w, get_loc events r) with
          | Some loc_w, Some loc_r ->
              (* TODO use semantic equivalence relative to valres *)
              let* loc_eq = Solver.expoteq ~state:r_restrict loc_w loc_r in
                if loc_eq then dslwb structure events w r else Lwt.return false
          | _ -> Lwt.return false
      )
      w_cross_r_and_po
  in

  let all_rf = _rf_pairs in

  Logs.debug (fun m -> m "Initial RF pairs (%d)" (USet.size all_rf));

  (* Build justification map: write label -> list of justifications *)
  let justmap = Hashtbl.create 16 in
    USet.iter
      (fun (just : justification) ->
        let label = just.w.label in
        let existing = try Hashtbl.find justmap label with Not_found -> [] in
          Hashtbl.replace justmap label (just :: existing)
      )
      justs;

    Logs.debug (fun m -> m "Built justification map");

    (* Build justcombos for all paths *)
    let* justcombos =
      build_justcombos events structure paths write_events read_events init_ppo
        statex justmap
    in

    Logs.debug (fun m -> m "Built justification combinations for all paths");

    (* Enumerate over all RF sets and generate executions *)
    let paths_with_uset = paths in

    (* Filter function for RF enumeration *)
    let rf_filter = USet.intersection (URelation.cross e_set e_set) po in

    (* Enumerate RF sets - simplified version *)
    (* In full version, this would use a more sophisticated RF enumeration *)
    let* all_executions =
      (* For each path, try to build executions *)
      Lwt_list.map_p
        (fun path ->
          (* Get freeze functions for this path *)
          let freeze_fns =
            try Hashtbl.find justcombos path.path with Not_found -> []
          in

          (* Try each freeze function with the RF relation *)
          let* path_execs =
            Lwt_list.filter_map_p
              (fun freeze_fn ->
                (* Try to validate with all_rf *)
                freeze_fn all_rf
              )
              freeze_fns
          in

          Lwt.return path_execs
        )
        paths
    in

    Logs.debug (fun m -> m "Generated all executions from paths");

    let flat_execs = List.concat all_executions in

    (* Convert freeze_results to executions *)
    let* final_executions =
      Lwt_list.map_p
        (fun (freeze_res : freeze_result) ->
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
                | Some j -> vale events j.w.label r
                | None -> vale events w r
              in
              let r_val =
                match get_val events r with
                | Some v -> v
                | None -> EVar "?"
              in

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

          (* Create execution *)
          let exec =
            {
              ex_e = freeze_res.e;
              rf = freeze_res.rf;
              dp = freeze_res.dp;
              ppo = freeze_res.ppo;
              ex_rmw = freeze_res.rmw;
              ex_p = freeze_res.pp;
              conds = freeze_res.conds;
              fix_rf_map = final_map;
              justs = freeze_res.justs;
              pointer_map = None;
            }
          in

          Lwt.return exec
        )
        flat_execs
    in

    Logs.debug (fun m ->
        m "Generated %d executions before coherence filtering\n\n%s"
          (List.length final_executions)
          (String.concat "\n\n" (List.map to_string final_executions))
    );

    (* Filter through coherence checking *)
    let* coherent_execs =
      Lwt_list.filter_p
        (fun exec ->
          check_for_coherence structure events exec restrictions
            include_dependencies
        )
        final_executions
    in
      Lwt.return coherent_execs
