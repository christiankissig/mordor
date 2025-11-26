open Lwt.Syntax
open Algorithms
open Coherence
open Events
open Expr
open Trees
open Types
open Uset

(** Utils **)
let to_string (exec : symbolic_execution) : string =
  Printf.sprintf "{\n\tex_e=%s,\n\trf=%s\n\tdp=%s\n\tppo=%s\n}"
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

(** Create disjoint predicate for two (location, value) pairs *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

(* Find the origin of a symbol in a symbolic event structure *)
let origin structure (s : string) = Hashtbl.find_opt structure.origin s

(* Check if write w is downward-closed same-location write before read r. This
   prevents r reading from shadowed writes w.*)
(* TODO optimize *)
let dslwb structure events w r =
  let write_events = structure.write_events in
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
let rec cartesian = function
  | [] -> [ [] ]
  | hd :: tl ->
      List.concat_map (fun x -> List.map (List.cons x) (cartesian tl)) hd

(** Partition neighbours into groups where each group is mutually in conflict *)
let partition_by_conflict neighbours conflict =
  let neighbours_list = USet.values neighbours in

  (* Helper: find all neighbours in the same conflict group as 'seed' *)
  let rec find_conflict_group seed remaining acc =
    match remaining with
    | [] -> (acc, [])
    | n :: rest ->
        (* Check if n conflicts with all members of acc (including seed) *)
        let conflicts_with_all =
          List.for_all
            (fun member ->
              USet.mem conflict (member, n)
              || USet.mem conflict (n, member)
              || member = n
            )
            (seed :: acc)
        in
          if conflicts_with_all then find_conflict_group seed rest (n :: acc)
          else
            let group, remaining' = find_conflict_group seed rest acc in
              (group, n :: remaining')
  in

  (* Partition all neighbours into conflict groups *)
  let rec partition remaining groups =
    match remaining with
    | [] -> groups
    | seed :: rest ->
        let group, remaining' = find_conflict_group seed rest [ seed ] in
          partition remaining' (group :: groups)
  in

  partition neighbours_list []

let gen_paths events (structure : symbolic_event_structure) restrict =
  let po_intransitive = URelation.transitive_reduction structure.po in
  let po_tree = build_tree structure.e po_intransitive in
  (* TODO subsequently assuming that multiple successors are in conflict *)

  (* DFS search for all paths. Each path is a uset event IDs. Search produces list
   of such paths. *)
  let rec dfs current =
    let neighbours =
      Hashtbl.find_opt po_tree current |> Option.value ~default:(USet.create ())
    in
      if USet.size neighbours == 0 then
        (* leaf node *)
        [ USet.singleton current ]
      else if USet.size neighbours == 1 then
        (* one neighbour; continue down that path *)
        let next = USet.values neighbours |> List.hd in
          dfs next |> List.map (fun path -> USet.add path current)
      else if
        USet.subset
          (USet.set_minus
             (URelation.cross neighbours neighbours)
             (URelation.identity_relation neighbours)
          )
          structure.conflict
      then
        (* neighbour branches are in conflict; disjoint union *)
        USet.values neighbours
        |> List.map dfs
        |> List.flatten
        |> List.map (fun path -> USet.add path current)
      else
        (* Multiple neighbours: partition by conflict *)
        let conflict_groups =
          partition_by_conflict neighbours structure.conflict
        in

        Logs.debug (fun m ->
            m "Event %d has %d conflict groups: [%s]" current
              (List.length conflict_groups)
              (String.concat "; "
                 (List.map
                    (fun g -> string_of_int (List.length g))
                    conflict_groups
                 )
              )
        );

        (* For each conflict group, choose one alternative (disjoint union) *)
        (* Across groups, take all combinations (cartesian product) *)
        conflict_groups
        |> List.map (fun group ->
            (* Within this conflict group, just flatten (disjoint union) *)
            List.map dfs group |> List.flatten
        )
        |> cartesian
        |> List.map (fun paths ->
            List.fold_left
              (fun acc path -> USet.union acc path)
              (USet.singleton current) paths
        )
  in

  (* Find root events (events with no predecessors in po) *)
  let roots =
    let all_events = structure.e in
    let has_predecessor = URelation.pi_2 structure.po in
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

let atomicity_pairs structure e_set rhb p =
  (* Compute atomicity pairs AF *)
  let read_events = USet.intersection structure.read_events e_set in
  let malloc_events = USet.intersection structure.malloc_events e_set in
  let a = USet.union read_events malloc_events in
  let a_squared = URelation.cross a a in

  USet.async_filter
    (fun (e_1, e_2) ->
      if e_1 >= e_2 then Lwt.return_false
      else
        (* Check if there's no intermediate event between e_1 and e_2 *)
        let* has_intermediate =
          USet.async_exists
            (fun ep ->
              if not (USet.mem rhb (e_1, ep) && USet.mem rhb (ep, e_2)) then
                Lwt.return_false
              else
                (* Check if loc(e_1) = loc(ep) under env_rf using semeq *)
                let loc_e1 = get_loc structure.events e_1 |> Option.get in
                let loc_ep = get_loc structure.events ep |> Option.get in

                Solver.exeq ~state:p loc_e1 loc_ep
            )
            e_set
        in
          Lwt.return (not has_intermediate)
    )
    a_squared

let validate_rf (structure : symbolic_event_structure) e elided elided_rf
    ppo_loc ppo_loc_tree dp dp_ppo j_list (pp : expr list) p_combined rf =
  let* _ = Lwt.return_unit in

  let po = USet.intersection structure.po (URelation.cross e e) in
  let read_events = USet.intersection structure.read_events e in
  let write_events = USet.intersection structure.write_events e in

  (* Remove elided RF edges *)
  let rf_m = USet.set_minus rf elided_rf in
  let rf_e = USet.union (URelation.pi_1 rf_m) (URelation.pi_2 rf_m) in

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
              | Some j -> vale structure.events j.w.label r
              | None -> vale structure.events w r
            in
            let r_val = get_val structure.events r |> Option.get in
              Expr.binop w_val "=" r_val
        )
      in

      let check_rf =
        USet.values rf
        |> List.map (fun (w, r) ->
            let just_w = List.find_opt (fun j -> j.w.label = w) j_list in
            let w_loc =
              match just_w with
              | Some j -> loce structure.events j.w.label r
              | None -> loce structure.events w r
            in
            let r_loc = get_loc structure.events r |> Option.get in
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
        USet.size
          (USet.intersection (URelation.pi_2 delta) (URelation.pi_1 rf_m))
        = 0
        && USet.equal read_events (URelation.pi_2 rf)
      in

      if not check_1_1 then Lwt.return_none
      else
        (* Check acyclicity of rhb = dp_ppo ∪ rf *)
        let rhb = USet.union dp_ppo rf in
          if not (URelation.acyclic rhb) then Lwt.return_none
          else
            let* has_dslwb =
              USet.async_exists
                (fun (w, r) -> dslwb structure structure.events w r)
                rf
            in

            if has_dslwb then Lwt.return_none
            else
              (* Rewrite predicates *)
              let big_p_exprs = p_combined @ env_rf @ check_rf in
              let big_p =
                List.map (fun e -> Expr.evaluate e (fun _ -> None)) big_p_exprs
              in
                (* atomicity constraint *)
                let* af = atomicity_pairs structure e rhb env_rf in

                (* Create disjointness predicates *)
                (* TODO why ? *)
                let disj =
                  USet.map
                    (fun (a, b) ->
                      let loc_a = get_loc structure.events a |> Option.get in
                      let val_a = get_val structure.events a |> Option.get in
                      let loc_b = get_loc structure.events b |> Option.get in
                      let val_b = get_val structure.events b |> Option.get in
                        (* disjoint only uses location *)
                        disjoint (loc_a, val_a) (loc_b, val_b)
                    )
                    af
                  |> USet.values
                in

                let bigger_p =
                  List.map
                    (fun expr -> Expr.evaluate expr (fun _ -> None))
                    (big_p @ disj)
                in

                (* Filter po to only include events in e *)
                let po_filtered =
                  USet.filter (fun (f, t) -> USet.mem e f && USet.mem e t) po
                in
                let inv_po_tree =
                  build_tree e (URelation.inverse_relation po_filtered)
                in

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

(** Create a freeze function that validates RF sets for a justification
    combination *)
let create_freeze (structure : symbolic_event_structure) path j_list init_ppo
    statex =
  let* _ = Lwt.return_unit in

  let e = path.path in
  let e_squared = URelation.cross e e in
  let pp = path.p in

  let read_events = USet.intersection structure.read_events e in
  let write_events = USet.intersection structure.write_events e in
  let malloc_events = USet.intersection structure.malloc_events e in

  Logs.debug (fun m ->
      m "Creating freeze function for justification combination with %d justs"
        (List.length j_list)
  );

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

  Logs.debug (fun m -> m "  Created dp with %d pairs" (USet.size dp));

  (* Compute combined fwd and we *)
  let f =
    List.fold_left (fun acc j -> USet.union acc j.fwd) (USet.create ()) j_list
  in
  let we =
    List.fold_left (fun acc j -> USet.union acc j.we) (USet.create ()) j_list
  in

  let delta = USet.union f we in
  let elided = URelation.pi_2 delta in

  (* elided_rf: Delta ∩ (W × R) ∩ E² *)
  let w_cross_r = URelation.cross write_events read_events in
  let elided_rf =
    USet.intersection delta w_cross_r |> fun s -> USet.intersection s e_squared
  in

  let _e = USet.set_minus e elided in

  Logs.debug (fun m ->
      m "  Created elided set with %d events and elided_rf with %d pairs"
        (USet.size elided) (USet.size elided_rf)
  );

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

  Logs.debug (fun m ->
      m "  Combined predicates count: %d" (List.length p_combined)
  );

  (* Check if predicates are satisfiable *)
  let* p_combined_sat = Solver.is_sat p_combined in
    if not p_combined_sat then (
      Logs.debug (fun m -> m "  Predicates unsatisfiable");
      Lwt.return_none
    )
    else (
      Logs.debug (fun m -> m "  Predicates satisfiable");
      (* Check that all writes in E are either elided or have justifications *)
      let check_3 =
        USet.for_all
          (fun w ->
            USet.mem elided w || List.exists (fun j -> j.w.label = w) j_list
          )
          write_events
      in

      if not check_3 then Lwt.return_none
      else (
        Logs.debug (fun m ->
            m "  All writes in E are either elided or justified"
        );
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
                  URelation.cross (URelation.pi_1 po_to_w)
                    (URelation.pi_1 po_to_w)
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
            (fun (a, b) ->
              not (USet.mem read_events a && USet.mem read_events b)
            )
            ppo_loc
        in

        (* Compute transitive closure *)
        let ppo_loc = URelation.transitive_closure ppo_loc in
        let ppo_loc = USet.intersection ppo_loc e_squared in
        let ppo_loc_tree = build_tree e ppo_loc in

        Logs.debug (fun m ->
            m "  Computed ppo with %d pairs and ppo_loc with %d pairs"
              (USet.size ppo) (USet.size ppo_loc)
        );

        (* Combine dp and ppo *)
        let dp_ppo = USet.union dp ppo in

        (* Return the freeze validation function *)
        let freeze_fn rf =
          validate_rf
            (structure : symbolic_event_structure)
            e elided elided_rf ppo_loc ppo_loc_tree dp dp_ppo j_list pp
            p_combined rf
        in

        Logs.debug (fun m -> m "  Created freeze function");

        Lwt.return_some freeze_fn
      )
    )

(** Build justification combinations for all paths with caching *)
let build_justcombos structure paths init_ppo statex
    (justmap : (int, justification list) Hashtbl.t) =
  let events = structure.events in
  let read_events = structure.read_events in
  let write_events = structure.write_events in

  (* TODO check that the following constraints make sense, and implement more
     extensive structural checks *)
  let check_partial_combo (path : path_info) (combo : justification list)
      (just : justification) =
    let path_preds = path.p in

    (* origin of all symbols on path. fail if symbol not in origin map *)
    let sym_origins =
      USet.map (fun symbol -> origin structure symbol |> Option.get) just.d
    in
      if not (USet.subset sym_origins path.path) then (
        Logs.debug (fun m ->
            m "Origins %s of symbols %s not on path [%s]"
              (String.concat ", "
                 (List.map (Printf.sprintf "%d")
                    (USet.values (USet.set_minus sym_origins path.path))
                 )
              )
              (String.concat ", "
                 (List.map (Printf.sprintf "%s") (USet.values just.d))
              )
              (String.concat ", "
                 (List.map (Printf.sprintf "%d") (USet.values path.path))
              )
        );
        Lwt.return false
      )
      else
        (* delta events must be on path *)
        let just_delta = USet.union just.fwd just.we in
        let just_delta_events =
          USet.union (URelation.pi_1 just_delta) (URelation.pi_2 just_delta)
        in
          if not (USet.subset just_delta_events path.path) then
            ( Logs.debug (fun m ->
                  m
                    "Delta events %s of justification for write %d not on path \
                     [%s]"
                    (String.concat ", "
                       (List.map (Printf.sprintf "%d")
                          (USet.values
                             (USet.set_minus just_delta_events path.path)
                          )
                       )
                    )
                    just.w.label
                    (String.concat ", "
                       (List.map (Printf.sprintf "%d") (USet.values path.path))
                    )
              );
              Lwt.return
            )
              false
          else
            let fwdwe =
              List.fold_left
                (fun acc j -> USet.union acc (USet.union j.fwd j.we))
                (USet.create ()) combo
            in

            (* TODO This used to check that just_delta and fwdwe do no overlap
             in domain and range. This seems incorrect. Instead we check that
             adding just maintains delta as a function, i.e. jointly fwd and we
             map events unambiguously. *)
            let structurally_compatible =
              USet.exists
                (fun (f, t) ->
                  USet.exists (fun (f', t') -> f = f' && t <> t') fwdwe
                )
                just_delta
            in

            if not structurally_compatible then
              ( Logs.debug (fun m ->
                    m
                      "Justification for write %d not structurally compatible \
                       with current combination on path [%s]"
                      just.w.label
                      (String.concat ", "
                         (List.map (Printf.sprintf "%d") (USet.values path.path))
                      )
                );
                Lwt.return
              )
                false
            else
              List.map (fun (just : justification) -> just.p) combo
              |> List.flatten
              |> List.append path_preds
              |> USet.of_list
              |> USet.values
              |> Solver.is_sat
  in
  let check_final_combo _ _ = Lwt.return true in

  let* justcombos_list =
    Lwt_list.map_s
      (fun path ->
        Logs.debug (fun m ->
            m "Building justification combinations for path [%s]"
              (String.concat ", "
                 (List.map (Printf.sprintf "%d")
                    (List.sort compare (USet.values path.path))
                 )
              )
        );

        let path_writes =
          USet.intersection path.path write_events |> USet.values
        in

        let* js_combinations =
          ListMapCombinationBuilder.build_combinations justmap path_writes
            (fun combo just -> check_partial_combo path combo just)
            (fun combo -> check_final_combo path.p combo)
        in

        Logs.debug (fun m ->
            m "  Found %d justification combinations"
              (List.length js_combinations)
        );

        (* For each combination, create freeze functions *)
        let* freeze_fns =
          Lwt_list.map_s
            (fun j_list ->
              let fwd =
                List.fold_left
                  (fun acc j -> USet.union acc j.fwd)
                  (USet.create ()) j_list
              in

              (* TODO this shouldn't be possible, because fwd should be
                 po-before w and thus on path *)
              if
                USet.union (URelation.pi_1 fwd) (URelation.pi_2 fwd)
                |> USet.exists (fun e -> not (USet.mem path.path e))
              then (
                Logs.debug (fun m ->
                    m
                      "  Skipping justification combination with out-of-path \
                       fwd"
                );
                Lwt.return_none
              )
              else
                let we =
                  List.fold_left
                    (fun acc j -> USet.union acc j.we)
                    (USet.create ()) j_list
                in

                if
                  USet.union (URelation.pi_1 we) (URelation.pi_2 we)
                  |> USet.exists (fun e -> not (USet.mem path.path e))
                then (
                  Logs.debug (fun m ->
                      m
                        "  Skipping justification combination with out-of-path \
                         we"
                  );
                  Lwt.return_none
                )
                else
                  let con = Forwardingcontext.create ~fwd ~we () in
                  let j_remapped =
                    List.map
                      (fun j -> Forwardingcontext.remap_just con j None)
                      j_list
                  in

                  let* freeze_opt =
                    create_freeze structure path j_remapped init_ppo statex
                  in
                    Lwt.return freeze_opt
            )
            js_combinations
        in

        let freeze_fns_filtered = List.filter_map Fun.id freeze_fns in
          Logs.debug (fun m ->
              m "  Created %d freeze functions for this path"
                (List.length freeze_fns_filtered)
          );
          Lwt.return (path.path, freeze_fns_filtered)
      )
      paths
  in

  let justcombos = Hashtbl.create 16 in
    List.iter
      (fun (path_uset, freezes) -> Hashtbl.add justcombos path_uset freezes)
      justcombos_list;

    Lwt.return justcombos

(** Generate executions **)

(** Main execution generation - replaces the stub in calculate_dependencies *)
let generate_executions (structure : symbolic_event_structure)
    (justs : justification uset) statex init_ppo ~include_dependencies
    ~restrictions =
  let* _ = Lwt.return_unit in

  let events = structure.events in
  let restrict = structure.restrict in

  Logs.debug (fun m ->
      m "Generating executions for structure with %d events"
        (USet.size structure.e)
  );

  let e_set = structure.e in
  let read_events = structure.read_events in
  let write_events = structure.write_events in
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
      m "Generated %d paths through the control flow" (List.length paths)
  );

  (* Compute initial RF relation: writes × reads that are not in po^-1 and not dslwb *)
  let inv_po = URelation.inverse_relation po in
  let w_with_init = USet.union write_events (USet.singleton 0) in
  let w_cross_r = URelation.cross w_with_init read_events in
  let w_cross_r_minus_inv_po = USet.set_minus w_cross_r inv_po in

  let* all_rf =
    USet.async_filter
      (fun (w, r) ->
        let r_restrict =
          Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
        in
        let w_restrict =
          Hashtbl.find_opt structure.restrict w |> Option.value ~default:[]
        in
          let* w_r_comp = Solver.is_sat (r_restrict @ w_restrict) in
            if w_r_comp then
              match (get_loc events w, get_loc events r) with
              | Some loc_w, Some loc_r ->
                  (* TODO use semantic equivalence relative to valres *)
                  let* loc_eq = Solver.expoteq ~state:r_restrict loc_w loc_r in
                    if loc_eq then dslwb structure events w r
                    else Lwt.return false
              | _ -> Lwt.return false
            else Lwt.return false
      )
      w_cross_r_minus_inv_po
  in

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
      build_justcombos structure paths init_ppo statex justmap
    in

    Logs.debug (fun m -> m "Built justification combinations for all paths");

    (* Enumerate RF sets - simplified version *)
    (* In full version, this would use a more sophisticated RF enumeration *)
    let* all_executions =
      (* For each path, try to build executions *)
      Lwt_list.map_s
        (fun path ->
          (* Get freeze functions for this path *)
          let freeze_fns =
            Hashtbl.find_opt justcombos path.path |> Option.value ~default:[]
          in

          (* Try each freeze function with the RF relation *)
          let* path_execs =
            Lwt_list.filter_map_s
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

    (* Convert freeze_results to executions *)
    let* final_executions =
      List.concat all_executions
      |> Lwt_list.map_s (fun (freeze_res : freeze_result) ->
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
              let r_val = get_val structure.events r |> Option.get in

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
