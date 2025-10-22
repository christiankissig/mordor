open Lwt.Syntax
open Coherence
open Events
open Expr
open Trees
open Types
open Utils

(** Utils **)

(** Create disjoint predicate for two (location, value) pairs *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

(** Find origin event of a symbol *)
let origin events read_events malloc_events s =
  (* Try to find in reads *)
  let in_reads =
    Uset.filter
      (fun x ->
        match val_ events x with
        | Some (VSymbol sym) -> sym = s
        | _ -> false
      )
      read_events
  in
  let in_reads_vals = Uset.values in_reads in
    match in_reads_vals with
    | e :: _ -> Some e
    | [] -> (
        (* Try to find in mallocs by symbol *)
        let in_mallocs =
          Uset.filter
            (fun x ->
              try
                let event = Hashtbl.find events x in
                  match event.id with
                  | Some (VSymbol sym) -> sym = s
                  | _ -> false
              with Not_found -> false
            )
            malloc_events
        in
        let in_mallocs_vals = Uset.values in_mallocs in
          match in_mallocs_vals with
          | e :: _ -> Some e
          | [] -> None
      )

(** Generate Paths **)

(** Path type *)
type path_info = {
  path : int list;
  p : expr list list; (* List of predicate lists *)
}

(** Generate all paths through the control flow structure *)
let gen_paths events (structure : symbolic_event_structure) restrict =
  let po_tree = build_tree structure.e structure.po in

  (* Find root events (events with no predecessors in po) *)
  let find_roots () =
    let all_events = structure.e in
    let has_predecessor = pi_2 structure.po in
    let roots = Uset.set_minus all_events has_predecessor in
    let root_list = Uset.values roots in
      match root_list with
      | [] -> (
          if
            (* If no roots found, try to find event 0 or use first event *)
            Hashtbl.mem events 0
          then [ 0 ]
          else
            let first_events = Uset.values structure.e in
              match first_events with
              | [] -> failwith "No events in structure"
              | hd :: _ -> [ hd ]
        )
      | roots -> roots
  in

  let rec gen_paths_rec e =
    (* Check if event exists before accessing *)
    if not (Hashtbl.mem events e) then [ { path = []; p = [] } ]
    else
      let next_uset =
        try Hashtbl.find po_tree e with Not_found -> Uset.create ()
      in
      let next = Uset.values next_uset in

      if List.length next = 0 then [ { path = [ e ]; p = [] } ]
      else
        (* Check if event is a branch *)
        let event = Hashtbl.find events e in
          if event.typ = Branch then (
            (* Branch event - create two paths *)
            if List.length next <> 2 then
              failwith "Branch event must have exactly 2 successors";

            let next0 = List.nth next 0 in
            let next1 = List.nth next 1 in

            let restrict_e =
              try Hashtbl.find restrict e with Not_found -> []
            in

            let cond =
              match event.cond with
              | Some (VExpression c) -> c
              | Some c -> EVar (Value.to_string c)
              | None -> failwith "Branch missing condition"
            in

            (* Left branch paths *)
            let n0_paths =
              if Uset.mem structure.e next0 then
                let restrict_next0 =
                  try Hashtbl.find restrict next0 with Not_found -> []
                in
                  List.map
                    (fun p ->
                      { path = p.path @ [ e ]; p = p.p @ [ restrict_next0 ] }
                    )
                    (gen_paths_rec next0)
              else [ { path = [ e ]; p = [ restrict_e @ [ cond ] ] } ]
            in

            (* Right branch paths *)
            let n1_paths =
              if Uset.mem structure.e next1 then
                let restrict_next1 =
                  try Hashtbl.find restrict next1 with Not_found -> []
                in
                  List.map
                    (fun p ->
                      { path = p.path @ [ e ]; p = p.p @ [ restrict_next1 ] }
                    )
                    (gen_paths_rec next1)
              else
                [ { path = [ e ]; p = [ restrict_e @ [ Expr.inverse cond ] ] } ]
            in

            n0_paths @ n1_paths
          )
          else
            (* Non-branch event - combine paths from successors *)
            let successor_paths = List.map gen_paths_rec next in

            (* Cartesian product and concatenation *)
            let rec combine_paths paths =
              match paths with
              | [] -> [ { path = []; p = [] } ]
              | p :: rest ->
                  let rest_combined = combine_paths rest in
                    List.concat_map
                      (fun path1 ->
                        List.map
                          (fun path2 ->
                            {
                              path =
                                List.filter (( <> ) e) path1.path @ path2.path;
                              p = path1.p @ path2.p;
                            }
                          )
                          rest_combined
                      )
                      p
            in

            let combined = combine_paths successor_paths in
              List.map (fun p -> { path = p.path @ [ e ]; p = p.p }) combined
  in

  (* Generate paths from each root and combine *)
  let roots = find_roots () in
    List.concat_map gen_paths_rec roots

(** Freezing **)

(** Choose compatible justifications for a path *)
let choose justmap path_events =
  let path_list = Uset.values path_events in

  let rec choose_rec list i items fwdwe =
    if i = 0 then [ items ]
    else
      let i = i - 1 in

      (* Skip if already covered by fwdwe *)
      if List.length items > 0 && Uset.mem (pi_2 fwdwe) list.(i) then
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
              let x = Uset.union just.fwd just.we in
              (* Check no conflicts with existing fwdwe *)
              let pi1_x = pi_1 x in
              let pi2_x = pi_2 x in
              let pi1_fwdwe = pi_1 fwdwe in
              let pi2_fwdwe = pi_2 fwdwe in

              Uset.size (Uset.intersection pi1_x pi2_fwdwe) = 0
              && Uset.size (Uset.intersection pi2_x pi1_fwdwe) = 0
            )
            justs_for_event
        in

        (* Recursively choose for each compatible justification *)
        List.concat_map
          (fun just ->
            let new_fwdwe = Uset.union fwdwe (Uset.union just.fwd just.we) in
              choose_rec list i (items @ [ just ]) new_fwdwe
          )
          compatible
  in

  choose_rec (Array.of_list path_list) (List.length path_list) []
    (Uset.create ())

(** Type for a freeze function - validates an RF set for a justification
    combination *)
type freeze_result = {
  justs : justification list;
  e : int uset;
  dp : (int * int) uset;
  ppo : (int * int) uset;
  rf : (int * int) uset;
  rmw : (int * int) uset;
  pp : expr list list;
  conds : expr list;
}

let rec validate_rf events (structure : symbolic_event_structure) e elided
    elided_rf ppo_loc ppo_loc_tree dp dp_ppo j_list pp p_combined rf
    write_events read_events po =
  let* _ = Lwt.return_unit in

  (* Filter po to only include events in e *)
  let po_filtered =
    Uset.filter (fun (f, t) -> Uset.mem e f && Uset.mem e t) po
  in

  (* Remove elided RF edges *)
  let rf_m = Uset.set_minus rf elided_rf in
  let rf_e = Uset.union (pi_1 rf_m) (pi_2 rf_m) in

  (* Check 1: elided_rf must be subset of rf *)
  if not (Uset.subset elided_rf rf) then Lwt.return_none
    (* Check 2: rf_e should not overlap with elided *)
  else if Uset.exists (fun e -> Uset.mem elided e) rf_e then Lwt.return_none
  else
    (* Check 3: All rf edges respect ppo_loc *)
    let rf_respects_ppo =
      Uset.for_all
        (fun (w, r) ->
          if Uset.mem ppo_loc (w, r) then
            (* If (w,r) in ppo_loc, check that r is reachable from w *)
            let reachable =
              try
                let successors = Hashtbl.find ppo_loc_tree w in
                  Uset.mem successors r
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
        Uset.filter (fun (f, t) -> Uset.mem e f || Uset.mem e t) structure.rmw
      in

      (* Create environment from RF *)
      let env_rf =
        Uset.values rf
        |> List.map (fun (w, r) ->
               let just_w = List.find_opt (fun j -> j.w.label = w) j_list in
               let w_val =
                 match just_w with
                 | Some j -> vale events j.w.label r
                 | None -> vale events w r
               in
               let r_val =
                 match val_ events r with
                 | Some v -> v
                 | None -> VVar "?"
               in
                 EBinOp (w_val, "=", r_val)
           )
      in

      let check_rf =
        Uset.values rf
        |> List.map (fun (w, r) ->
               let just_w = List.find_opt (fun j -> j.w.label = w) j_list in
               let w_loc =
                 match just_w with
                 | Some j -> loce events j.w.label r
                 | None -> loce events w r
               in
               let r_loc =
                 match loc events r with
                 | Some l -> l
                 | None -> VVar "?"
               in
                 EBinOp (w_loc, "=", r_loc)
           )
      in

      (* Check 1.1: Various consistency checks *)
      let delta =
        Uset.union
          (List.fold_left
             (fun acc j -> Uset.union acc j.fwd)
             (Uset.create ()) j_list
          )
          (List.fold_left
             (fun acc j -> Uset.union acc j.we)
             (Uset.create ()) j_list
          )
      in
      let check_1_1 =
        Uset.size (Uset.intersection (pi_2 delta) (pi_1 rf_m)) = 0
        && Uset.equal (Uset.intersection e read_events) (pi_2 rf)
      in

      if not check_1_1 then Lwt.return_none
      else
        (* Check acyclicity of rhb = dp_ppo ∪ rf *)
        let rhb = Uset.union dp_ppo rf in
          if not (Uset.acyclic rhb) then Lwt.return_none
          else
            (* Rewrite predicates *)
            let big_p_exprs = p_combined @ env_rf @ check_rf in
              let* big_p_opt = Rewrite.rewrite_pred big_p_exprs in

              match big_p_opt with
              | None -> Lwt.return_none
              | Some big_p -> (
                  (* Compute atomicity pairs AF *)
                  let malloc_events = Uset.create () in
                  (* TODO: get from structure *)
                  let a = Uset.union read_events malloc_events in
                  let a_squared = Uset.cross a a in

                  let* af =
                    Uset.async_filter
                      (fun (e_1, e_2) ->
                        if e_1 >= e_2 then Lwt.return_false
                        else
                          (* Check if there's no intermediate event between e_1 and e_2 *)
                          let* has_intermediate =
                            Uset.async_exists
                              (fun ep ->
                                if
                                  not
                                    (Uset.mem rhb (e_1, ep)
                                    && Uset.mem rhb (ep, e_2)
                                    )
                                then Lwt.return_false
                                else
                                  (* Check if loc(e_1) = loc(ep) under env_rf using semeq *)
                                  let loc_e1 =
                                    match loc events e_1 with
                                    | Some l -> l
                                    | None -> VVar "?"
                                  in
                                  let loc_ep =
                                    match loc events ep with
                                    | Some l -> l
                                    | None -> VVar "?"
                                  in

                                  (* Convert to expressions for semeq *)
                                  let expr_e1 =
                                    match loc_e1 with
                                    | VExpression e -> e
                                    | v -> EVar (Value.to_string v)
                                  in
                                  let expr_ep =
                                    match loc_ep with
                                    | VExpression e -> e
                                    | v -> EVar (Value.to_string v)
                                  in

                                  Solver.exeq ~state:env_rf expr_e1 expr_ep
                              )
                              e
                          in
                            Lwt.return (not has_intermediate)
                      )
                      a_squared
                  in

                  (* Create disjointness predicates *)
                  let disj =
                    Uset.values af
                    |> List.map (fun (a, b) ->
                           let loc_a =
                             match loc events a with
                             | Some l -> l
                             | None -> VVar "?"
                           in
                           let val_a =
                             match val_ events a with
                             | Some v -> v
                             | None -> VVar "?"
                           in
                           let loc_b =
                             match loc events b with
                             | Some l -> l
                             | None -> VVar "?"
                           in
                           let val_b =
                             match val_ events b with
                             | Some v -> v
                             | None -> VVar "?"
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
                        Uset.filter
                          (fun (f, t) -> Uset.mem e f && Uset.mem e t)
                          po
                      in
                      let inv_po_tree =
                        build_tree e (Uset.inverse_relation po_filtered)
                      in

                      let check_dslwb w _r =
                        let rec f r =
                          if w = r then Lwt.return_false
                          else
                            let event_r =
                              try Some (Hashtbl.find events r)
                              with Not_found -> None
                            in
                              match event_r with
                              | Some ev when ev.typ = Write ->
                                  let loc_r =
                                    match loc events r with
                                    | Some l -> l
                                    | None -> VVar "?"
                                  in
                                  let loc__r = loce events _r _r in

                                  (* Convert to expressions for exeq *)
                                  let expr_r =
                                    match loc_r with
                                    | VExpression e -> e
                                    | v -> EVar (Value.to_string v)
                                  in
                                  let expr__r =
                                    match loc__r with
                                    | VExpression e -> e
                                    | v -> EVar (Value.to_string v)
                                  in

                                  let* same_loc =
                                    Solver.exeq ~state:bigger_p expr_r expr__r
                                  in
                                    if same_loc then Lwt.return_true
                                    else
                                      let preds =
                                        try Hashtbl.find inv_po_tree r
                                        with Not_found -> Uset.create ()
                                      in
                                        Uset.async_for_all f preds
                              | _ ->
                                  let preds =
                                    try Hashtbl.find inv_po_tree r
                                    with Not_found -> Uset.create ()
                                  in
                                    Uset.async_for_all f preds
                        in
                          let* in_po =
                            Lwt.return (Uset.mem po_filtered (w, _r))
                          in
                            if not in_po then Lwt.return_false else f _r
                      in

                      let* has_dslwb =
                        Uset.async_exists (fun (w, r) -> check_dslwb w r) rf
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

  let e = Uset.of_list path.path in
  let e_squared = Uset.cross e e in
  let pp = path.p in

  (* Compute dependency relation *)
  let dp_pairs =
    List.concat_map
      (fun just ->
        let syms = Uset.values just.d in
          List.concat_map
            (fun sym ->
              let malloc_events = Uset.create () in
                (* TODO *)
                match origin events read_events malloc_events sym with
                | Some orig -> [ (orig, just.w.label) ]
                | None -> []
            )
            syms
      )
      j_list
  in
  let dp = Uset.of_list dp_pairs in

  (* Compute combined fwd and we *)
  let f =
    List.fold_left (fun acc j -> Uset.union acc j.fwd) (Uset.create ()) j_list
  in
  let we =
    List.fold_left (fun acc j -> Uset.union acc j.we) (Uset.create ()) j_list
  in

  let delta = Uset.union f we in
  let elided = pi_2 delta in

  (* elided_rf: Delta ∩ (W × R) ∩ E² *)
  let w_cross_r = Uset.cross write_events read_events in
  let elided_rf =
    Uset.intersection delta w_cross_r |> fun s -> Uset.intersection s e_squared
  in

  let _e = Uset.set_minus e elided in

  (* Create forwarding context *)
  let con = Forwardingcontext.create ~fwd:f ~we () in

  (* Combine predicates *)
  let p_combined =
    List.concat_map (fun (j : justification) -> j.p) j_list
    @ con.psi
    @ List.concat pp
    @ statex
  in

  (* Check if predicates are satisfiable *)
  let solver = Solver.create p_combined in
    let* sat = Solver.check solver in
      match sat with
      | Some false -> Lwt.return_none
      | _ ->
          (* Check that all writes in E are either elided or have justifications *)
          let e_writes = Uset.intersection e write_events in
          let check_3 =
            Uset.for_all
              (fun w ->
                Uset.mem elided w || List.exists (fun j -> j.w.label = w) j_list
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
                      Uset.filter (fun (_, t) -> t = just.w.label) structure.po
                    in
                    let po_to_w_squared =
                      Uset.cross (pi_1 po_to_w) (pi_1 po_to_w)
                    in
                      Lwt.return (Uset.intersection ppo_j po_to_w_squared)
                )
                j_list
            in

            let ppo = List.fold_left Uset.union (Uset.create ()) ppos in
            let ppo = Uset.union ppo (Forwardingcontext.ppo_sync con) in

            (* Compute ppo_loc *)
            let* ppo_loc_base = Forwardingcontext.ppo_loc con p_combined in
            let ppo_loc = Uset.union ppo_loc_base init_ppo in

            (* Filter out read-read pairs *)
            let ppo_loc =
              Uset.filter
                (fun (a, b) ->
                  not (Uset.mem read_events a && Uset.mem read_events b)
                )
                ppo_loc
            in

            (* Compute transitive closure *)
            let ppo_loc = Uset.transitive_closure ppo_loc in
            let ppo_loc_tree = build_tree e ppo_loc in

            let dp_ppo = Uset.union dp ppo in

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
          List.filter (fun e -> Uset.mem write_events e) path.path
        in
        let path_writes_uset = Uset.of_list path_writes in

        (* Get compatible justification combinations *)
        let js_combinations = choose justmap path_writes_uset in

        (* For each combination, create remapped justifications *)
        let* freeze_fns =
          Lwt_list.map_p
            (fun j_list ->
              (* Compute combined fwd and we *)
              let fwd =
                List.fold_left
                  (fun acc j -> Uset.union acc j.fwd)
                  (Uset.create ()) j_list
              in
              let we =
                List.fold_left
                  (fun acc j -> Uset.union acc j.we)
                  (Uset.create ()) j_list
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
          Lwt.return (Uset.of_list path.path, freeze_fns_filtered)
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
let generate_executions events structure final_justs statex e_set po rmw
    write_events read_events init_ppo ~include_dependencies ~restrictions =
  let* _ = Lwt.return_unit in

  (* Build program order tree *)
  let po_tree = build_tree e_set po in
  let inv_po_tree = build_tree e_set (Uset.inverse_relation po) in

  (* Generate all paths through the control flow *)
  let paths = gen_paths events structure structure.restrict in

  (* Check if write w is downward-closed same-location write before read r *)
  let dslwb w _r =
    let rec f r =
      if w = r then false
      else
        let event_r =
          try Some (Hashtbl.find events r) with Not_found -> None
        in
          match event_r with
          | Some ev when ev.typ = Write -> (
              let loc_r =
                match loc events r with
                | Some l -> l
                | None -> VVar "?"
              in
              let loc__r = loce events _r _r in
                (* Simple string comparison - in full version would use expoteq *)
                Value.to_string loc_r = Value.to_string loc__r
                ||
                try
                  let preds = Hashtbl.find inv_po_tree r in
                    Uset.for_all f preds
                with Not_found -> true
            )
          | _ -> (
              try
                let preds = Hashtbl.find inv_po_tree r in
                  Uset.for_all f preds
              with Not_found -> true
            )
    in
      Uset.mem po (w, _r) && f _r
  in

  (* Compute initial RF relation: writes × reads that are not in po^-1 and not dslwb *)
  let inv_po = Uset.inverse_relation po in
  let w_with_init = Uset.union write_events (Uset.singleton 0) in
  let w_cross_r = Uset.cross w_with_init read_events in
  let w_cross_r_minus_inv_po = Uset.set_minus w_cross_r inv_po in

  let* _rf_pairs =
    Uset.async_filter
      (fun (w, r) ->
        if dslwb w r then Lwt.return_false
        else if w = 0 then Lwt.return_true
        else
          (* Check location equality *)
          let loc_w =
            match loc events w with
            | Some l -> l
            | None -> VVar "?"
          in
          let loc_r =
            match loc events r with
            | Some l -> l
            | None -> VVar "?"
          in
            (* Simple comparison - full version would use expoteq *)
            Lwt.return (Value.to_string loc_w = Value.to_string loc_r)
      )
      w_cross_r_minus_inv_po
  in

  let all_rf = _rf_pairs in

  (* Build justification map: write label -> list of justifications *)
  let justmap = Hashtbl.create 16 in
    Uset.iter
      (fun (just : justification) ->
        let label = just.w.label in
        let existing = try Hashtbl.find justmap label with Not_found -> [] in
          Hashtbl.replace justmap label (just :: existing)
      )
      final_justs;

    (* Build justcombos for all paths *)
    let* justcombos =
      build_justcombos events structure paths write_events read_events init_ppo
        statex justmap
    in

    (* Enumerate over all RF sets and generate executions *)
    let paths_with_uset = List.map (fun p -> { p with path = p.path }) paths in

    (* Filter function for RF enumeration *)
    let rf_filter = Uset.intersection (Uset.cross e_set e_set) po in

    (* Enumerate RF sets - simplified version *)
    (* In full version, this would use a more sophisticated RF enumeration *)
    let* all_executions =
      (* For each path, try to build executions *)
      Lwt_list.map_p
        (fun path ->
          let path_uset = Uset.of_list path.path in

          (* Get freeze functions for this path *)
          let freeze_fns =
            try Hashtbl.find justcombos path_uset with Not_found -> []
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

    let flat_execs = List.concat all_executions in

    (* Convert freeze_results to executions *)
    let* final_executions =
      Lwt_list.map_p
        (fun (freeze_res : freeze_result) ->
          (* Fixed point computation for RF mapping *)
          let fix_rf_map = Hashtbl.create 16 in

          (* Build initial mapping from RF *)
          Uset.iter
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
                match val_ events r with
                | Some v -> v
                | None -> VVar "?"
              in

              (* Store mapping *)
              Hashtbl.replace fix_rf_map (Value.to_string r_val) w_val
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
                  | VVar v -> (
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
              ex_p = List.concat freeze_res.pp;
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
