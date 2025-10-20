open Expr
open Types
open Justifications
open Lwt.Syntax

type context = {
  structure : symbolic_event_structure;
  events : (int, event) Hashtbl.t;
  e_set : int Uset.t;
  branch_events : int Uset.t;
  read_events : int Uset.t;
  write_events : int Uset.t;
  malloc_events : int Uset.t;
  po : (int * int) Uset.t;
  rmw : (int * int) Uset.t;
  fj : (int * int) Uset.t;
  val_fn : int -> value_type option;
  build_tree : (int * int) Uset.t -> (int, int Uset.t) Hashtbl.t;
  conflicting_branch : int -> int -> int;
}

let pred (elab_ctx : context) (ctx : Forwardingcontext.t option)
    (p : expr list option) ?ppo () =
  let* ppo_result =
    match ppo with
    | Some ppo_val -> ppo_val
    | None -> (
        match (ctx, p) with
        | Some ctx_val, Some p_val -> Forwardingcontext.ppo ctx_val p_val
        | _ -> failwith "ctx and p must be provided when ppo is not given"
      )
  in
  let inversed = Uset.inverse_relation ppo_result in
  let tree = elab_ctx.build_tree inversed in
    Lwt.return (fun e -> Hashtbl.find tree e)

let filter elab_ctx (justs : justification list) =
  let landmark = Landmark.register "dp.filter" in
    Landmark.enter landmark;

    let* (justs' : justification option list) =
      Lwt_list.map_p
        (fun (just : justification) ->
          let* p' = Rewrite.rewrite_pred just.p in
            match p' with
            | Some p -> Lwt.return_some { just with p }
            | None -> Lwt.return_none
        )
        justs
    in

    let (justs'' : justification list) = List.filter_map Fun.id justs' in

    (* Remove covered justifications *)
    let indexed = List.mapi (fun i j -> (i, j)) justs'' in
    let result =
      indexed
      |> List.filter (fun (i, (j : justification)) ->
             not
               (List.exists
                  (fun (i', (j' : justification)) ->
                    i' > i
                    && List.length j'.p < List.length j.p
                    && List.for_all (fun e -> List.mem e j.p) j'.p
                  )
                  indexed
               )
         )
      |> List.map snd
      |> Uset.of_list
    in

    Landmark.exit landmark;
    Lwt.return result

let value_assign elab_ctx justs =
  let landmark = Landmark.register "dp.va" in
    Landmark.enter landmark;

    let* results =
      Lwt_list.map_p
        (fun (just : justification) ->
          let solver = Solver.create just.p in
            let* model = Solver.solve solver in
              match model with
              | Some bindings ->
                  let new_wval =
                    match just.w.wval with
                    | Some (VVar v) -> (
                        match Solver.concrete_value bindings v with
                        | Some value -> Some value
                        | None -> just.w.wval
                      )
                    | _ -> just.w.wval
                  in
                  let new_w = { just.w with wval = new_wval } in
                    Lwt.return
                      { just with w = new_w; op = ("va", Some just, None) }
              | None -> Lwt.return just
        )
        justs
    in

    Landmark.exit landmark;
    Lwt.return (Uset.of_list results)

let fprime elab_ctx pred_fn ppo_loc =
  let w_cross_r = Uset.cross elab_ctx.write_events elab_ctx.read_events in
  let r_cross_r = Uset.cross elab_ctx.read_events elab_ctx.read_events in
  let w_cross_w = Uset.cross elab_ctx.write_events elab_ctx.write_events in
  let combined = Uset.union w_cross_r r_cross_r in
  let combined = Uset.union combined w_cross_w in
  let in_po = Uset.intersection combined elab_ctx.po in
    Uset.filter
      (fun (e1, e2) -> Uset.mem ppo_loc (e1, e2) && Uset.mem (pred_fn e2) e1)
      in_po

(* Define fwd function *)
let fwd elab_ctx pred_fn (ctx : Forwardingcontext.t) ppo_loc =
  let edges = fprime elab_ctx pred_fn ppo_loc in
    Uset.filter
      (fun (e1, e2) ->
        try
          let ev2 = Hashtbl.find elab_ctx.events e2 in
            (not ev2.volatile)
            &&
            if ev2.typ = Write then
              let remapped = Forwardingcontext.remap ctx e2 in
              let ev_remapped = Hashtbl.find elab_ctx.events remapped in
                ev_remapped.wmod = Relaxed
            else true
        with Not_found -> false
      )
      edges

(* Define we function *)
let we elab_ctx pred_fn (ctx : Forwardingcontext.t) ppo_loc =
  let edges = fprime elab_ctx pred_fn ppo_loc in
    Uset.filter
      (fun (e1, e2) ->
        try
          let ev1 = Hashtbl.find elab_ctx.events e1 in
          let ev2 = Hashtbl.find elab_ctx.events e2 in
            (not ev1.volatile) && ev1.typ = Write && ev2.typ = Write
        with Not_found -> false
      )
      edges
    |> Uset.map (fun (e1, e2) -> (e2, e1))

let forward elab_ctx justs =
  let landmark = Landmark.register "dp.forward" in
    Landmark.enter landmark;

    let* out =
      (* Map over justifications *)
      let* results =
        Lwt_list.map_p
          (fun (just : justification) ->
            (* Determine paths to check *)
            let ps =
              if elab_ctx.structure.pwg <> [] then
                [ just.p; just.p @ elab_ctx.structure.pwg ]
              else [ just.p ]
            in

            (* Map over each path *)
            let* path_results =
              Lwt_list.map_p
                (fun p ->
                  let ctx =
                    Forwardingcontext.create ~fwd:just.fwd ~we:just.we ()
                  in
                    let* ppo = Forwardingcontext.ppo ctx p in
                      let* ppo_loc = Forwardingcontext.ppo_loc ctx p in
                        let* _pred =
                          pred elab_ctx None None ~ppo:(Lwt.return ppo) ()
                        in

                        (* Subtract fj from ppo_loc *)
                        let _ppo_loc = Uset.set_minus ppo_loc elab_ctx.fj in

                        (* Compute fwd and we edges *)
                        let _fwd = fwd elab_ctx _pred ctx _ppo_loc in
                        let _we = we elab_ctx _pred ctx _ppo_loc in

                        (* Filter edges by label *)
                        let _fwd =
                          Uset.filter (fun (_, e2) -> e2 <> just.w.label) _fwd
                        in
                        let _we =
                          Uset.filter (fun (_, e2) -> e2 <> just.w.label) _we
                        in

                        (* Filter edge function *)
                        let filtedge (edge, new_fwd, new_we) =
                          if Forwardingcontext.is_bad new_fwd new_we then
                            Lwt.return_false
                          else if Forwardingcontext.is_good new_fwd new_we then
                            Lwt.return_true
                          else
                            let con =
                              Forwardingcontext.create ~fwd:new_fwd ~we:new_we
                                ()
                            in
                              Forwardingcontext.check con
                        in

                        (* Create fwd edges with contexts *)
                        let fwdedges =
                          Uset.values _fwd
                          |> List.map (fun edge ->
                                 ( edge,
                                   Uset.union just.fwd (Uset.singleton edge),
                                   just.we
                                 )
                             )
                        in

                        (* Create we edges with contexts *)
                        let weedges =
                          Uset.values _we
                          |> List.map (fun edge ->
                                 ( edge,
                                   just.fwd,
                                   Uset.union just.we (Uset.singleton edge)
                                 )
                             )
                        in

                        (* Filter both edge types *)
                        let* filtered_fwd =
                          Lwt_list.filter_p filtedge fwdedges
                        in
                          let* filtered_we =
                            Lwt_list.filter_p filtedge weedges
                          in

                          (* Remap justifications *)
                          let fwd_justs =
                            List.map
                              (fun (edge, new_fwd, new_we) ->
                                let con =
                                  Forwardingcontext.create ~fwd:new_fwd
                                    ~we:new_we ()
                                in
                                  Forwardingcontext.remap_just con just
                                    (Some ("fwd", Some just, None))
                              )
                              filtered_fwd
                          in

                          let we_justs =
                            List.map
                              (fun (edge, new_fwd, new_we) ->
                                let con =
                                  Forwardingcontext.create ~fwd:new_fwd
                                    ~we:new_we ()
                                in
                                  Forwardingcontext.remap_just con just
                                    (Some ("we", Some just, None))
                              )
                              filtered_we
                          in

                          Lwt.return (fwd_justs @ we_justs)
                )
                ps
            in
              Lwt.return (List.concat path_results)
          )
          (Uset.values justs)
      in

      (* Flatten results and convert to USet *)
      let flattened = List.concat results in
        Lwt.return (Uset.of_list flattened)
    in

    (* Simplified forwarding *)
    Landmark.exit landmark;
    Lwt.return out

let strengthen elab_ctx (just_1 : justification) (just_2 : justification) ppo
    con =
  let landmark = Landmark.register "dp.strengthen" in
    Landmark.enter landmark;

    let p_1 = Uset.of_list just_1.p in
    let p_2 = Uset.of_list just_2.p in
    let w_1 = just_1.w in
    let w_2 = just_2.w in
    let e_1 = w_1.label in
    let e_2 = w_2.label in

    (* Get symbols for an event *)
    let gsyms e =
      let po_neighbors =
        Uset.filter (fun (f, t) -> f = e || t = e) elab_ctx.po
        |> Uset.map (fun (f, t) -> [ f; t ])
        |> fun s ->
        Uset.fold (fun acc pairs -> pairs @ acc) s [] |> Uset.of_list
      in
      let r_union_a = Uset.union elab_ctx.read_events elab_ctx.malloc_events in
        Uset.intersection po_neighbors r_union_a
        |> Uset.filter (fun ep -> not (Uset.mem ppo (e, ep)))
        |> Uset.map (fun ep ->
               let remapped = Forwardingcontext.remap con ep in
                 match elab_ctx.val_fn remapped with
                 | Some (VSymbol s) when is_symbol s -> Some s
                 | _ -> None
           )
        |> Uset.filter (fun x -> x <> None)
        |> Uset.map (fun x ->
               match x with
               | Some s -> s
               | None -> ""
           )
    in

    let syms_1 = gsyms e_1 in
    let syms_2 = gsyms e_2 in
    let cs = Uset.intersection syms_1 syms_2 in
    let syms_1 = Uset.set_minus syms_1 cs in
    let syms_2 = Uset.set_minus syms_2 cs in
    let pos_rp = Uset.cross syms_1 syms_2 in

    (* Get necessary symbols *)
    let get_expr_symbols exprs =
      List.map Expr.get_symbols exprs |> List.concat |> Uset.of_list
    in

    let w1_syms =
      match elab_ctx.val_fn w_1.label with
      | Some v -> Value.get_symbols v
      | None -> []
    in
    let w2_syms =
      match elab_ctx.val_fn w_2.label with
      | Some v -> Value.get_symbols v
      | None -> []
    in

    let ness_1 =
      let p1_syms = get_expr_symbols just_1.p in
        Uset.union p1_syms (Uset.of_list w1_syms) |> fun s ->
        Uset.intersection s syms_1
    in
    let ness_2 =
      let p2_syms = get_expr_symbols just_2.p in
        Uset.union p2_syms (Uset.of_list w2_syms) |> fun s ->
        Uset.intersection s syms_2
    in
    let ness = Uset.union ness_1 ness_2 in

    (* Get branch predicate *)
    let bp_event =
      Hashtbl.find elab_ctx.events (elab_ctx.conflicting_branch e_1 e_2)
    in
    let bp =
      match bp_event.cond with
      | Some (VExpression e) -> e
      | _ -> failwith "Expected expression in cond"
    in
    let bpi = Expr.inverse bp in

    (* Compute uncommon predicates *)
    let uncommon = Uset.difference p_1 p_2 in
    let uncommonstr =
      Uset.filter (fun x -> not (Uset.mem uncommon (Expr.inverse x))) uncommon
    in

    let notcommon_1 = Uset.set_minus uncommonstr p_2 in
    let notcommon_2 = Uset.set_minus uncommonstr p_1 in

    (* Iterator function *)
    let it n_1 n_2 =
      let ncs_1 =
        Uset.values n_1
        |> List.map Expr.get_symbols
        |> List.concat
        |> Uset.of_list
        |> fun s -> Uset.set_minus s cs
      in
      let ncs_2 =
        Uset.values n_2
        |> List.map Expr.get_symbols
        |> List.concat
        |> Uset.of_list
        |> fun s -> Uset.set_minus s cs
      in
      let rls = ref (Uset.values (Uset.union ncs_1 ncs_2)) in

      let str_1 = ref (Uset.union p_1 n_2) in
      let str_2 = ref (Uset.union p_2 n_1) in
      let i = ref 0 in

      let rp =
        let filter1 =
          Uset.filter
            (fun (f, t) ->
              not (Uset.exists (fun (f2, t2) -> f2 = f && t <> t2) pos_rp)
            )
            pos_rp
        in
        let filter2 =
          Uset.filter
            (fun (f, t) ->
              not (Uset.exists (fun (f2, t2) -> t2 = t && f <> f2) pos_rp)
            )
            pos_rp
        in
          ref (Uset.union filter1 filter2)
      in

      while !rls <> [] && !i < 10 do
        incr i;
        let s = List.hd !rls in
          rls := List.tl !rls;

          let relabels = Uset.filter (fun (a, b) -> a = s || b = s) pos_rp in
            if Uset.size relabels = 0 then rls := []
            else if Uset.size relabels <> 1 then
              assert
                (* debugger - assertion failure *)
                false
            else
              let values = Uset.values relabels in
              let f, t = List.hd values in
                rp := Uset.add !rp (f, t);

                str_1 :=
                  Uset.map
                    (fun x -> Expr.subst x (VSymbol t) (VSymbol f))
                    !str_1;
                str_2 :=
                  Uset.map
                    (fun x -> Expr.subst x (VSymbol f) (VSymbol t))
                    !str_2;

                rls := List.filter (fun x -> x <> f && x <> t) !rls
      done;

      if !rls = [] || !i >= 10 then
        [ (Uset.values !str_1, Uset.values !str_2, !rp) ]
      else []
    in

    (* Generate all combinations *)
    let empty_set = Uset.create () in
    let results =
      [
        it notcommon_1 notcommon_2;
        it empty_set empty_set;
        it empty_set notcommon_2;
        it notcommon_1 empty_set;
      ]
    in

    let out =
      List.filter (fun x -> x <> []) results
      |> List.concat
      |> List.filter (fun (_, _, r) ->
             Uset.for_all
               (fun x -> Uset.exists (fun (y0, y1) -> x = y0 || x = y1) r)
               ness
         )
    in

    Landmark.exit landmark;
    Lwt.return out

let conflict (elab_ctx : context) events =
  (* Build po tree *)
  let po_tree = elab_ctx.build_tree elab_ctx.po in

  (* Semicolon composition *)
  let semicolon r1 r2 =
    let result = Uset.create () in
      Uset.iter
        (fun (a, b) ->
          Uset.iter
            (fun (c, d) -> if b = c then Uset.add result (a, d) |> ignore)
            r2
        )
        r1;
      result
  in

  (* Compute all successors of x in po (including x) *)
  let it x =
    let singleton = Uset.singleton (x, x) in
    let composed = semicolon singleton elab_ctx.po in
    let successors = Uset.map (fun (_, y) -> y) composed in
      Uset.add successors x
  in

  (* Process each branch event *)
  let branch_results =
    Uset.map
      (fun x ->
        let successors =
          try Hashtbl.find po_tree x with Not_found -> Uset.create ()
        in
        let values = Uset.values successors in
          match values with
          | [ a; b ] ->
              let ita = it a in
              let itb = it b in

              (* Remove common elements *)
              let ita_clone = Uset.clone ita in
                Uset.iter
                  (fun e ->
                    if Uset.mem itb e then (
                      Uset.remove ita e |> ignore;
                      Uset.remove itb e |> ignore
                    )
                  )
                  ita_clone;

                (* Cross product and inverse *)
                let cross = Uset.cross ita itb in
                let inverse = Uset.inverse_relation cross in
                  Uset.union cross inverse
          | _ -> Uset.create ()
      )
      elab_ctx.branch_events
  in

  (* Union all results *)
  Uset.fold (fun acc s -> Uset.union acc s) branch_results (Uset.create ())

let lift elab_ctx justs =
  let landmark = Landmark.register "dp.lift" in
    Landmark.enter landmark;

    let ctx = Forwardingcontext.create () in

    (* Simplified lifting *)
    Landmark.exit landmark;
    Lwt.return justs

let weaken elab_ctx justs =
  let landmark = Landmark.register "dp.weaken" in
    Landmark.enter landmark;

    if elab_ctx.structure.pwg = [] then (
      Landmark.exit landmark;
      Lwt.return justs
    )
    else
      let* out =
        Lwt_list.map_p
          (fun (just : justification) ->
            let con = Forwardingcontext.create ~fwd:just.fwd ~we:just.we () in

            (* Filter predicates that are not implied by PWG *)
            let* filtered_p =
              Lwt_list.filter_p
                (fun x ->
                  (* Remap PWG predicates using the forwarding context *)
                  let remapped_pwg =
                    List.map
                      (Forwardingcontext.remap_expr con)
                      elab_ctx.structure.pwg
                  in

                  (* Create formula: And(remapped_pwg) ∧ Not(x) *)
                  (* If SAT, then x is not implied by pwg, so keep it *)
                  let not_x = Expr.inverse x in
                  let formula = remapped_pwg @ [ not_x ] in

                  let solver = Solver.create formula in
                    let* result = Solver.check solver in
                      match result with
                      | Some true ->
                          Lwt.return_true
                          (* SAT: x not implied by pwg, keep it *)
                      | Some false ->
                          Lwt.return_false
                          (* UNSAT: x implied by pwg, remove it *)
                      | None -> Lwt.return_true
                  (* Unknown: keep predicate to be safe *)
                )
                just.p
            in

            Lwt.return
              { just with p = filtered_p; op = ("weak", Some just, None) }
          )
          justs
      in

      Landmark.exit landmark;
      Lwt.return out
