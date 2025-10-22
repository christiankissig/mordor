open Lwt.Syntax
open Expr
open Trees
open Types

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
  let tree = build_tree elab_ctx.e_set inversed in
    Lwt.return (fun e -> Hashtbl.find tree e)

(** Lifted cache for relations with forwarding context *)
type lifted_cache = {
  mutable t : (justification * justification) Uset.t;
  mutable to_ : ((justification * justification) * justification list) Uset.t;
}

(** Create a new lifted cache *)
let create_lifted_cache () = { t = Uset.create (); to_ = Uset.create () }

(** Compare two events for equality *)
let event_equal e1 e2 = e1.label = e2.label && e1.van = e2.van

let lifted_has cache (a, b) =
  (* Filter to find matching elements *)
  let vals =
    Uset.filter
      (fun ((_a, _b), _) ->
        (* Compare write events *)
        event_equal _a.w a.w
        && event_equal _b.w b.w
        (* Compare predicates as sets *)
        && Uset.equal (Uset.of_list _a.p) (Uset.of_list a.p)
        && Uset.equal (Uset.of_list _b.p) (Uset.of_list b.p)
        (* Compare forwarding and write-elision sets *)
        && Uset.equal _a.fwd a.fwd
        && Uset.equal _a.we a.we
      )
      cache.to_
  in

  if Uset.size vals > 0 then
    (* Return mapped justifications *)
    let results =
      Uset.map
        (fun ((_, _), (justifs : justification list)) ->
          (* Add type annotation here *)
          List.map
            (fun (x : justification) ->
              (* Add type annotation here *)
              {
                p = x.p;
                d = x.d;
                fwd = a.fwd;
                we = a.we;
                w = x.w;
                op = ("lifted", Some a, None);
              }
            )
            justifs
        )
        vals
      |> Uset.values
      |> List.flatten
    in
      Some results
  else if Uset.mem cache.t (a, b) then Some []
  else None

(** Add pair to cache *)
let lifted_add cache (a, b) = Uset.add cache.t (a, b) |> ignore

(** Add mapping to results cache *)
let lifted_to cache x r = Uset.add cache.to_ (x, r) |> ignore

(** Clear cache *)
let lifted_clear cache =
  Uset.clear cache.t |> ignore;
  Uset.clear cache.to_ |> ignore

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
  let po_tree = build_tree elab_ctx.e_set elab_ctx.po in

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

(** Helper: Get write value from event *)
let val_of_event e = e.wval

(** Helper: Get location from event *)
let loc e = e.id

(** Helper: Parse dependency symbol to get origin event label *)
let origin s =
  (* Dependency symbols are typically formatted as "symbol@label" *)
  try
    let parts = String.split_on_char '@' s in
      match parts with
      | [ _; label ] -> int_of_string label
      | _ -> failwith ("Invalid dependency symbol: " ^ s)
  with _ -> failwith ("Failed to parse origin: " ^ s)

(** Helper: Check if justification is independent *)
let independent just =
  Uset.size just.fwd = 0 && Uset.size just.we = 0 && Uset.size just.d = 0

(** Helper: Apply relabeling substitutions *)
let relabel expr pairs =
  Uset.fold
    (fun acc (f, t) -> Expr.subst acc (VSymbol f) (VSymbol t))
    pairs expr

(** Helper: Apply inverse relabeling substitutions *)
let unlabel expr pairs =
  Uset.fold
    (fun acc (f, t) -> Expr.subst acc (VSymbol t) (VSymbol f))
    pairs expr

(** Check if two expressions are equivalent under predicates using Z3 *)
let relabel_equivalent_expressions elab_ctx con statex p_1 p_2 relabelPairs e_1
    e_2 =
  (* Remap and relabel e_1 *)
  let e_1_remapped = Forwardingcontext.remap_expr con e_1 in
  let e_1_relabeled =
    match e_1_remapped with
    | VExpression expr -> VExpression (relabel expr relabelPairs)
    | v -> v
  in

  (* Remap e_2 *)
  let e_2_remapped = Forwardingcontext.remap_expr con e_2 in

  (* Quick check: if they're the same, return true *)
  if Value.equal e_1_relabeled e_2_remapped then Lwt.return_true
  else
    (* Check if e_1 = e_2 clashes with static constraints *)
    let e1_eq_e2 = EBinOp (e_1_relabeled, "=", e_2_remapped) in
    let stat_clash = Solver.create (statex @ [ e1_eq_e2 ]) in
      let* clash_result = Solver.check stat_clash in
        match clash_result with
        | Some false ->
            Lwt.return_false (* UNSAT: expressions cannot be equal *)
        | _ -> (
            (* Use Z3 exists quantification *)
            (* Formula: ∃v. (p_1 => e_1 = v) ∧ (p_2 => e_2 = v) *)
            let context = Solver.create_context () in
            let v_name = "0v0" in
            let v_sort = Z3.Arithmetic.Integer.mk_sort context.ctx in
            let v_symbol = Z3.Symbol.mk_string context.ctx v_name in
            let v_var = Z3.Expr.mk_const context.ctx v_symbol v_sort in

            (* Convert predicates to Z3 *)
            let p_1_z3 =
              match p_1 with
              | [] -> Z3.Boolean.mk_true context.ctx
              | _ ->
                  let exprs = List.map (Solver.expr_to_z3 context) p_1 in
                    Z3.Boolean.mk_and context.ctx exprs
            in
            let p_2_z3 =
              match p_2 with
              | [] -> Z3.Boolean.mk_true context.ctx
              | _ ->
                  let exprs = List.map (Solver.expr_to_z3 context) p_2 in
                    Z3.Boolean.mk_and context.ctx exprs
            in

            (* e_1 = v *)
            let e_1_z3 = Solver.value_to_z3 context e_1_relabeled in
            let e1_eq_v = Z3.Boolean.mk_eq context.ctx e_1_z3 v_var in

            (* e_2 = v *)
            let e_2_z3 = Solver.value_to_z3 context e_2_remapped in
            let e2_eq_v = Z3.Boolean.mk_eq context.ctx e_2_z3 v_var in

            (* (p_1 => e_1 = v) ∧ (p_2 => e_2 = v) *)
            let imply1 = Z3.Boolean.mk_implies context.ctx p_1_z3 e1_eq_v in
            let imply2 = Z3.Boolean.mk_implies context.ctx p_2_z3 e2_eq_v in
            let body = Z3.Boolean.mk_and context.ctx [ imply1; imply2 ] in

            (* Add static constraints *)
            let statex_z3 = List.map (Solver.expr_to_z3 context) statex in
            let full_formula =
              Z3.Boolean.mk_and context.ctx (statex_z3 @ [ body ])
            in

            (* ∃v. formula *)
            let exists =
              Z3.Quantifier.mk_exists context.ctx [ v_sort ] [ v_symbol ]
                full_formula None [] [] None None
            in
            let exists_expr = Z3.Quantifier.expr_of_quantifier exists in

            (* Check satisfiability *)
            Z3.Solver.add context.solver [ exists_expr ];
            let result = Z3.Solver.check context.solver [] in

            match result with
            | Z3.Solver.SATISFIABLE -> Lwt.return_true
            | _ -> Lwt.return_false
          )

(** Recursively check if two events are equivalent *)
let rec relabel_equivalent elab_ctx con statex p_1 p_2 relabelPairs _pred
    label_1 label_2 =
  (* Get events from labels *)
  let e_1 =
    try Hashtbl.find elab_ctx.events label_1
    with Not_found -> failwith ("Event not found: " ^ string_of_int label_1)
  in
  let e_2 =
    try Hashtbl.find elab_ctx.events label_2
    with Not_found -> failwith ("Event not found: " ^ string_of_int label_2)
  in

  if e_1.label = e_2.label then Lwt.return_true
  else
    (* Get predecessors *)
    let pred_1 = _pred e_1.label in
    let pred_2 = _pred e_2.label in

    let ps1 = Uset.size pred_1 = 0 in
    let ps2 = Uset.size pred_2 = 0 in

    if ps1 <> ps2 then Lwt.return_false
    else if e_1.typ <> e_2.typ then Lwt.return_false
    else
      match e_1.typ with
      | Fence -> Lwt.return_true
      | Read | Write | Malloc -> (
          let* loc_eq =
            match (loc e_1, loc e_2) with
            | Some l1, Some l2 ->
                relabel_equivalent_expressions elab_ctx con statex p_1 p_2
                  relabelPairs l1 l2
            | None, None -> Lwt.return_true
            | _ -> Lwt.return_false
          in
            if not loc_eq then Lwt.return_false
            else
              let* val_eq =
                match (val_of_event e_1, val_of_event e_2) with
                | Some v1, Some v2 ->
                    relabel_equivalent_expressions elab_ctx con statex p_1 p_2
                      relabelPairs v1 v2
                | None, None -> Lwt.return_true
                | _ -> Lwt.return_false
              in
                if not val_eq then Lwt.return_false
                else if ps1 then Lwt.return_true
                else
                  (* Recurse on predecessors *)
                  let pred_1_vals = Uset.values pred_1 in
                  let pred_2_vals = Uset.values pred_2 in
                    match (pred_1_vals, pred_2_vals) with
                    | [ p1 ], [ p2 ] ->
                        relabel_equivalent elab_ctx con statex p_1 p_2
                          relabelPairs _pred p1 p2
                    | _ -> Lwt.return_false
        )
      | Free -> (
          let* loc_eq =
            match (loc e_1, loc e_2) with
            | Some l1, Some l2 ->
                relabel_equivalent_expressions elab_ctx con statex p_1 p_2
                  relabelPairs l1 l2
            | None, None -> Lwt.return_true
            | _ -> Lwt.return_false
          in
            if not loc_eq then Lwt.return_false
            else if ps1 then Lwt.return_true
            else
              let pred_1_vals = Uset.values pred_1 in
              let pred_2_vals = Uset.values pred_2 in
                match (pred_1_vals, pred_2_vals) with
                | [ p1 ], [ p2 ] ->
                    relabel_equivalent elab_ctx con statex p_1 p_2 relabelPairs
                      _pred p1 p2
                | _ -> Lwt.return_false
        )
      | _ -> Lwt.return_true

let lift elab_ctx justs =
  let landmark = Landmark.register "dp.lift" in
    Landmark.enter landmark;

    (* Static constraints from structure *)
    let statex = elab_ctx.structure.constraint_ in

    (* Create justification map: event label -> set of justifications *)
    let justmap = Hashtbl.create 16 in
      Uset.iter
        (fun just ->
          let label = just.w.label in
          let existing =
            match Hashtbl.find_opt justmap label with
            | Some s -> s
            | None -> Uset.create ()
          in
            Hashtbl.replace justmap label (Uset.add existing just)
        )
        justs;

      (* Compute liftpairs: conflicting write pairs *)
      let w_cross_w = Uset.cross elab_ctx.write_events elab_ctx.write_events in
      let conflict_set = conflict elab_ctx elab_ctx.e_set in
      let liftpairs = Uset.intersection w_cross_w conflict_set in

      (* Create pairs of justifications from liftpairs *)
      let pairs =
        Uset.fold
          (fun acc (a, b) ->
            let justs_a =
              match Hashtbl.find_opt justmap a with
              | Some s -> s
              | None -> Uset.create ()
            in
            let justs_b =
              match Hashtbl.find_opt justmap b with
              | Some s -> s
              | None -> Uset.create ()
            in
              Uset.union acc (Uset.cross justs_a justs_b)
          )
          liftpairs (Uset.create ())
      in

      (* Create lifted cache *)
      let lifted = create_lifted_cache () in

      (* If no pairs to lift, return input unchanged *)
      if Uset.size pairs = 0 then (
        Landmark.exit landmark;
        Lwt.return justs
      )
      else
        (* Process each pair of justifications *)
        let* out =
          Lwt_list.map_p
            (fun (just_1, just_2) ->
              let ojust_1 = just_1 in
              let ojust_2 = just_2 in

              (* Check if contexts match and not both independent *)
              if
                (not (Uset.equal just_1.fwd just_2.fwd))
                || (not (Uset.equal just_1.we just_2.we))
                || (independent just_1 && independent just_2)
              then Lwt.return []
              else
                (* Check lifted cache *)
                match lifted_has lifted (just_1, just_2) with
                | Some cached -> Lwt.return cached
                | None ->
                    (* Add to cache to prevent recomputation *)
                    lifted_add lifted (just_1, just_2);
                    lifted_add lifted (just_2, just_1);

                    (* Create forwarding context *)
                    let con =
                      Forwardingcontext.create ~fwd:just_1.fwd ~we:just_1.we ()
                    in

                    (* Compute ppo for both justifications *)
                    let* ppo_1 = Forwardingcontext.ppo con just_1.p in
                      let* ppo_2 = Forwardingcontext.ppo con just_2.p in
                      let ppo = Uset.union ppo_1 ppo_2 in

                      (* Get pred function *)
                      let* _pred =
                        pred elab_ctx None None ~ppo:(Lwt.return ppo) ()
                      in

                      (* Clone and unify values if needed *)
                      let just_1, just_2 =
                        match
                          (val_of_event just_1.w, val_of_event just_2.w)
                        with
                        | Some (VNumber n1), Some v2 when not (is_number v2) ->
                            (* just_1 has number, just_2 has symbol - unify *)
                            let eq_pred = EBinOp (v2, "=", VNumber n1) in
                            let new_w2 =
                              { just_2.w with wval = Some (VNumber n1) }
                            in
                              ( just_1,
                                {
                                  just_2 with
                                  p = just_2.p @ [ eq_pred ];
                                  w = new_w2;
                                  d = Uset.create ();
                                }
                              )
                        | Some v1, Some (VNumber n2) when not (is_number v1) ->
                            (* just_2 has number, just_1 has symbol - unify *)
                            let eq_pred = EBinOp (v1, "=", VNumber n2) in
                            let new_w1 =
                              { just_1.w with wval = Some (VNumber n2) }
                            in
                              ( {
                                  just_1 with
                                  p = just_1.p @ [ eq_pred ];
                                  w = new_w1;
                                  d = Uset.create ();
                                },
                                just_2
                              )
                        | _ -> (just_1, just_2)
                      in

                      (* Strengthen the pair *)
                      let* str = strengthen elab_ctx just_1 just_2 ppo con in

                      (* Process each strengthening result *)
                      let* results =
                        Lwt_list.map_p
                          (fun (str_1, str_2, relabelPairs) ->
                            (* Update predicates *)
                            let just_1 = { just_1 with p = str_1 } in
                            let just_2 = { just_2 with p = str_2 } in

                            (* Check uniqueness of relabel pairs *)
                            let from_syms =
                              Uset.map (fun (f, _) -> f) relabelPairs
                            in
                            let to_syms =
                              Uset.map (fun (_, t) -> t) relabelPairs
                            in
                              if
                                Uset.size from_syms <> Uset.size relabelPairs
                                || Uset.size to_syms <> Uset.size relabelPairs
                              then Lwt.return []
                              else
                                (* Apply relabeling to predicates *)
                                let p_1 =
                                  List.map
                                    (fun x ->
                                      let remapped =
                                        Forwardingcontext.remap_expr con x
                                      in
                                        relabel remapped relabelPairs
                                    )
                                    just_1.p
                                in
                                let p_2 =
                                  List.map
                                    (fun x -> Forwardingcontext.remap_expr con x)
                                    just_2.p
                                in

                                (* Check if writes are equivalent *)
                                let* writes_eq =
                                  relabel_equivalent elab_ctx con statex p_1 p_2
                                    relabelPairs _pred just_1.w.label
                                    just_2.w.label
                                in
                                  if not writes_eq then Lwt.return []
                                  else
                                    (* Check if all dependencies have equivalent origins *)
                                    let* deps_eq =
                                      Uset.async_for_all
                                        (fun s_1 ->
                                          Uset.async_exists
                                            (fun s_2 ->
                                              relabel_equivalent elab_ctx con
                                                statex p_1 p_2 relabelPairs
                                                _pred (origin s_1) (origin s_2)
                                            )
                                            just_2.d
                                        )
                                        just_1.d
                                    in
                                      if not deps_eq then Lwt.return []
                                      else
                                        (* Compute P_prime: simplify (p_1 OR p_2) *)
                                        let p_1_relabeled =
                                          List.map
                                            (fun x -> relabel x relabelPairs)
                                            p_1
                                        in
                                        let disjunction =
                                          [ p_1_relabeled; p_2 ]
                                          (* CNF: list of clauses *)
                                        in
                                          let* simplified =
                                            Solver.simplify_disjunction
                                              disjunction
                                          in
                                            match simplified with
                                            | None -> Lwt.return []
                                            | Some clauses ->
                                                (* Create output justifications for each clause *)
                                                let outputs =
                                                  List.map
                                                    (fun clause ->
                                                      [
                                                        {
                                                          p =
                                                            List.map
                                                              (fun x ->
                                                                unlabel x
                                                                  relabelPairs
                                                              )
                                                              clause;
                                                          fwd = just_1.fwd;
                                                          we = just_1.we;
                                                          d = just_1.d;
                                                          w = just_1.w;
                                                          op =
                                                            ( "lift",
                                                              Some just_1,
                                                              Some
                                                                (EVar "just_2")
                                                            );
                                                        };
                                                        {
                                                          p = clause;
                                                          fwd = just_1.fwd;
                                                          we = just_1.we;
                                                          d = just_2.d;
                                                          w = just_2.w;
                                                          op =
                                                            ( "lift",
                                                              Some just_2,
                                                              Some
                                                                (EVar "just_1")
                                                            );
                                                        };
                                                      ]
                                                    )
                                                    clauses
                                                  |> List.concat
                                                in
                                                  Lwt.return outputs
                          )
                          str
                      in

                      let out = List.concat results in
                        (* Store in cache *)
                        lifted_to lifted (ojust_1, ojust_2) out;
                        Lwt.return out
            )
            (Uset.values pairs)
        in

        let result = List.concat out |> Uset.of_list in
          Landmark.exit landmark;
          Lwt.return result

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
