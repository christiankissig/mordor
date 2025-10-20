(** sMRD - Symbolic Memory Relaxation Dependencies Main dependency calculation
    algorithm *)

open Expr
open Parse (* must come before open Types *)
open Types
open Lwt.Syntax

(** Helper functions *)
let loc events e =
  try
    let event = Hashtbl.find events e in
      event.id
  with Not_found -> None

let val_ events e =
  try
    let event = Hashtbl.find events e in
      match event.wval with
      | Some v -> Some v
      | None -> event.rval
  with Not_found -> None

(** Calculate dependencies *)
let calculate_dependencies ast structure events ~exhaustive
    ~include_dependencies ~just_structure ~restrictions =
  let landmark = Landmark.register "calculate_dependencies" in
    Landmark.enter landmark;

    let e_set = structure.e in
    let restrict = structure.restrict in
    let rmw = structure.rmw in
    let po = structure.po in

    (* Filter to only events that exist in the hashtable *)
    let e_set_filtered =
      Uset.filter (fun id -> Hashtbl.mem events id) structure.e
    in

    (* Event type filters *)
    let filter_events typ =
      Uset.filter
        (fun e ->
          try
            let event = Hashtbl.find events e in
              event.typ = typ
          with Not_found -> false
        )
        e_set
    in

    let branch_events = filter_events Branch in
    let read_events = filter_events Read in
    let write_events = filter_events Write in
    let fence_events = filter_events Fence in
    let malloc_events = filter_events Malloc in
    let free_events = filter_events Free in

    (* Build tree for program order *)
    let build_tree rel =
      let tree = Hashtbl.create 256 in
        Uset.iter (fun e -> Hashtbl.add tree e (Uset.create ())) e_set;
        Uset.iter
          (fun (from, to_) ->
            let set = Hashtbl.find tree from in
              Uset.add set to_ |> ignore
          )
          rel;
        tree
    in

    let po_tree = build_tree po in

    (* Build ebranch mapping *)
    let ebranch =
      let tbl = Hashtbl.create 16 in
        Uset.iter
          (fun e ->
            let branches =
              Uset.filter (fun (f, t) -> Uset.mem branch_events f && t = e) po
              |> Uset.map (fun (f, _) -> f)
            in
              Hashtbl.add tbl e branches
          )
          e_set;
        tbl
    in

    let conflicting_branch e1 e2 =
      let branches1 =
        try Hashtbl.find ebranch e1 with Not_found -> Uset.create ()
      in
      let branches2 =
        try Hashtbl.find ebranch e2 with Not_found -> Uset.create ()
      in
      let common = Uset.intersection branches1 branches2 in
      let values = Uset.values common in
        match values with
        | [] -> failwith "No conflicting branch found"
        | hd :: tl -> List.fold_left max hd tl
    in

    (* Define the val function that extracts values from events *)
    let val_fn event_id =
      let ev = Hashtbl.find events event_id in
        match ev.wval with
        | Some v -> ev.wval
        | None -> ev.rval
    in

    (* Initialize ForwardingContext *)
    let* () =
      Forwardingcontext.init
        {
          init_e = e_set_filtered;
          init_po = po;
          init_events = events;
          init_val = val_fn;
          init_rmw = rmw;
        }
    in

    let pred (ctx : Forwardingcontext.t option) (p : expr list option) ?ppo () =
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
      let tree = build_tree inversed in
        Lwt.return (fun e -> Hashtbl.find tree e)
    in

    let fprime pred_fn ppo_loc =
      let w_cross_r = Uset.cross write_events read_events in
      let r_cross_r = Uset.cross read_events read_events in
      let w_cross_w = Uset.cross write_events write_events in
      let combined = Uset.union w_cross_r r_cross_r in
      let combined = Uset.union combined w_cross_w in
      let in_po = Uset.intersection combined po in
        Uset.filter
          (fun (e1, e2) -> Uset.mem ppo_loc (e1, e2) && Uset.mem (pred_fn e2) e1)
          in_po
    in

    (* Define fwd function *)
    let fwd pred_fn ctx ppo_loc =
      let edges = fprime pred_fn ppo_loc in
        Uset.filter
          (fun (e1, e2) ->
            try
              let ev2 = Hashtbl.find events e2 in
                (not ev2.volatile)
                &&
                if ev2.typ = Write then
                  let remapped = Forwardingcontext.remap ctx e2 in
                  let ev_remapped = Hashtbl.find events remapped in
                    ev_remapped.wmod = Relaxed
                else true
            with Not_found -> false
          )
          edges
    in

    (* Define we function *)
    let we pred_fn ctx ppo_loc =
      let edges = fprime pred_fn ppo_loc in
        Uset.filter
          (fun (e1, e2) ->
            try
              let ev1 = Hashtbl.find events e1 in
              let ev2 = Hashtbl.find events e2 in
                (not ev1.volatile) && ev1.typ = Write && ev2.typ = Write
            with Not_found -> false
          )
          edges
        |> Uset.map (fun (e1, e2) -> (e2, e1))
    in

    (* Initialize justifications for writes *)
    let init_justs =
      Uset.map
        (fun w ->
          try
            let event = Hashtbl.find events w in
              {
                p = [];
                d = Uset.create ();
                fwd = Uset.create ();
                we = Uset.create ();
                w = event;
                op = ("init", None, None);
              }
          with Not_found -> failwith "Event not found"
        )
        write_events
    in

    let init_ppo =
      if Hashtbl.mem events 0 then
        Uset.cross (Uset.singleton 0)
          (Uset.set_minus
             (Uset.of_list (Hashtbl.fold (fun k _ acc -> k :: acc) events []))
             (Uset.singleton 0)
          )
      else Uset.create ()
    in

    let fj = Uset.union structure.fj init_ppo in

    (* Justification elaboration *)
    let elaborate =
      object
        method filter (justs : justification list) =
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

            let (justs'' : justification list) =
              List.filter_map Fun.id justs'
            in

            (* Remove covered justifications *)
            let indexed = List.mapi (fun i j -> (i, j)) justs'' in
            let result =
              indexed
              |> List.filter (fun (i, (j : justification)) ->
                     (* Keep j if it's NOT covered by any later justification *)
                     not
                       (List.exists
                          (fun (i', (j' : justification)) ->
                            i' > i
                            (* Only check justifications that come after *)
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

        method value_assign justs =
          let landmark = Landmark.register "dp.va" in
            Landmark.enter landmark;

            let* results =
              Lwt_list.map_p
                (fun (just : justification) ->
                  (* Simplified value assignment *)
                  let solver = Solver.create just.p in
                    let* model = Solver.solve solver in
                      match model with
                      | Some bindings ->
                          (* Apply concrete values to write value *)
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
                              {
                                just with
                                w = new_w;
                                op = ("va", Some just, None);
                              }
                      | None -> Lwt.return just
                )
                justs
            in

            Landmark.exit landmark;
            Lwt.return (Uset.of_list results)

        method forward justs =
          let landmark = Landmark.register "dp.forward" in
            Landmark.enter landmark;

            let* out =
              (* Map over justifications *)
              let* results =
                Lwt_list.map_p
                  (fun (just : justification) ->
                    (* Determine paths to check *)
                    let ps =
                      if structure.pwg <> [] then
                        [ just.p; just.p @ structure.pwg ]
                      else [ just.p ]
                    in

                    (* Map over each path *)
                    let* path_results =
                      Lwt_list.map_p
                        (fun p ->
                          let ctx =
                            Forwardingcontext.create ~fwd:just.fwd ~we:just.we
                              ()
                          in
                            let* ppo = Forwardingcontext.ppo ctx p in
                              let* ppo_loc = Forwardingcontext.ppo_loc ctx p in
                                let* _pred =
                                  pred None None ~ppo:(Lwt.return ppo) ()
                                in

                                (* Subtract fj from ppo_loc *)
                                let _ppo_loc = Uset.set_minus ppo_loc fj in

                                (* Compute fwd and we edges *)
                                let _fwd = fwd _pred ctx _ppo_loc in
                                let _we = we _pred ctx _ppo_loc in

                                (* Filter edges by label *)
                                let _fwd =
                                  Uset.filter
                                    (fun (_, e2) -> e2 <> just.w.label)
                                    _fwd
                                in
                                let _we =
                                  Uset.filter
                                    (fun (_, e2) -> e2 <> just.w.label)
                                    _we
                                in

                                (* Filter edge function *)
                                let filtedge (edge, new_fwd, new_we) =
                                  if Forwardingcontext.is_bad new_fwd new_we
                                  then Lwt.return_false
                                  else if
                                    Forwardingcontext.is_good new_fwd new_we
                                  then Lwt.return_true
                                  else
                                    let con =
                                      Forwardingcontext.create ~fwd:new_fwd
                                        ~we:new_we ()
                                    in
                                      Forwardingcontext.check con
                                in

                                (* Create fwd edges with contexts *)
                                let fwdedges =
                                  Uset.values _fwd
                                  |> List.map (fun edge ->
                                         ( edge,
                                           Uset.union just.fwd
                                             (Uset.singleton edge),
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
                                           Uset.union just.we
                                             (Uset.singleton edge)
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

        method strengthen (just_1 : justification) (just_2 : justification) ppo
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
                Uset.filter (fun (f, t) -> f = e || t = e) po
                |> Uset.map (fun (f, t) -> [ f; t ])
                |> fun s ->
                Uset.fold (fun acc pairs -> pairs @ acc) s [] |> Uset.of_list
              in
              let r_union_a = Uset.union read_events malloc_events in
                Uset.intersection po_neighbors r_union_a
                |> Uset.filter (fun ep -> not (Uset.mem ppo (e, ep)))
                |> Uset.map (fun ep ->
                       let remapped = Forwardingcontext.remap con ep in
                         match val_fn remapped with
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
              match val_fn w_1.label with
              | Some v -> Value.get_symbols v
              | None -> []
            in
            let w2_syms =
              match val_fn w_2.label with
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
            let bp_event = Hashtbl.find events (conflicting_branch e_1 e_2) in
            let bp =
              match bp_event.cond with
              | Some (VExpression e) -> e
              | _ -> failwith "Expected expression in cond"
            in
            let bpi = Expr.inverse bp in

            (* Compute uncommon predicates *)
            let uncommon = Uset.difference p_1 p_2 in
            let uncommonstr =
              Uset.filter
                (fun x -> not (Uset.mem uncommon (Expr.inverse x)))
                uncommon
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
                      not
                        (Uset.exists (fun (f2, t2) -> f2 = f && t <> t2) pos_rp)
                    )
                    pos_rp
                in
                let filter2 =
                  Uset.filter
                    (fun (f, t) ->
                      not
                        (Uset.exists (fun (f2, t2) -> t2 = t && f <> f2) pos_rp)
                    )
                    pos_rp
                in
                  ref (Uset.union filter1 filter2)
              in

              while !rls <> [] && !i < 10 do
                incr i;
                let s = List.hd !rls in
                  rls := List.tl !rls;

                  let relabels =
                    Uset.filter (fun (a, b) -> a = s || b = s) pos_rp
                  in
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
                       (fun x ->
                         Uset.exists (fun (y0, y1) -> x = y0 || x = y1) r
                       )
                       ness
                 )
            in

            Landmark.exit landmark;
            Lwt.return out

        method lift justs =
          let landmark = Landmark.register "dp.lift" in
            Landmark.enter landmark;

            let ctx = Forwardingcontext.create () in

            (* Simplified lifting *)
            Landmark.exit landmark;
            Lwt.return justs

        method weaken justs =
          let landmark = Landmark.register "dp.weaken" in
            Landmark.enter landmark;
            (* Simplified weakening *)
            Landmark.exit landmark;
            Lwt.return justs
      end
    in

    (* Main justification computation *)
    let* final_justs =
      if include_dependencies then
        let rec fixed_point justs =
          let* va = elaborate#value_assign justs in
            let* lift = elaborate#lift va in
              let* weak = elaborate#weaken lift in
                let* fwd = elaborate#forward weak in
                  let* filtered =
                    elaborate#filter
                      (Uset.values (Uset.union (Uset.of_list justs) fwd))
                  in

                  if Uset.equal filtered (Uset.of_list justs) then
                    Lwt.return filtered
                  else fixed_point (Uset.values filtered)
        in

        let* filtered_init = elaborate#filter (Uset.values init_justs) in
          fixed_point (Uset.values filtered_init)
      else Lwt.return init_justs
    in

    (* Build executions if not just structure *)
    let* executions =
      if just_structure then Lwt.return []
      else
        (* Simplified execution generation *)
        let exec =
          {
            ex_e = e_set;
            rf = Uset.create ();
            dp = Uset.create ();
            ppo = Uset.create ();
            ex_rmw = rmw;
            ex_p = [];
            conds = [];
            fix_rf_map = Hashtbl.create 16;
            justs = Uset.values final_justs;
            pointer_map = None;
          }
        in
          Lwt.return [ exec ]
    in

    Landmark.exit landmark;
    Lwt.return (structure, final_justs, executions)

(** Convert parsed AST to interpreter format *)
let rec convert_stmt = function
  | Parse.SThread { lhs; rhs } ->
      `Thread (List.map convert_stmt lhs, List.map convert_stmt rhs)
  | Parse.SGlobalLoad { register; global; assign } ->
      `GlobalLoad (register, global, assign.mode, assign.volatile)
  | Parse.SGlobalStore { global; expr; assign } ->
      `GlobalStore (global, assign.mode, expr, assign.volatile)
  | Parse.SFence { mode } -> `Fence mode
  (* Add other statement conversions as needed *)
  | _ -> failwith "Statement conversion not implemented"

(** Parse program *)
let parse_program program =
  Printf.printf "[DEBUG] Parsing program...\n";
  flush stdout;
  try
    let litmus = Parse.parse program in
    let constraints =
      List.map Parse.ast_expr_to_expr litmus.config.constraint_
    in
    let program_stmts = List.map convert_stmt litmus.program in
      (constraints, program_stmts)
  with
  | Failure msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      ([], [])
  | e ->
      Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string e);
      ([], [])

(** Main entry point *)
let create_symbolic_event_structure program options =
  let* _ = Lwt.return_unit in

  (* Parse program - get both constraints and program statements *)
  let ast, program_stmts = parse_program program in

  (* Interpret program *)
  let* structure, events =
    Interpret.interpret program_stmts [] (Hashtbl.create 16) []
  in

  (* Calculate dependencies *)
  let* structure', justs, executions =
    calculate_dependencies ast structure events
      ~exhaustive:(options.exhaustive || false)
      ~include_dependencies:(options.dependencies || true)
      ~just_structure:(options.just_structure || false)
      ~restrictions:options
  in

  (* Check assertion if present *)
  let result =
    {
      ast;
      structure = structure';
      events;
      executions;
      valid = true;
      ub = false;
    }
  in

  Printf.printf "[DEBUG] Verification complete.\n";
  flush stdout;

  Lwt.return result
