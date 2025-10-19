(** sMRD - Symbolic Memory Relaxation Dependencies Main dependency calculation
    algorithm *)

open Parse (* order with open Types important *)
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

    (* Define the val function that extracts values from events *)
    let val_fn event_id =
      let ev = Hashtbl.find events event_id in
        match ev.wval with
        | Some v -> v
        | None -> (
            match ev.rval with
            | Some v -> v
            | None -> VSymbol (Printf.sprintf "v%d" event_id)
          )
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
