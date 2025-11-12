(** Mordor - Main dependency calculation algorithm *)

open Context
open Events
open Executions
open Expr
open Lwt.Syntax
open Types
open Uset

(** Calculate dependencies and justifications *)

let calculate_dependencies ast (structure : symbolic_event_structure)
    (events : (int, event) Hashtbl.t) ~exhaustive ~include_dependencies
    ~restrictions =
  let e_set = structure.e in
  let restrict = structure.restrict in
  let rmw = structure.rmw in
  let po = structure.po in

  let branch_events = filter_events events e_set Branch in
  let read_events = filter_events events e_set Read in
  let write_events = filter_events events e_set Write in
  let fence_events = filter_events events e_set Fence in
  let malloc_events = filter_events events e_set Malloc in
  let free_events = filter_events events e_set Free in

  (* Build tree for program order *)
  let build_tree rel =
    let tree = Hashtbl.create 256 in
      USet.iter (fun e -> Hashtbl.add tree e (USet.create ())) e_set;
      USet.iter
        (fun (from, to_) ->
          let set = Hashtbl.find tree from in
            USet.add set to_ |> ignore
        )
        rel;
      tree
  in

  Logs.debug (fun m -> m "Building PO tree...");

  let po_tree = build_tree po in

  Logs.debug (fun m -> m "PO tree built");

  (* Build ebranch mapping *)
  let ebranch =
    let tbl = Hashtbl.create 16 in
      USet.iter
        (fun e ->
          let branches =
            USet.filter (fun (f, t) -> USet.mem branch_events f && t = e) po
            |> USet.map (fun (f, _) -> f)
          in
            Hashtbl.add tbl e branches
        )
        e_set;
      tbl
  in

  let conflicting_branch e1 e2 =
    let branches1 =
      try Hashtbl.find ebranch e1 with Not_found -> USet.create ()
    in
    let branches2 =
      try Hashtbl.find ebranch e2 with Not_found -> USet.create ()
    in
    let common = USet.intersection branches1 branches2 in
    let values = USet.values common in
      match values with
      | [] -> failwith "No conflicting branch found"
      | hd :: tl -> List.fold_left max hd tl
  in

  (* Define the val function that extracts values from events *)
  let val_fn event_id =
    let ev = Hashtbl.find events event_id in
      match ev.wval with
      | Some v -> ev.wval
      | None -> (
          match ev.rval with
          | Some v -> Some (Expr.of_value v)
          | None -> None
        )
  in

  (* Initialize ForwardingContext *)
  let* () =
    Forwardingcontext.init
      {
        init_e = e_set;
        init_po = po;
        init_events = events;
        init_val = val_fn;
        init_rmw = rmw;
      }
  in

  (* Initialize justifications for writes *)
  let pre_justs = Elaborations.pre_justifications structure events e_set in

  Logs.debug (fun m ->
      m "Pre-justifications for event\n\t%s"
        (String.concat "\n\t"
           (List.map Justifications.to_string (USet.values pre_justs))
        )
  );

  (* Initialize initial PPO relation *)
  let init_ppo =
    if Hashtbl.mem events 0 then
      URelation.cross (USet.singleton 0)
        (USet.set_minus
           (USet.of_list (Hashtbl.fold (fun k _ acc -> k :: acc) events []))
           (USet.singleton 0)
        )
    else USet.create ()
  in

  let fj = USet.union structure.fj init_ppo in

  (* Build context for elaborations *)
  let elab_ctx =
    {
      Elaborations.structure;
      events;
      e_set;
      branch_events;
      read_events;
      write_events;
      malloc_events;
      po;
      rmw;
      fj;
      val_fn;
      conflicting_branch;
    }
  in

  Logs.debug (fun m -> m "Starting elaborations...");

  let* final_justs =
    if include_dependencies then
      let rec fixed_point (justs : justification uset) =
        Logs.debug (fun m ->
            m "Fixed-point iteration with %d justifications" (USet.size justs)
        );
        let* va = Elaborations.value_assign elab_ctx justs in
          let* lift = Elaborations.lift elab_ctx va in
            let* weak = Elaborations.weaken elab_ctx lift in
              let* fwd = Elaborations.forward elab_ctx weak in
                let* filtered =
                  Elaborations.filter elab_ctx (USet.union justs fwd)
                in

                let justs_str =
                  String.concat "\n\t"
                    (USet.values (USet.map Justifications.to_string filtered))
                in
                  if USet.equal filtered justs then (
                    Logs.debug (fun m ->
                        m "Fixed-point reached with %d justifications:\n\t%s"
                          (USet.size filtered) justs_str
                    );
                    Lwt.return filtered
                  )
                  else (
                    Logs.debug (fun m ->
                        m "Continue elaborating with %d justifications:\n\t%s"
                          (USet.size filtered) justs_str
                    );
                    fixed_point filtered
                  )
      in

      let* filtered_init = Elaborations.filter elab_ctx pre_justs in
        fixed_point filtered_init
    else Lwt.return pre_justs
  in

  Logs.debug (fun m ->
      m "Elaborations complete. Final justifications count: %d"
        (USet.size final_justs)
  );

  Logs.debug (fun m -> m "Generating executions...");

  (* Build executions if not just structure *)
  let* executions =
    generate_executions events structure final_justs structure.constraint_
      init_ppo ~include_dependencies ~restrictions
  in

  Logs.debug (fun m -> m "Executions generated: %d" (List.length executions));

  Lwt.return (structure, final_justs, executions)

let step_calculate_dependencies (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t
    =
  let* ctx = lwt_ctx in

  (* Create restrictions for coherence checking *)
  let coherence_restrictions =
    {
      Coherence.coherent =
        ( try ctx.options.coherent with _ -> "imm"
        )
        (* default to IMM if not specified *);
    }
  in
    match
      (ctx.program_stmts, ctx.litmus_constraints, ctx.structure, ctx.events)
    with
    | Some stmts, Some constraints, Some structure, Some events ->
        let* structure, justs, executions =
          calculate_dependencies constraints structure events
            ~exhaustive:(ctx.options.exhaustive || false)
            ~include_dependencies:(ctx.options.dependencies || true)
            ~restrictions:coherence_restrictions
        in
          ctx.structure <- Some structure;
          ctx.justifications <- Some justs;
          ctx.executions <- Some (USet.of_list executions);
          Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "Program statements or litmus constraints not available."
        );
        Lwt.return ctx
