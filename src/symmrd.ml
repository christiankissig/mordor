(** Mordor - Main dependency calculation algorithm *)

open Context
open Elaborations
open Executions
open Expr
open Justifications
open Lwt.Syntax
open Types
open Uset

(** Calculate dependencies and justifications *)

let calculate_dependencies ?(include_rf = true)
    (structure : symbolic_event_structure) ~exhaustive ~restrictions =
  let e_set = structure.e in
  let events = structure.events in
  let restrict = structure.restrict in
  let po = structure.po in

  let read_events = structure.read_events in
  let write_events = structure.write_events in
  let rlx_read_events = structure.rlx_read_events in
  let rlx_write_events = structure.rlx_write_events in
  let fence_events = structure.fence_events in
  let malloc_events = structure.malloc_events in
  let free_events = structure.free_events in

  (* Initialize ForwardingContext *)
  let* () =
    Forwardingcontext.init
      { init_structure = structure; init_val = Events.get_val structure }
  in

  (* Initialize justifications for writes *)
  let pre_justs = Elaborations.pre_justifications structure in

  Logs.debug (fun m ->
      m "Pre-justifications for event\n\t%s"
        (String.concat "\n\t"
           (List.map Justification.to_string (USet.values pre_justs))
        )
  );

  (* Initialize initial PPO relation - relates all initial events and terminal
     events to other events along po-edges. *)
  let init_ppo =
    if Hashtbl.mem events 0 then USet.filter (fun (f, t) -> f <> t && f = 0) po
    else USet.create ()
  in
  let terminal_events =
    Hashtbl.fold
      (fun lbl ev acc -> if ev.typ = Terminal then USet.add acc lbl else acc)
      structure.events (USet.create ())
  in
  let terminal_ppo =
    USet.filter (fun (f, t) -> f <> t && USet.mem terminal_events t) po
  in
  (* TODO discern in subsequent computation *)
  let init_ppo = USet.union init_ppo terminal_ppo in

  let fj = USet.union structure.fj init_ppo in

  (* Build context for elaborations *)
  let elab_ctx : Elaborations.context =
    {
      structure;
      fj;
      value_assign_seen = JustificationCache.create 1000;
      lifted_seen = JustificationPairCache.create 1000000;
      forwarding_seen = JustificationCache.create 1000;
      weaken_seen = JustificationCache.create 1000;
      filter_seen = JustificationPairCache.create 1000;
    }
  in

  Logs.debug (fun m -> m "Starting elaborations...");

  let justification_set_equal s1 s2 =
    USet.size s1 = USet.size s2
    && USet.for_all
         (fun j1 -> USet.exists (fun j2 -> Justification.equal j1 j2) s2)
         s1
  in

  let* final_justs = Elaborations.chain_elaborations elab_ctx pre_justs in

  Logs.debug (fun m ->
      m "Elaborations complete. Final justifications count: %d"
        (USet.size final_justs)
  );

  Logs.debug (fun m -> m "Generating executions...");

  (* Compute statex: allocation disjointness constraints *)

  (* 1. Extract static/global locations from all events *)
  let static_locs =
    USet.values e_set
    |> List.filter_map (fun eid ->
        match Hashtbl.find_opt events eid with
        | Some evt -> (
            (* Get location from event if it exists and is a variable *)
            match Events.get_loc structure eid with
            | Some loc when Expr.is_var loc -> Some loc
            | _ -> None
          )
        | None -> None
    )
    |> List.sort_uniq compare (* Remove duplicates *)
  in

  (* 2. Extract malloc locations *)
  (* TODO these constraints do not account for intermediate deallocation:

    • enforces the disjointness of symbolic memory locations introduced by
    consecutive allocation events, i.e. without an intermediate deallocation
    event.
    *)
  let malloc_locs =
    USet.values malloc_events
    |> List.filter_map (fun eid ->
        match Hashtbl.find_opt events eid with
        | Some evt -> Option.map Expr.of_value evt.rval
        | None -> None
    )
  in

  (* 3. Combine both sets *)
  let all_locs = static_locs @ malloc_locs in

  (* 4. Create pairwise disjointness for ALL distinct locations *)
  let statex =
    let pairs = ref [] in
      for i = 0 to List.length all_locs - 1 do
        for j = i + 1 to List.length all_locs - 1 do
          let loc1 = List.nth all_locs i in
          let loc2 = List.nth all_locs j in
            pairs := Expr.binop loc1 "!=" loc2 :: !pairs
        done
      done;
      !pairs @ structure.constraints
  in

  (* Build executions if not just structure *)
  let* executions =
    generate_executions ~include_rf structure final_justs statex init_ppo
      ~restrictions
  in

  Logs.debug (fun m -> m "Executions generated: %d" (List.length executions));

  Lwt.return (final_justs, executions)

let step_calculate_dependencies (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t
    =
  let* ctx = lwt_ctx in

  (* Create restrictions for coherence checking *)
  Logs.debug (fun m ->
      m "Setting up coherence restrictions...%s" ctx.options.coherent
  );
  let coherence_restrictions =
    {
      Coherence.coherent =
        ( try ctx.options.coherent with _ -> "imm"
        )
        (* default to IMM if not specified *);
    }
  in
    match ctx.structure with
    | Some structure ->
        let* justs, executions =
          calculate_dependencies structure
            ~exhaustive:(ctx.options.exhaustive || false)
            ~restrictions:coherence_restrictions
        in
          ctx.justifications <- Some justs;
          ctx.executions <- Some (USet.of_list executions);
          Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "Program statements or litmus constraints not available."
        );
        Lwt.return ctx
