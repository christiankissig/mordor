open Context
open Lwt.Syntax
open Types
open Uset

(* Compute the future set for a given set of executions, where a future is the
   projection of the execution to ppo and dp relation plus identity on events.
   *)
let calculate_future_set (execs : symbolic_execution uset) : future_set =
  USet.map
    (fun exec ->
      USet.union
        (URelation.identity_relation exec.ex_e)
        (USet.intersection
           (USet.union exec.dp exec.ppo)
           (URelation.cross exec.ex_e exec.ex_e)
        )
    )
    execs

(* Compute all histories of a symbolic execution.
   A history is a subset of ex_e that is downward closed with respect to ppo,
   dp, and rf. That is, if e2 is in a history H, then every e1 with (e1,e2) in
   ppo, dp, or rf must also be in H. *)
let calculate_histories (exec : symbolic_execution) : int USet.t USet.t =
  let all_events = exec.ex_e in
  let ppo = exec.ppo in
  let dp = exec.dp in
  let rf = exec.rf in

  (* Get all immediate predecessors of an event e
     (events e1 where (e1, e) is in ppo, dp, or rf) *)
  let get_predecessors e =
    let pred_set = USet.create () in
    let add_if_predecessor (e1, e2) =
      if e2 = e then ignore (USet.add pred_set e1)
    in
      USet.iter add_if_predecessor ppo;
      USet.iter add_if_predecessor dp;
      USet.iter add_if_predecessor rf;
      pred_set
  in

  (* Check if event e can be added to history h
     (all its predecessors are already in h) *)
  let can_add_event h e =
    let preds = get_predecessors e in
      USet.for_all (fun p -> USet.mem h p) preds
  in

  (* Check if a history already exists in the set of histories *)
  let history_exists histories h =
    USet.exists (fun existing_h -> USet.equal existing_h h) histories
  in

  (* Generate all histories using breadth-first search *)
  let histories = USet.create () in
  let worklist = Queue.create () in

  (* Start with the empty history (always downward closed) *)
  let empty_hist = USet.create () in
    ignore (USet.add histories empty_hist);
    Queue.add empty_hist worklist;

    (* BFS: for each history, try extending it with each compatible event *)
    while not (Queue.is_empty worklist) do
      let current_hist = Queue.take worklist in

      (* Try to add each event that's not yet in the current history *)
      USet.iter
        (fun e ->
          if not (USet.mem current_hist e) then
            (* Check if all predecessors of e are in current_hist *)
            if can_add_event current_hist e then
              let new_hist = USet.add (USet.clone current_hist) e in
                (* Only add if this is a new history *)
                if not (history_exists histories new_hist) then (
                  ignore (USet.add histories new_hist);
                  Queue.add new_hist worklist
                )
        )
        all_events
    done;

    histories

(* Compute the posterior future for a given future and history.
   The posterior future contains all pairs (e1, e2) from the future
   where e1 does not occur in the history. *)
let posterior_future (future : future) (history : int USet.t) : future =
  USet.filter (fun (e1, _e2) -> not (USet.mem history e1)) future

(* Compute the posterior future set for a given future set and history.
   For each future in the future set, compute its posterior future
   with respect to the given history. *)
let posterior_future_set (future_set : future_set) (history : int USet.t) :
    future_set =
  USet.map (fun future -> posterior_future future history) future_set

(* Alternative implementation with explicit iteration for clarity *)
let posterior_future_explicit (future : future) (history : int USet.t) : future
    =
  let result = USet.create () in
    USet.iter
      (fun (e1, e2) ->
        if not (USet.mem history e1) then ignore (USet.add result (e1, e2))
      )
      future;
    result

let posterior_future_set_explicit (future_set : future_set)
    (history : int USet.t) : future_set =
  let result = USet.create () in
    USet.iter
      (fun future ->
        let post_future = posterior_future future history in
          ignore (USet.add result post_future)
      )
      future_set;
    result

let print_futures (lwt_ctx : mordor_ctx Lwt.t) =
  let* ctx = lwt_ctx in
  let name =
    match ctx.litmus_name with
    | Some n -> n
    | None -> "unknown_program"
  in
  let program =
    match ctx.litmus with
    | Some p -> p
    | None -> ""
  in

  Logs.info (fun m -> m "Computing futures for program %s." name);
  (* Generate output based on output mode *)
  match ctx.output_mode with
  | Json -> (
      let futures_json =
        (* Create JSON representation of futures *)
        let executions_json =
          match ctx.executions with
          | None -> "[]"
          | Some execs ->
              USet.values execs
              |> List.mapi (fun i _exec ->
                  Printf.sprintf
                    "    {\n\
                    \      \"execution\": %d,\n\
                    \      \"futures\": %s\n\
                    \    }"
                    i
                    ( match ctx.futures with
                    | None -> "[]"
                    | Some future_set ->
                        USet.values future_set
                        |> List.mapi (fun j _future ->
                            Printf.sprintf
                              "        {\n          \"future\": %s\n        }"
                              (USet.values _future
                              |> List.map (fun (e1, e2) ->
                                  Printf.sprintf "(%d, %d)" e1 e2
                              )
                              |> String.concat ", "
                              )
                        )
                        |> String.concat ",\n"
                    )
              )
              |> String.concat ",\n"
        in
          Printf.sprintf
            "{\n  \"program\": \"%s\",\n  \"executions\": [\n%s\n  ]\n}\n" name
            executions_json
      in
        match ctx.output_file with
        | "stdout" ->
            Printf.printf "Generated futures JSON file: %s\n" futures_json;
            flush stdout;
            Lwt.return ctx
        | _ ->
            let oc = open_out ctx.output_file in
              output_string oc futures_json;
              close_out oc;
              Printf.printf "Generated futures JSON file: %s\n" ctx.output_file;
              flush stdout;
              Lwt.return ctx
    )
  | _ ->
      Logs.err (fun m -> m "Unsupported output mode for futures.");
      Lwt.return ctx

let step_futures (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match ctx.executions with
    | Some execs ->
        Logs.debug (fun m -> m "Calculating futures...");
        let future_set = calculate_future_set execs in
          ctx.futures <- Some future_set;
          Logs.debug (fun m -> m "Futures calculated.");
          Lwt.return ctx
    | None ->
        Logs.err (fun m -> m "No executions available to calculate futures.");
        Lwt.return ctx
