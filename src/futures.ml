open Context
open Lwt.Syntax
open Types
open Uset

(* Compute the future set for a given set of executions, where a future is the
   projection of the execution to ppo and dp relation plus identity on events.

   rf is deliberately NOT one of the edge sources. A future is the INTRA-THREAD
   order a thread must execute its own statements in; the only inter-thread
   dependency of the model is reads-from, and it does not contribute to the
   future set (Wright et al. 2023, sec 6). Keeping rf out is what makes the
   futures split per thread, and hence what makes the Owicki-Gries
   decomposition of the future predicate sound. Cross-thread ordering -- a
   release/acquire handshake among it -- is carried by the memory semantics
   (timestamps and views), not by Phi. *)
let calculate_future_set (execs : symbolic_execution uset) : future_set =
  USet.map
    (fun exec ->
      USet.union
        (URelation.identity exec.e)
        (USet.intersection
           (USet.union exec.dp exec.ppo)
           (URelation.cross exec.e exec.e)
        )
    )
    execs

(* Compute all histories of a symbolic execution.
   A history is a subset of e that is downward closed with respect to ppo,
   dp, and rf. That is, if e2 is in a history H, then every e1 with (e1,e2) in
   ppo, dp, or rf must also be in H. *)
let calculate_histories (exec : symbolic_execution) : int USet.t USet.t =
  let all_events = exec.e in
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
  let name = ctx.litmus_name in
  let program =
    match ctx.litmus with
    | Some p -> p
    | None -> ""
  in

  Logs_safe.info (fun m -> m "Computing futures for program %s." name);
  (* Generate output based on output mode *)
  match ctx.output_mode with
  | Isa ->
      Isa_export.emit ctx;
      Lwt.return ctx
  | Json -> (
      let futures_json =
        (* Create JSON representation of futures *)
        let executions_json =
          Printf.sprintf "    {\n      \"futures\": [\n%s]\n    }"
            ( match ctx.futures with
            | None -> ""
            | Some future_set ->
                USet.values future_set
                |> List.mapi (fun j _future ->
                    Printf.sprintf "          [%s]"
                      (USet.values _future
                      |> List.map (fun (e1, e2) ->
                          Printf.sprintf "(%d, %d)" e1 e2
                      )
                      |> String.concat ", "
                      )
                )
                |> String.concat ",\n"
            )
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
      Logs_safe.err (fun m -> m "Unsupported output mode for futures.");
      Lwt.return ctx

(** S16 (how far executions collapse under a quotient, #93): with [MORDOR_S16]
    set, {!step_futures} reports how many classes the executions fall into under
    successively finer keys: the future; the final registers; the final memory
    (each location's co-last write); the value every read observes; the
    undefined behaviour. *)
module S16 = struct
  let enabled = Option.is_some (Sys.getenv_opt "MORDOR_S16")

  let report (structure : symbolic_event_structure)
      (execs : symbolic_execution list) =
    let sorted l = List.sort compare l in
    let resolve (ex : symbolic_execution) e =
      Expr.Expr.to_string
        (Expr.Expr.evaluate ~env:(Hashtbl.find_opt ex.fix_rf_map) e)
    in
    let future (ex : symbolic_execution) =
      let inside (a, b) = USet.mem ex.e a && USet.mem ex.e b in
        ( sorted (USet.values ex.e),
          sorted (List.filter inside (USet.values (USet.union ex.dp ex.ppo)))
        )
    in
    let registers ex =
      Hashtbl.fold (fun r e acc -> (r, resolve ex e) :: acc) ex.final_env []
      |> sorted
    in
    let memory (ex : symbolic_execution) =
      let co = Option.value ex.co ~default:(USet.create ()) in
      let writes =
        USet.values ex.e
        |> List.filter_map (fun l ->
            match Hashtbl.find_opt structure.events l with
            | Some ({ typ = Write; loc = Some loc; wval = Some v; _ } : event)
              -> Some (l, resolve ex loc, resolve ex v)
            | _ -> None
        )
      in
        List.filter
          (fun (w, loc, _) ->
            not
              (List.exists
                 (fun (w', loc', _) ->
                   w' <> w && loc' = loc && USet.mem co (w, w')
                 )
                 writes
              )
          )
          writes
        |> List.map (fun (_, loc, v) -> (loc, v))
        |> sorted
    in
    let reads ex =
      USet.values ex.rf
      |> List.filter_map (fun (_, r) ->
          Option.map (fun v -> (r, resolve ex v)) (Events.get_val structure r)
      )
      |> sorted
    in
    let ub ex =
      List.map
        (fun reason ->
          let pairs s =
            USet.values s
            |> sorted
            |> List.map (fun (a, b) -> Printf.sprintf "%d-%d" a b)
            |> String.concat " "
          in
            match reason with
            | UAF s -> "UAF " ^ pairs s
            | UPD s -> "UPD " ^ pairs s
        )
        (Assertion.ub_reasons structure ex)
      |> sorted
    in
    let rows =
      List.map
        (fun ex ->
          let f = future ex and g = registers ex and m = memory ex in
          let r = reads ex and u = ub ex in
            (f, g, m, r, u)
        )
        execs
    in
    let classes key =
      let t = Hashtbl.create 64 in
        List.iter (fun row -> Hashtbl.replace t (key row) ()) rows;
        Hashtbl.length t
    in
    let digest x = Digest.string (Marshal.to_string x []) in
    let per_future = Hashtbl.create 64 in
      List.iter
        (fun ((f, _, _, _, _) as row) ->
          let k = digest f in
            Hashtbl.replace per_future k
              (row
              :: (Hashtbl.find_opt per_future k |> Option.value ~default:[])
              )
        )
        rows;
      let within key =
        Hashtbl.fold
          (fun _ members acc ->
            let t = Hashtbl.create 8 in
              List.iter (fun row -> Hashtbl.replace t (key row) ()) members;
              max acc (Hashtbl.length t)
          )
          per_future 0
      in
      let largest =
        Hashtbl.fold (fun _ m acc -> max acc (List.length m)) per_future 0
      in
        Printf.eprintf
          "S16 executions=%d futures=%d outcomes=%d ub_kinds=%d \
           future+registers=%d +memory=%d +reads=%d +ub=%d largest_future=%d \
           within_future_max: registers+memory=%d +reads=%d +ub=%d\n\
           %!"
          (List.length rows)
          (classes (fun (f, _, _, _, _) -> digest f))
          (classes (fun (_, g, m, _, _) -> digest (g, m)))
          (classes (fun (_, _, _, _, u) -> digest u))
          (classes (fun (f, g, _, _, _) -> digest (f, g)))
          (classes (fun (f, g, m, _, _) -> digest (f, g, m)))
          (classes (fun (f, g, m, r, _) -> digest (f, g, m, r)))
          (classes (fun (f, g, m, r, u) -> digest (f, g, m, r, u)))
          largest
          (within (fun (_, g, m, _, _) -> digest (g, m)))
          (within (fun (_, g, m, r, _) -> digest (g, m, r)))
          (within (fun (_, g, m, r, u) -> digest (g, m, r, u)));
        (* The outcomes themselves, for reading. *)
        if Option.is_some (Sys.getenv_opt "MORDOR_S16_SHOW") then (
          let t = Hashtbl.create 16 in
            List.iter
              (fun (_, g, m, _, u) ->
                let k = (g, m, u) in
                  Hashtbl.replace t k
                    (1 + (Hashtbl.find_opt t k |> Option.value ~default:0))
              )
              rows;
            Hashtbl.iter
              (fun (g, m, u) n ->
                Printf.eprintf
                  "S16 outcome n=%d registers=%s memory=%s ub=%s\n%!" n
                  (String.concat "," (List.map (fun (r, v) -> r ^ "=" ^ v) g))
                  (String.concat "," (List.map (fun (l, v) -> l ^ "=" ^ v) m))
                  (String.concat ";" u)
              )
              t
        )
end

let step_futures (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    Progress.stage ~unit:"" "futures" @@ fun () ->
    match ctx.executions with
    | Some execs ->
        Logs_safe.debug (fun m -> m "Calculating futures...");
        if S16.enabled then
          Option.iter
            (fun structure -> S16.report structure (USet.values execs))
            ctx.structure;
        let future_set = calculate_future_set execs in
          ctx.futures <- Some future_set;
          Logs_safe.debug (fun m -> m "Futures calculated.");
          Lwt.return ctx
    | None ->
        Logs_safe.err (fun m ->
            m "No executions available to calculate futures."
        );
        Lwt.return ctx
