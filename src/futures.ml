open Types

(* Compute the future set for a given set of executions, where a future is the
   projection of the execution to ppo and dp relation plus identity on events.
   *)
let calculate_future_set (execs : symbolic_execution uset) : future_set =
  Uset.map
    (fun exec ->
      Uset.union
        (Uset.identity_relation exec.ex_e)
        (Uset.intersection
           (Uset.union exec.dp exec.ppo)
           (Uset.cross exec.ex_e exec.ex_e)
        )
    )
    execs

(* Compute all histories of a symbolic execution.
   A history is a subset of ex_e that is downward closed with respect to ppo,
   dp, and rf. That is, if e2 is in a history H, then every e1 with (e1,e2) in
   ppo, dp, or rf must also be in H. *)
let calculate_histories (exec : symbolic_execution) : int Uset.t Uset.t =
  let all_events = exec.ex_e in
  let ppo = exec.ppo in
  let dp = exec.dp in
  let rf = exec.rf in

  (* Get all immediate predecessors of an event e
     (events e1 where (e1, e) is in ppo, dp, or rf) *)
  let get_predecessors e =
    let pred_set = Uset.create () in
    let add_if_predecessor (e1, e2) =
      if e2 = e then ignore (Uset.add pred_set e1)
    in
      Uset.iter add_if_predecessor ppo;
      Uset.iter add_if_predecessor dp;
      Uset.iter add_if_predecessor rf;
      pred_set
  in

  (* Check if event e can be added to history h
     (all its predecessors are already in h) *)
  let can_add_event h e =
    let preds = get_predecessors e in
      Uset.for_all (fun p -> Uset.mem h p) preds
  in

  (* Check if a history already exists in the set of histories *)
  let history_exists histories h =
    Uset.exists (fun existing_h -> Uset.equal existing_h h) histories
  in

  (* Generate all histories using breadth-first search *)
  let histories = Uset.create () in
  let worklist = Queue.create () in

  (* Start with the empty history (always downward closed) *)
  let empty_hist = Uset.create () in
    ignore (Uset.add histories empty_hist);
    Queue.add empty_hist worklist;

    (* BFS: for each history, try extending it with each compatible event *)
    while not (Queue.is_empty worklist) do
      let current_hist = Queue.take worklist in

      (* Try to add each event that's not yet in the current history *)
      Uset.iter
        (fun e ->
          if not (Uset.mem current_hist e) then
            (* Check if all predecessors of e are in current_hist *)
            if can_add_event current_hist e then
              let new_hist = Uset.add (Uset.clone current_hist) e in
                (* Only add if this is a new history *)
                if not (history_exists histories new_hist) then (
                  ignore (Uset.add histories new_hist);
                  Queue.add new_hist worklist
                )
        )
        all_events
    done;

    histories

(* Compute the posterior future for a given future and history.
   The posterior future contains all pairs (e1, e2) from the future
   where e1 does not occur in the history. *)
let posterior_future (future : future) (history : int Uset.t) : future =
  Uset.filter (fun (e1, _e2) -> not (Uset.mem history e1)) future

(* Compute the posterior future set for a given future set and history.
   For each future in the future set, compute its posterior future
   with respect to the given history. *)
let posterior_future_set (future_set : future_set) (history : int Uset.t) :
    future_set =
  Uset.map (fun future -> posterior_future future history) future_set

(* Alternative implementation with explicit iteration for clarity *)
let posterior_future_explicit (future : future) (history : int Uset.t) : future
    =
  let result = Uset.create () in
    Uset.iter
      (fun (e1, e2) ->
        if not (Uset.mem history e1) then ignore (Uset.add result (e1, e2))
      )
      future;
    result

let posterior_future_set_explicit (future_set : future_set)
    (history : int Uset.t) : future_set =
  let result = Uset.create () in
    Uset.iter
      (fun future ->
        let post_future = posterior_future future history in
          ignore (Uset.add result post_future)
      )
      future_set;
    result
