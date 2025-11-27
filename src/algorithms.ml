open Lwt.Syntax

module ListMapCombinationBuilder = struct
  (* OPTIMIZED VERSION - Addresses memory issues *)

  let build_combinations (type a) (listmap : (int, a list) Hashtbl.t)
      (keys : int list) (check_partial_combo : a list -> a -> bool Lwt.t)
      (check_final_combo : a list -> bool Lwt.t) =
    let rec combine_and_check combinations keys =
      match keys with
      | [] -> Lwt_list.filter_p check_final_combo combinations
      | key :: rest_keys ->
          let justs = try Hashtbl.find listmap key with Not_found -> [] in

          (* OPTIMIZATION 1: Process combinations in a streaming fashion *)
          (* Instead of collecting all new_combinations at once, process incrementally *)
          let* new_combinations =
            Lwt_list.fold_left_s
              (fun acc just ->
                (* OPTIMIZATION 2: Filter first, then extend *)
                let* filtered =
                  Lwt_list.filter_p
                    (fun combo -> check_partial_combo combo just)
                    combinations
                in
                (* OPTIMIZATION 3: Use cons (::) instead of append (@) *)
                (* Reverse the list once at the end instead of maintaining order *)
                let extended = List.map (fun combo -> just :: combo) filtered in
                  (* OPTIMIZATION 4: Use rev_append for efficient concatenation *)
                  Lwt.return (List.rev_append extended acc)
              )
              [] justs
          in

          Logs.debug (fun m ->
              m "After processing key %d, have %d combinations" key
                (List.length new_combinations)
          );

          (* Note: Combinations are now in reverse order within each combo *)
          (* If order matters, reverse each combo at the end *)
          combine_and_check new_combinations rest_keys
    in

    let* result = combine_and_check [ [] ] keys in
      (* OPTIMIZATION 5: Reverse each combination to restore original order *)
      Lwt.return (List.map List.rev result)
end

(* ALTERNATIVE: Memory-bounded version with early pruning *)
module ListMapCombinationBuilderBounded = struct
  (* This version limits the number of active combinations to prevent unbounded growth *)

  let build_combinations_bounded (type a) (listmap : (int, a list) Hashtbl.t)
      (keys : int list) (check_partial_combo : a list -> a -> bool Lwt.t)
      (check_final_combo : a list -> bool Lwt.t) ~max_combinations =
    let rec combine_and_check combinations keys =
      match keys with
      | [] -> Lwt_list.filter_p check_final_combo combinations
      | key :: rest_keys ->
          let justs = try Hashtbl.find listmap key with Not_found -> [] in

          let* new_combinations =
            Lwt_list.fold_left_s
              (fun acc just ->
                if List.length acc >= max_combinations then (
                  Logs.warn (fun m ->
                      m "Reached maximum combinations limit (%d), pruning..."
                        max_combinations
                  );
                  Lwt.return acc
                )
                else
                  let* filtered =
                    Lwt_list.filter_p
                      (fun combo -> check_partial_combo combo just)
                      combinations
                  in
                  let extended =
                    List.map (fun combo -> just :: combo) filtered
                  in
                    Lwt.return (List.rev_append extended acc)
              )
              [] justs
          in

          (* OPTIMIZATION 6: Apply final check early if combinations grow too large *)
          let* pruned =
            if List.length new_combinations > max_combinations then (
              Logs.warn (fun m ->
                  m "Pruning %d combinations down to %d using final check"
                    (List.length new_combinations)
                    max_combinations
              );
              let* validated =
                Lwt_list.filter_p check_final_combo new_combinations
              in
                (* Take only the first max_combinations after validation *)
                Lwt.return
                  (List.filteri (fun i _ -> i < max_combinations) validated)
            )
            else Lwt.return new_combinations
          in

          Logs.debug (fun m ->
              m "After processing key %d, have %d combinations (pruned from %d)"
                key (List.length pruned)
                (List.length new_combinations)
          );

          combine_and_check pruned rest_keys
    in

    let* result = combine_and_check [ [] ] keys in
      Lwt.return (List.map List.rev result)
end

(* ALTERNATIVE: Batched processing to allow GC *)
module ListMapCombinationBuilderBatched = struct
  (* Process combinations in batches to allow garbage collection *)

  let build_combinations_batched (type a) (listmap : (int, a list) Hashtbl.t)
      (keys : int list) (check_partial_combo : a list -> a -> bool Lwt.t)
      (check_final_combo : a list -> bool Lwt.t) ~batch_size =
    let rec combine_and_check_batched combinations keys =
      match keys with
      | [] -> Lwt_list.filter_p check_final_combo combinations
      | key :: rest_keys ->
          let justs = try Hashtbl.find listmap key with Not_found -> [] in

          (* OPTIMIZATION 7: Process combinations in batches *)
          let rec process_batches combo_batches acc =
            match combo_batches with
            | [] -> Lwt.return acc
            | batch :: remaining_batches ->
                let* batch_results =
                  Lwt_list.fold_left_s
                    (fun batch_acc just ->
                      let* filtered =
                        Lwt_list.filter_p
                          (fun combo -> check_partial_combo combo just)
                          batch
                      in
                      let extended =
                        List.map (fun combo -> just :: combo) filtered
                      in
                        Lwt.return (List.rev_append extended batch_acc)
                    )
                    [] justs
                in
                  (* Force a yield point to allow GC *)
                  let* () = Lwt.pause () in
                    process_batches remaining_batches
                      (List.rev_append batch_results acc)
          in

          (* Split combinations into batches *)
          let rec split_into_batches lst batches current_batch count =
            match lst with
            | [] ->
                if current_batch = [] then List.rev batches
                else List.rev (List.rev current_batch :: batches)
            | x :: xs ->
                if count >= batch_size then
                  split_into_batches xs
                    (List.rev current_batch :: batches)
                    [ x ] 1
                else
                  split_into_batches xs batches (x :: current_batch) (count + 1)
          in

          let batches = split_into_batches combinations [] [] 0 in

          Logs.debug (fun m ->
              m "Processing %d combinations in %d batches for key %d"
                (List.length combinations) (List.length batches) key
          );

          let* new_combinations = process_batches batches [] in

          Logs.debug (fun m ->
              m "After processing key %d, have %d combinations" key
                (List.length new_combinations)
          );

          combine_and_check_batched new_combinations rest_keys
    in

    let* result = combine_and_check_batched [ [] ] keys in
      Lwt.return (List.map List.rev result)
end
