open Lwt.Syntax

module ListMapCombinationBuilder = struct
  let build_combinations (type a) (listmap : (int, a list) Hashtbl.t)
      (keys : int list)
      ?(check_partial_combo = fun _ ?alternatives:_ _ -> Lwt.return true)
      ?(check_final_combo = fun _ -> Lwt.return true) () =
    let rec combine_and_check combinations keys =
      match keys with
      | [] -> Lwt_list.filter_s check_final_combo combinations
      | key :: rest_keys ->
          let justs = try Hashtbl.find listmap key with Not_found -> [] in

          (* OPTIMIZATION 1: Process combinations in a streaming fashion *)
          (* Instead of collecting all new_combinations at once, process incrementally *)
          let* new_combinations =
            Lwt_list.fold_left_s
              (fun acc just ->
                (* OPTIMIZATION 2: Filter first, then extend *)
                let* filtered =
                  Lwt_list.filter_s
                    (fun combo ->
                      check_partial_combo combo ?alternatives:(Some justs)
                        (key, just)
                    )
                    combinations
                in
                (* OPTIMIZATION 3: Use cons (::) instead of append (@) *)
                (* Reverse the list once at the end instead of maintaining order *)
                let extended =
                  List.map (fun combo -> (key, just) :: combo) filtered
                in
                  (* OPTIMIZATION 4: Use rev_append for efficient concatenation *)
                  Lwt.return (List.rev_append extended acc)
              )
              [] justs
          in

          (* Note: Combinations are now in reverse order within each combo *)
          (* If order matters, reverse each combo at the end *)
          combine_and_check new_combinations rest_keys
    in

    let* result = combine_and_check [ [] ] keys in
      (* OPTIMIZATION 5: Reverse each combination to restore original order *)
      Lwt.return (List.map List.rev result)
end

(** Generate all permutations of a list *)
let rec permutations = function
  | [] -> [ [] ]
  | x :: xs ->
      let perms = permutations xs in
        List.concat
          (List.map
             (fun perm ->
               let rec insert_at_all_positions acc = function
                 | [] -> [ List.rev (x :: acc) ]
                 | y :: ys as rest ->
                     (List.rev acc @ (x :: rest))
                     :: insert_at_all_positions (y :: acc) ys
               in
                 insert_at_all_positions [] perm
             )
             perms
          )
