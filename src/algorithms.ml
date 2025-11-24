open Lwt.Syntax

module ListMapCombinationBuilder = struct
  let build_combinations (type a) (listmap : (int, a list) Hashtbl.t)
      (keys : int list) (check_partial_combo : a list -> a -> bool Lwt.t)
      (check_final_combo : a list -> bool Lwt.t) =
    let rec combine_and_check combinations keys =
      match keys with
      | [] -> Lwt_list.filter_p check_final_combo combinations
      | key :: rest_keys ->
          Logs.debug (fun m -> m "Combining with key %d" key);
          let justs = try Hashtbl.find listmap key with Not_found -> [] in
            let* new_combinations =
              let* lists =
                Lwt_list.map_s
                  (fun just ->
                    let* filtered =
                      Lwt_list.filter_p
                        (fun combo -> check_partial_combo combo just)
                        combinations
                    in
                      Lwt_list.map_s
                        (fun combo -> Lwt.return (combo @ [ just ]))
                        filtered
                  )
                  justs
              in
                Lwt_list.fold_left_s
                  (fun acc lst -> Lwt.return (acc @ lst))
                  [] lists
            in
              Logs.debug (fun m ->
                  m "Processed key %d: %d combinations before, %d after" key
                    (List.length combinations)
                    (List.length new_combinations)
              );
              combine_and_check new_combinations rest_keys
    in
      combine_and_check [ [] ] keys
end
