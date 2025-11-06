open Ir

let all_loops_episodic (ast : ir_stmt list) : bool =
  let rec check_stmt (stmt : ir_stmt) =
    match stmt with
    | While { body; _ } | Do { body; _ } -> is_episodic_loop body
    | Threads { threads } ->
        List.for_all (fun thread -> List.for_all check_stmt thread) threads
    | _ -> true
  and is_episodic_loop (body : ir_stmt list) =
    List.for_all
      (fun stmt ->
        match stmt with
        | GlobalStore _ | GlobalLoad _ -> true
        | Threads { threads } ->
            List.for_all (fun thread -> List.for_all check_stmt thread) threads
        | _ -> false
      )
      body
  in
    List.for_all check_stmt ast
