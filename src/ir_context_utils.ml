open Context
open Types

(** Extract all loop IDs from the program IR by recursively traversing nodes *)
let rec collect_loop_ids_and_spans_from_node (node : ir_node) :
    (int * source_span option) list =
  (* Get current loop ID from annotations if present *)
  let current_ids =
    match node.stmt with
    | While _ | Do _ -> (
        match (node.annotations.loop_ctx, node.annotations.source_span) with
        | Some loop_ctx, source_span -> [ (loop_ctx.lid, source_span) ]
        | None, _ -> []
      )
    | _ -> []
  in
  (* Recursively collect from nested statements *)
  let nested_ids = collect_loop_ids_and_spans_from_stmt node.stmt in
    current_ids @ nested_ids

and collect_loop_ids_and_spans_from_stmt (stmt : ir_stmt) :
    (int * source_span option) list =
  match stmt with
  | Threads { threads } ->
      (* Traverse all threads *)
      List.concat_map
        (fun thread ->
          List.concat_map collect_loop_ids_and_spans_from_node thread
        )
        threads
  | While { body; _ } | Do { body; _ } ->
      (* Traverse loop bodies *)
      List.concat_map collect_loop_ids_and_spans_from_node body
  | If { then_body; else_body; _ } ->
      (* Traverse if branches *)
      let then_ids =
        List.concat_map collect_loop_ids_and_spans_from_node then_body
      in
      let else_ids =
        match else_body with
        | Some else_stmts ->
            List.concat_map collect_loop_ids_and_spans_from_node else_stmts
        | None -> []
      in
        then_ids @ else_ids
  | Labeled { stmt; _ } ->
      (* Traverse labeled statement *)
      collect_loop_ids_and_spans_from_node stmt
  | _ -> []

(** Collect all unique loop IDs from the program *)
let collect_loop_ids_and_spans (program : ir_node list) :
    (int * source_span option) list =
  List.concat_map collect_loop_ids_and_spans_from_node program
  |> List.sort_uniq (fun (id1, _) (id2, _) -> compare id1 id2)

let collect_loop_ids_from_node (node : ir_node) : int list =
  collect_loop_ids_and_spans_from_node node |> List.map fst

let collect_loop_ids (program : ir_node list) : int list =
  collect_loop_ids_and_spans program |> List.map fst

(** Check if a node belongs to a specific loop *)
let node_in_loop (node : ir_node) (loop_id : int) : bool =
  match node.annotations.loop_ctx with
  | Some loop_ctx -> loop_ctx.lid = loop_id
  | None -> false

(** Find all nodes that belong to a specific loop *)
let rec find_loop_nodes (program : ir_node list) (loop_id : int) : ir_node list
    =
  List.concat_map (find_loop_nodes_in_node loop_id) program

and find_loop_nodes_in_node (loop_id : int) (node : ir_node) : ir_node list =
  let current_match = if node_in_loop node loop_id then [ node ] else [] in
  let nested_matches = find_loop_nodes_in_stmt loop_id node.stmt in
    current_match @ nested_matches

and find_loop_nodes_in_stmt (loop_id : int) (stmt : ir_stmt) : ir_node list =
  match stmt with
  | Threads { threads } ->
      List.concat_map (fun thread -> find_loop_nodes thread loop_id) threads
  | While { body; _ } | Do { body; _ } -> find_loop_nodes body loop_id
  | If { then_body; else_body; _ } ->
      let then_nodes = find_loop_nodes then_body loop_id in
      let else_nodes =
        match else_body with
        | Some else_stmts -> find_loop_nodes else_stmts loop_id
        | None -> []
      in
        then_nodes @ else_nodes
  | Labeled { stmt; _ } -> find_loop_nodes_in_node loop_id stmt
  | _ -> []

(** Get the iteration number for an event in a specific loop *)
let get_iteration_for_loop (loop_indices : (int, int list) Hashtbl.t)
    (event_label : int) (loop_lid : int) : int option =
  match Hashtbl.find_opt loop_indices event_label with
  | Some iterations ->
      (* The iterations list corresponds to nested loop iterations
         We need to determine which index corresponds to loop_lid
         For now, we take the last element as the innermost loop iteration *)
      if List.length iterations > 0 then
        Some (List.nth iterations (List.length iterations - 1))
      else None
  | None -> None
