(** Episodicity Analysis Module

    This module implements episodicity checks for loops based on Definition 4.1.
    A loop is episodic if it satisfies four conditions:
    1. Registers only accessed if written to ⊑-before within same iteration or before loop
    2. Reads must read from: (a) same-iteration writes, (b) cross-thread writes,
       or (c) read-don't-modify RMWs derived from such writes
    3. Branching conditions don't constrain symbols read before the loop
    4. Events from prior iterations are ordered before later iterations by (ppo ∪ dp)*

    Where:
    - ⊑ is sequenced-before (program order)
    - ⪯ is ppo (preserved program order)
    - dp is semantic dependency (from justification freezing)
*)

open Context
open Types
open Uset

(** Note: We work with ir_node (Context.ir_node) which is ir_node_ann Ir.ir_node
    The annotations contain loop_ctx, thread_ctx, etc. *)

(** {1 Types} *)

(** Result of episodicity check for a single condition *)
type condition_result = {
  satisfied : bool;
  violations : string list;
}

(** Complete episodicity analysis result for a loop *)
type loop_episodicity_result = {
  loop_id : int;
  condition1 : condition_result; (* Register access *)
  condition2 : condition_result; (* Memory read sources *)
  condition3 : condition_result; (* Branch conditions *)
  condition4 : condition_result; (* Inter-iteration ordering *)
  is_episodic : bool;
}

(** {1 Utilities} *)

(** Extract all loop IDs from the program IR by recursively traversing nodes *)
let rec collect_loop_ids_from_node (node : ir_node) : int list =
  (* Get current loop ID from annotations if present *)
  let current_ids =
    match node.annotations.loop_ctx with
    | Some loop_ctx -> [ loop_ctx.lid ]
    | None -> []
  in
  (* Recursively collect from nested statements *)
  let nested_ids = collect_loop_ids_from_stmt node.stmt in
  current_ids @ nested_ids

and collect_loop_ids_from_stmt (stmt : ir_stmt) : int list =
  match stmt with
  | Threads { threads } ->
      (* Traverse all threads *)
      List.concat_map
        (fun thread -> List.concat_map collect_loop_ids_from_node thread)
        threads
  | While { body; _ } | Do { body; _ } ->
      (* Traverse loop bodies *)
      List.concat_map collect_loop_ids_from_node body
  | If { then_body; else_body; _ } ->
      (* Traverse if branches *)
      let then_ids = List.concat_map collect_loop_ids_from_node then_body in
      let else_ids =
        match else_body with
        | Some else_stmts -> List.concat_map collect_loop_ids_from_node else_stmts
        | None -> []
      in
      then_ids @ else_ids
  | Labeled { stmt; _ } ->
      (* Traverse labeled statement *)
      collect_loop_ids_from_node stmt
  | RegisterStore _ | RegisterRefAssign _ | GlobalStore _ | GlobalLoad _
  | DerefStore _ | DerefLoad _ | Fence _ | Lock _ | Unlock _ | Free _
  | Cas _ | Fadd _ | RegMalloc _ | GlobalMalloc _ | Skip ->
      (* These statements don't contain nested nodes *)
      []

(** Collect all unique loop IDs from the program *)
let collect_loop_ids (program : ir_node list) : int list =
  List.concat_map collect_loop_ids_from_node program
  |> List.sort_uniq compare

(** Check if a node belongs to a specific loop *)
let node_in_loop (node : ir_node) (loop_id : int) : bool =
  match node.annotations.loop_ctx with
  | Some loop_ctx -> loop_ctx.lid = loop_id
  | None -> false

(** Find all nodes that belong to a specific loop *)
let rec find_loop_nodes (program : ir_node list) (loop_id : int) : ir_node list =
  List.concat_map (find_loop_nodes_in_node loop_id) program

and find_loop_nodes_in_node (loop_id : int) (node : ir_node) : ir_node list =
  let current_match = if node_in_loop node loop_id then [node] else [] in
  let nested_matches = find_loop_nodes_in_stmt loop_id node.stmt in
  current_match @ nested_matches

and find_loop_nodes_in_stmt (loop_id : int) (stmt : ir_stmt) : ir_node list =
  match stmt with
  | Threads { threads } ->
      List.concat_map
        (fun thread -> find_loop_nodes thread loop_id)
        threads
  | While { body; _ } | Do { body; _ } ->
      find_loop_nodes body loop_id
  | If { then_body; else_body; _ } ->
      let then_nodes = find_loop_nodes then_body loop_id in
      let else_nodes =
        match else_body with
        | Some else_stmts -> find_loop_nodes else_stmts loop_id
        | None -> []
      in
      then_nodes @ else_nodes
  | Labeled { stmt; _ } ->
      find_loop_nodes_in_node loop_id stmt
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
      else
        None
  | None -> None

(** {1 Condition 1: Register Access Restriction (Syntactic)} *)

(** Check if a register is written before it's read within a loop body *)
let check_register_accesses_in_loop (loop_body : ir_node list) : condition_result =
  (* TODO: Implement register dataflow analysis
     - Track which registers are written before each read
     - Ensure no reads of registers written in previous iterations
     - This requires traversing IR statements which we don't have direct access to
  *)
  { satisfied = true; violations = [] }

(** Condition 1: Registers only accessed if written to ⊑-before *)
let check_condition1_register_access (program : ir_node list) (loop_id : int)
    : condition_result =
  (* TODO:
     1. Find all nodes with annotations.loop_ctx.lid = loop_id
     2. Collect register reads and writes in program order
     3. Check that each read is preceded by a write in same iteration or before loop

     Note: This requires deep traversal of IR statements, which may need
     additional helper functions or access to the IR statement structure.
  *)
  { satisfied = true; violations = [] }

(** {1 Condition 2: Memory Read Sources (Semantic)} *)

(** Check if an event is a read-don't-modify RMW *)
let is_read_dont_modify_rmw (event : event) (structure : symbolic_event_structure)
    : bool =
  match event.typ with
  | RMW | CRMW ->
      (* TODO: Check if the read value equals the write value
         This requires comparing event.rval with event.wval
      *)
      false
  | _ -> false

(** Get the origin event for a symbol *)
let get_symbol_origin (structure : symbolic_event_structure) (symbol : string)
    : int option =
  Hashtbl.find_opt structure.origin symbol

(** Check if an event occurred before a loop started *)
let event_before_loop (loop_indices : (int, int list) Hashtbl.t)
    (event_label : int) (loop_lid : int) : bool =
  match Hashtbl.find_opt loop_indices event_label with
  | Some iterations ->
      (* If the event has no iterations for this loop, it's before the loop *)
      List.length iterations = 0
  | None ->
      (* No loop context means it's before any loop *)
      true

(** Condition 2: Reads must read from valid sources *)
let check_condition2_read_sources (structure : symbolic_event_structure)
    (execution : symbolic_execution) (loop_id : int)
    (loop_indices : (int, int list) Hashtbl.t) : condition_result =
  (* TODO:
     1. Find all read events in the loop (check loop_indices)
     2. For each read, trace its value origin through rf relation
     3. Check that origin satisfies one of:
        a. Write in same iteration before the read
        b. Write from different thread
        c. Read-don't-modify RMW derived from valid write
  *)
  { satisfied = true; violations = [] }

(** {1 Condition 3: Branch Condition Symbols (Syntactic + Origin Tracking)} *)

(** Extract all symbols from IR expressions *)
let rec extract_symbols_from_ir_expr (expr : expr) : string list =
  match expr with
  | ESymbol s -> [s]
  | EBinOp (e1, _, e2) ->
      extract_symbols_from_ir_expr e1 @ extract_symbols_from_ir_expr e2
  | EUnOp (_, e) -> extract_symbols_from_ir_expr e
  | EOr clauses ->
      List.concat_map (fun clause ->
        List.concat_map extract_symbols_from_ir_expr clause
      ) clauses
  | _ -> []

(** Check if a branch condition depends on pre-loop symbols *)
let check_branch_condition (condition : expr) (structure : symbolic_event_structure)
    (loop_indices : (int, int list) Hashtbl.t) (loop_id : int) : bool =
  (* TODO:
     1. Extract all symbols from condition
     2. For each symbol, get its origin event
     3. Check if any origin event occurred before the loop
  *)
  let symbols = extract_symbols_from_ir_expr condition in
  let has_pre_loop_symbol =
    List.exists (fun sym ->
      match Hashtbl.find_opt structure.origin sym with
      | Some origin_event ->
          event_before_loop loop_indices origin_event loop_id
      | None -> false
    ) symbols
  in
  not has_pre_loop_symbol

(** Condition 3: Branch conditions don't constrain pre-loop symbols *)
let check_condition3_branch_conditions (program : ir_node list)
    (structure : symbolic_event_structure) (loop_indices : (int, int list) Hashtbl.t)
    (loop_id : int) : condition_result =
  (* Find all nodes belonging to this loop *)
  let loop_nodes = find_loop_nodes program loop_id in

  (* Extract all conditions from these nodes *)
  let conditions =
    List.concat_map (fun (node: ir_node) -> Ir.extract_conditions_from_stmt node.stmt) loop_nodes
  in

  (* Check each condition for pre-loop symbols *)
  let violations = ref [] in
  List.iter (fun condition ->
    let symbols = extract_symbols_from_ir_expr condition in
    List.iter (fun sym ->
      match Hashtbl.find_opt structure.origin sym with
      | Some origin_event ->
          if event_before_loop loop_indices origin_event loop_id then
            violations :=
              Printf.sprintf "Condition depends on pre-loop symbol '%s' (origin: event %d)"
                sym origin_event :: !violations
      | None -> ()
    ) symbols
  ) conditions;

  { satisfied = List.length !violations = 0; violations = !violations }

(** {1 Condition 4: Inter-iteration Ordering (Semantic)} *)

(** Check if two events are ordered by (ppo ∪ dp)* *)
let events_ordered_by_ppo_dp (e1 : int) (e2 : int)
    (ppo : (int * int) uset) (dp : (int * int) uset) : bool =
  (* Compute transitive closure of ppo ∪ dp *)
  let ppo_dp = USet.union ppo dp in
  let ppo_dp_tc = URelation.transitive_closure ppo_dp in
  USet.mem ppo_dp_tc (e1, e2)

(** Condition 4: Events from prior iterations ordered before later iterations *)
let check_condition4_iteration_ordering (structure : symbolic_event_structure)
    (execution : symbolic_execution) (loop_id : int)
    (loop_indices : (int, int list) Hashtbl.t) : condition_result =
  (* TODO:
     1. Collect all events in this loop
     2. Group events by iteration number
     3. For each pair (e1, e2) where iter(e1) < iter(e2):
        - Verify (e1, e2) ∈ (ppo ∪ dp)*
     4. Report violations if any
  *)
  let violations = ref [] in

  (* Collect all events in the loop *)
  let loop_events =
    USet.filter (fun evt_label ->
      match get_iteration_for_loop loop_indices evt_label loop_id with
      | Some _ -> true
      | None -> false
    ) execution.ex_e
  in

  (* Check ordering between iterations *)
  (* TODO: Implement full checking logic *)

  { satisfied = true; violations = !violations }

(** {1 Main Episodicity Check} *)

(** Check if a specific loop is episodic *)
let check_loop_episodicity (ctx : mordor_ctx) (loop_id : int)
    : loop_episodicity_result option =
  match ctx.program_stmts, ctx.events, ctx.structure, ctx.executions with
  | Some program, Some events, Some structure, Some executions ->
      (* For now, check against the first execution
         TODO: Should we check all executions? *)
      if USet.is_empty executions then None
      else
        let execution =
          match USet.values executions with
          | [] -> failwith "Impossible: checked is_empty"
          | exec :: _ -> exec
        in

        (* Build loop indices mapping from events *)
        let loop_indices = Hashtbl.create 256 in
        (* TODO: Populate loop_indices from execution events *)

        (* Check all four conditions *)
        let cond1 = check_condition1_register_access program loop_id in
        let cond2 = check_condition2_read_sources structure execution loop_id loop_indices in
        let cond3 = check_condition3_branch_conditions program structure loop_indices loop_id in
        let cond4 = check_condition4_iteration_ordering structure execution loop_id loop_indices in

        let is_episodic =
          cond1.satisfied && cond2.satisfied && cond3.satisfied && cond4.satisfied
        in

        Some {
          loop_id;
          condition1 = cond1;
          condition2 = cond2;
          condition3 = cond3;
          condition4 = cond4;
          is_episodic;
        }
  | _ -> None

(** Main episodicity testing function called from pipeline *)
let step_test_episodicity (ctx : mordor_ctx) : unit =
  match ctx.program_stmts with
  | Some program ->
      (* Collect all loop IDs from the program *)
      let loop_ids = collect_loop_ids program in

      Logs.info (fun m ->
          m "Testing episodicity for %d loops: [%s]"
            (List.length loop_ids)
            (String.concat ", " (List.map string_of_int loop_ids))
      );

      (* Initialize episodicity table *)
      let is_episodic_table = Hashtbl.create 10 in

      (* Check each loop *)
      List.iter (fun loop_id ->
        match check_loop_episodicity ctx loop_id with
        | Some result ->
            Hashtbl.add is_episodic_table loop_id result.is_episodic;

            Logs.info (fun m ->
                m "Loop %d: %s" loop_id
                  (if result.is_episodic then "EPISODIC" else "NOT EPISODIC")
            );

            (* Log violations for each condition *)
            if not result.condition1.satisfied then
              Logs.warn (fun m ->
                  m "  Condition 1 violations: %s"
                    (String.concat "; " result.condition1.violations)
              );
            if not result.condition2.satisfied then
              Logs.warn (fun m ->
                  m "  Condition 2 violations: %s"
                    (String.concat "; " result.condition2.violations)
              );
            if not result.condition3.satisfied then
              Logs.warn (fun m ->
                  m "  Condition 3 violations: %s"
                    (String.concat "; " result.condition3.violations)
              );
            if not result.condition4.satisfied then
              Logs.warn (fun m ->
                  m "  Condition 4 violations: %s"
                    (String.concat "; " result.condition4.violations)
              );
        | None ->
            Logs.warn (fun m ->
                m "Loop %d: Could not analyze (missing execution data)" loop_id
            );
            Hashtbl.add is_episodic_table loop_id false
      ) loop_ids;

      (* Store results in context *)
      ctx.is_episodic <- Some is_episodic_table
  | None ->
      Logs.warn (fun m -> m "No program statements available for episodicity analysis")

(** {1 Query Functions} *)

(** Check if a specific loop is episodic *)
let is_loop_episodic (ctx : mordor_ctx) (loop_id : int) : bool option =
  match ctx.is_episodic with
  | Some table -> Hashtbl.find_opt table loop_id
  | None -> None

(** Get all episodic loops *)
let get_episodic_loops (ctx : mordor_ctx) : int list =
  match ctx.is_episodic with
  | Some table ->
      Hashtbl.fold (fun lid is_episodic acc ->
        if is_episodic then lid :: acc else acc
      ) table []
  | None -> []

(** Get all non-episodic loops *)
let get_non_episodic_loops (ctx : mordor_ctx) : int list =
  match ctx.is_episodic with
  | Some table ->
      Hashtbl.fold (fun lid is_episodic acc ->
        if not is_episodic then lid :: acc else acc
      ) table []
  | None -> []
