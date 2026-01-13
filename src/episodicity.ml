(** Episodicity Analysis Module

    This module implements episodicity checks for loops based on Definition 4.1.
    A loop is episodic if it satisfies four conditions: 1. Registers only
    accessed if written to ⊑-before within same iteration or before loop 2.
    Reads must read from: (a) same-iteration writes, (b) cross-thread writes, or
    (c) read-don't-modify RMWs derived from such writes 3. Branching conditions
    don't constrain symbols read before the loop 4. Events from prior iterations
    are ordered before later iterations by (ppo ∪ dp)*

    Where:
    - ⊑ is sequenced-before (program order)
    - ⪯ is ppo (preserved program order)
    - dp is semantic dependency (from justification freezing) *)

open Context
open Eventstructures
open Interpret
open Ir_context_utils
open Types
open Uset
open Lwt.Syntax

(** Note: We work with ir_node (Context.ir_node) which is ir_node_ann Ir.ir_node
    The annotations contain loop_ctx, thread_ctx, etc. *)

(** {1 Episodcity Cache} *)
type episodicity_cache = {
  mutable symbolic_structure : symbolic_event_structure;
  mutable source_spans : (int, source_span) Hashtbl.t;
}

(** {1 Event Structure Utilities} *)

(** Get all events in a specific loop from the symbolic event structure *)
let get_events_in_loop (structure : symbolic_event_structure) (loop_id : int) :
    int uset =
  USet.filter
    (fun evt_label ->
      match get_iteration_for_loop structure.loop_indices evt_label loop_id with
      | Some _ -> true
      | None -> false
    )
    structure.e

(** {1 Condition 1: Register Access Restriction (Syntactic)} *)

(** Check if a register is written before it's read within a loop body *)
let check_register_accesses_in_loop (loop_body : ir_node list) :
    condition_result =
  let violations = ref [] in
  let satisfied = ref true in
  let written_before_read = USet.create () in
  let must_not_write = USet.create () in
  let rec traverse_nodes (nodes : ir_node list) written_before_read
      must_not_write =
    match nodes with
    | [] -> ()
    | node :: rest -> (
        let stmt = node.stmt in
          match stmt with
          | Threads { threads } ->
              List.iter
                (fun thread ->
                  traverse_nodes thread
                    (USet.clone written_before_read)
                    (USet.clone must_not_write)
                )
                threads
          | While { condition; body } ->
              let read_regs =
                Ir.extract_read_registers_from_stmt stmt |> USet.of_list
              in
              let must_not_write =
                USet.set_minus read_regs written_before_read
                |> USet.union must_not_write
              in
                traverse_nodes (body @ rest) written_before_read must_not_write
          | Do { condition; body } ->
              traverse_nodes body written_before_read must_not_write;
              let read_regs =
                Ir.extract_read_registers_from_stmt stmt |> USet.of_list
              in
              let must_not_write =
                USet.set_minus read_regs written_before_read
                |> USet.union must_not_write
              in
                traverse_nodes rest written_before_read must_not_write
          | If { condition; then_body; else_body } -> (
              let read_regs =
                Ir.extract_read_registers_from_stmt stmt |> USet.of_list
              in
              let must_not_write =
                USet.set_minus read_regs written_before_read
                |> USet.union must_not_write
              in
                traverse_nodes (then_body @ rest)
                  (USet.clone written_before_read)
                  (USet.clone must_not_write);
                match else_body with
                | Some else_stmts ->
                    traverse_nodes (else_stmts @ rest)
                      (USet.clone written_before_read)
                      (USet.clone must_not_write)
                | None -> ()
            )
          | Labeled { stmt; _ } ->
              traverse_nodes (stmt :: rest) written_before_read must_not_write
          | _ ->
              let written_regs =
                Ir.extract_written_registers_from_stmt stmt |> USet.of_list
              in
              let read_regs =
                Ir.extract_read_registers_from_stmt stmt |> USet.of_list
              in

              (* Check reads against written_before_read *)
              USet.iter
                (fun reg -> USet.add must_not_write reg |> ignore)
                (USet.set_minus read_regs written_before_read);

              let invalid_written_regs =
                USet.intersection written_regs must_not_write
              in

              (* Record violations for invalid writes *)
              USet.iter
                (fun reg ->
                  let violation =
                    RegisterConditionViolation
                      (RegisterReadBeforeWrite
                         (reg, node.annotations.source_span)
                      )
                  in
                    violations := violation :: !violations;
                    satisfied := false
                )
                invalid_written_regs;

              (* Update written_before_read with newly written registers *)
              USet.iter
                (fun reg -> USet.add written_before_read reg |> ignore)
                (USet.set_minus written_regs must_not_write);

              (* Recurse on remaining nodes *)
              traverse_nodes rest written_before_read must_not_write
      )
  in
    traverse_nodes loop_body written_before_read must_not_write;
    { satisfied = !satisfied; violations = !violations }

(** Condition 1: Registers only accessed if written to ⊑-before *)
let check_condition1_register_access (program : ir_node list) cache
    (loop_id : int) : condition_result =
  let violations = ref [] in
  let satisfied = ref true in
  let loop_nodes = find_loop_nodes program loop_id in
    List.iter
      (fun (node : ir_node) ->
        match node.stmt with
        | While { body; _ } | Do { body; _ } ->
            let result = check_register_accesses_in_loop body in
              satisfied := !satisfied && result.satisfied;
              violations := result.violations @ !violations
        | _ -> failwith "Expected While or Do node in loop nodes"
      )
      loop_nodes;
    { satisfied = !satisfied; violations = !violations }

(** {1 Condition 2: Memory Read Sources (Semantic)} *)

(** Get the origin event for a symbol *)
let get_symbol_origin (structure : symbolic_event_structure) (symbol : string) :
    int option =
  Hashtbl.find_opt structure.origin symbol

(** Condition 2: Reads must read from valid sources *)
let check_condition2_read_sources cache (loop_id : int) : condition_result Lwt.t
    =
  let structure = cache.symbolic_structure in
  let events_in_loop =
    SymbolicEventStructure.events_in_loop structure loop_id
  in
  let reads_in_loop = USet.intersection events_in_loop structure.read_events in
  let writes_in_loop =
    USet.intersection events_in_loop structure.write_events
  in
  let violations = ref [] in
    let* () =
      USet.iter_async
        (fun read_event ->
          let* writes_in_loop_before_read =
            USet.async_filter
              (fun write_event ->
                if USet.mem cache.symbolic_structure.po (write_event, read_event)
                then
                  match
                    ( Events.get_loc structure write_event,
                      Events.get_loc structure read_event
                    )
                  with
                  | Some wloc, Some rloc ->
                      let state =
                        Hashtbl.find_opt structure.restrict read_event
                      in
                        let* same_loc = Solver.expoteq ?state wloc rloc in
                          if same_loc then
                            Lwt.return
                              (USet.mem structure.po (write_event, read_event)
                              || Events.is_rdmw structure write_event
                              )
                          else Lwt.return false
                  | _ -> Lwt.return false
                else Lwt.return false
              )
              writes_in_loop
          in
            USet.iter
              (fun write_event ->
                (* Check if write_event is a valid source for read_event *)
                let violation =
                  WriteConditionViolation
                    (WriteFromPreviousIteration
                       ( Events.get_loc structure read_event
                         |> Option.map show_expr
                         |> Option.value ~default:"",
                         Hashtbl.find_opt cache.source_spans read_event,
                         Hashtbl.find_opt cache.source_spans write_event
                       )
                    )
                in
                  violations := violation :: !violations
              )
              writes_in_loop_before_read;
            Lwt.return ()
        )
        reads_in_loop
    in

    Lwt.return
      { satisfied = List.length !violations == 0; violations = !violations }

(** {1 Condition 3: Branch Condition Symbols (Syntactic + Origin Tracking)} *)

(** Extract all symbols from IR expressions *)
let rec extract_symbols_from_ir_expr (expr : expr) : string list =
  match expr with
  | ESymbol s -> [ s ]
  | EBinOp (e1, _, e2) ->
      extract_symbols_from_ir_expr e1 @ extract_symbols_from_ir_expr e2
  | EUnOp (_, e) -> extract_symbols_from_ir_expr e
  | EOr clauses ->
      List.concat_map
        (fun clause -> List.concat_map extract_symbols_from_ir_expr clause)
        clauses
  | _ -> []

(** Check if a branch condition depends on pre-loop symbols *)
let check_branch_condition (condition : expr)
    (structure : symbolic_event_structure) (loop_id : int) : bool =
  (* TODO:
     1. Extract all symbols from condition
     2. For each symbol, get its origin event
     3. Check if any origin event occurred before the loop
  *)
  true

(** Condition 3: Branch conditions don't constrain pre-loop symbols *)
let check_condition3_branch_conditions (program : ir_node list) cache
    (loop_id : int) : condition_result =
  { satisfied = true; violations = [] }

(** {1 Condition 4: Inter-iteration Ordering (Semantic)} *)

(** Check if two events are ordered by (ppo ∪ dp)* *)
let events_ordered_by_ppo_dp (e1 : int) (e2 : int) (ppo : (int * int) uset)
    (dp : (int * int) uset) : bool =
  (* Compute transitive closure of ppo ∪ dp *)
  let ppo_dp = USet.union ppo dp in
  let ppo_dp_tc = URelation.transitive_closure ppo_dp in
    USet.mem ppo_dp_tc (e1, e2)

(** Condition 4: Events from prior iterations ordered before later iterations *)
let check_condition4_iteration_ordering cache (loop_id : int) : condition_result
    =
  (* TODO:
     1. Collect all events in this loop
     2. Group events by iteration number
     3. For each pair (e1, e2) where iter(e1) < iter(e2):
        - Verify (e1, e2) ∈ (ppo ∪ dp)*
     4. Report violations if any
  *)
  let violations = ref [] in

  (* TODO Collect all events in the loop *)

  (* Check ordering between iterations *)
  (* TODO: Implement full checking logic *)
  { satisfied = true; violations = !violations }

(** {1 Main Episodicity Check} *)

(** Check if a specific loop is episodic *)
let check_loop_episodicity (ctx : mordor_ctx) cache (loop_id : int) :
    loop_episodicity_result option Lwt.t =
  match ctx.program_stmts with
  | Some program ->
      (* Check all four conditions *)
      let cond1 = check_condition1_register_access program cache loop_id in
        let* cond2 = check_condition2_read_sources cache loop_id in
        let cond3 = check_condition3_branch_conditions program cache loop_id in
        let cond4 = check_condition4_iteration_ordering cache loop_id in

        let is_episodic =
          cond1.satisfied
          && cond2.satisfied
          && cond3.satisfied
          && cond4.satisfied
        in

        Lwt.return_some
          {
            loop_id;
            condition1 = cond1;
            condition2 = cond2;
            condition3 = cond3;
            condition4 = cond4;
            is_episodic;
          }
  | _ -> Lwt.return_none

(** Main episodicity testing function called from pipeline *)
let step_test_episodicity (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match ctx.program_stmts with
    | Some program ->
        (* Collect all loop IDs from the program *)
        let loop_ids = collect_loop_ids program in

        let* symbolic_structure, source_spans =
          SymbolicLoopSemantics.interpret lwt_ctx
        in

        let cache = { symbolic_structure; source_spans } in

        Logs.info (fun m ->
            m "Testing episodicity for %d loops: [%s]" (List.length loop_ids)
              (String.concat ", " (List.map string_of_int loop_ids))
        );

        let loop_episodicity_results = ref [] in

        (* Initialize episodicity table *)
        let is_episodic_table = Hashtbl.create 10 in

        (* Check each loop *)
        let* () =
          Lwt_list.iter_s
            (fun loop_id ->
              Logs.info (fun m -> m "Analyzing Loop %d..." loop_id);
              let* episodic_result = check_loop_episodicity ctx cache loop_id in
                match episodic_result with
                | Some result ->
                    Hashtbl.add is_episodic_table loop_id result.is_episodic;

                    Logs.info (fun m ->
                        m "Loop %d: %s" loop_id
                          ( if result.is_episodic then "EPISODIC"
                            else "NOT EPISODIC"
                          )
                    );

                    (* Log violations for each condition *)
                    if not result.condition1.satisfied then
                      Logs.warn (fun m ->
                          m "  Condition 1 violations: %s"
                            (String.concat "; "
                               (List.map show_episodicity_violation
                                  result.condition1.violations
                               )
                            )
                      );
                    if not result.condition2.satisfied then
                      Logs.warn (fun m ->
                          m "  Condition 2 violations: %s"
                            (String.concat "; "
                               (List.map show_episodicity_violation
                                  result.condition2.violations
                               )
                            )
                      );
                    if not result.condition3.satisfied then
                      Logs.warn (fun m ->
                          m "  Condition 3 violations: %s"
                            (String.concat "; "
                               (List.map show_episodicity_violation
                                  result.condition3.violations
                               )
                            )
                      );
                    if not result.condition4.satisfied then
                      Logs.warn (fun m ->
                          m "  Condition 4 violations: %s"
                            (String.concat "; "
                               (List.map show_episodicity_violation
                                  result.condition4.violations
                               )
                            )
                      );
                    loop_episodicity_results :=
                      result :: !loop_episodicity_results;
                    Lwt.return_unit
                | None ->
                    Logs.warn (fun m -> m "Loop %d: Could not analyze" loop_id);
                    Hashtbl.add is_episodic_table loop_id false;
                    Lwt.return_unit
            )
            loop_ids
        in

        (* Store results in context *)
        ctx.is_episodic <- Some is_episodic_table;
        ctx.episodicity_results <-
          Some
            {
              type_ = "episodicity-results";
              loop_episodicity_results = List.rev !loop_episodicity_results;
            };
        Lwt.return ctx
    | None ->
        Logs.warn (fun m ->
            m "No program statements available for episodicity analysis"
        );
        Lwt.return ctx

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
      Hashtbl.fold
        (fun lid is_episodic acc -> if is_episodic then lid :: acc else acc)
        table []
  | None -> []

(** Get all non-episodic loops *)
let get_non_episodic_loops (ctx : mordor_ctx) : int list =
  match ctx.is_episodic with
  | Some table ->
      Hashtbl.fold
        (fun lid is_episodic acc -> if not is_episodic then lid :: acc else acc)
        table []
  | None -> []

let send_episodicity_results (send_func : string -> unit Lwt.t)
    (ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = ctx in
    match ctx.episodicity_results with
    | Some results ->
        let json = loop_episodicity_result_summary_to_yojson results in
        let json_str = Yojson.Safe.to_string json in
          let* () = send_func json_str in
            Lwt.return ctx
    | None -> Lwt.return ctx
