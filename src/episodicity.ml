(** {1 Episodicity Analysis Module}

    This module implements episodicity checks for loops based on Definition 4.1.
    A loop is episodic if it satisfies four conditions:

    + Registers only accessed if written to ⊑-before within same iteration or
      before loop
    + Reads must read from: (a) same-iteration writes, (b) cross-thread writes,
      or (c) read-don't-modify RMWs derived from such writes
    + Branching conditions don't constrain symbols read before the loop
    + Events from prior iterations are ordered before later iterations by (ppo ∪
      dp)*

    Where:
    - ⊑ is sequenced-before (program order)
    - ⪯ is ppo (preserved program order)
    - dp is semantic dependency (from justification freezing)

    @author Mordor Team *)

open Context
open Eventstructures
open Expr
open Interpret
open Ir_context_utils
open Types
open Uset
open Lwt.Syntax

(** Note: We work with ir_node (Context.ir_node) which is ir_node_ann
    Ir.ir_node. The annotations contain loop_ctx, thread_ctx, etc. *)

(** {1 Types} *)

(** Cache for episodicity analysis containing symbolic and concrete event
    structures.

    This cache stores precomputed event structures and executions to avoid
    redundant computation during episodicity checking. *)
type episodicity_cache = {
  mutable symbolic_structure : symbolic_event_structure;
      (** Event structure with symbolic loop semantics *)
  mutable symbolic_source_spans : (int, source_span) Hashtbl.t;
      (** Source span mapping for symbolic events *)
  mutable three_structure : symbolic_event_structure;
      (** Event structure with 3-step counter semantics *)
  mutable three_source_spans : (int, source_span) Hashtbl.t;
      (** Source span mapping for 3-step events *)
  mutable three_executions : symbolic_execution list;
      (** List of concrete executions with 3 iterations *)
}

(** {1 Event Structure Utilities} *)

(** Get all events in a specific loop from the symbolic event structure.

    @param structure The symbolic event structure to query
    @param loop_id The identifier of the loop
    @return A set of event labels that belong to the specified loop *)
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

(** Check if a register is written before it's read within a loop body.

    This implements Condition 1 of episodicity: registers are only accessed if
    they have been written to ⊑-before within the same iteration or before the
    loop starts.

    @param loop_body The list of IR nodes representing the loop body
    @return A condition result indicating satisfaction and any violations *)
let check_register_accesses_in_loop (loop_body : ir_node list) :
    condition_result =
  let violations = ref [] in
  let satisfied = ref true in
  let written_before_read = USet.create () in
  let must_not_write = USet.create () in

  (* Recursively traverse IR nodes to check register accesses.

     @param nodes The list of IR nodes to traverse
     @param written_before_read Set of registers written before current point
     @param must_not_write Set of registers that must not be written *)
  let rec traverse_nodes (nodes : ir_node list) written_before_read
      must_not_write =
    match nodes with
    | [] -> ()
    | node :: rest -> (
        let stmt = node.stmt in
          match stmt with
          | Threads { threads } ->
              (* Each thread gets independent copies of register sets *)
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
                (* Each branch gets independent copies *)
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

(** Check Condition 1: Registers only accessed if written to ⊑-before.

    @param program The complete program as a list of IR nodes
    @param cache The episodicity cache (unused in this check)
    @param loop_id The identifier of the loop to check
    @return A condition result indicating satisfaction and any violations *)
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
        | _ -> ()
      )
      loop_nodes;
    { satisfied = !satisfied; violations = !violations }

(** {1 Condition 2: Memory Read Sources (Semantic)} *)

(** Get the origin event for a symbol.

    @param structure The symbolic event structure
    @param symbol The symbol name to look up
    @return The event label that introduced this symbol, if any *)
let get_symbol_origin (structure : symbolic_event_structure) (symbol : string) :
    int option =
  Hashtbl.find_opt structure.origin symbol

(** Check Condition 2: Reads must read from valid sources.

    Valid sources are:
    - Same-iteration writes (⊑-before the read)
    - Cross-thread writes
    - Read-don't-modify RMWs derived from such writes

    @param cache The episodicity cache containing event structures
    @param loop_id The identifier of the loop to check
    @return
      A condition result (async) indicating satisfaction and any violations *)
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
          (* Find writes to same location not ⊑-before the read *)
          let* writes_in_loop_not_before_read =
            USet.async_filter
              (fun write_event ->
                if USet.mem cache.symbolic_structure.po (write_event, read_event)
                then Lwt.return false
                else
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
                            (* Only invalid if not a read-don't-modify RMW *)
                            Lwt.return
                              (not (Events.is_rdmw structure write_event))
                          else Lwt.return false
                  | _ -> Lwt.return false
              )
              writes_in_loop
          in
            (* Record violations for invalid write sources *)
            USet.iter
              (fun write_event ->
                let violation =
                  WriteConditionViolation
                    (WriteFromPreviousIteration
                       ( Events.get_loc structure read_event
                         |> Option.map show_expr
                         |> Option.value ~default:"",
                         Hashtbl.find_opt cache.symbolic_source_spans read_event,
                         Hashtbl.find_opt cache.symbolic_source_spans
                           write_event
                       )
                    )
                in
                  violations := violation :: !violations
              )
              writes_in_loop_not_before_read;
            Lwt.return ()
        )
        reads_in_loop
    in

    Lwt.return
      { satisfied = List.length !violations == 0; violations = !violations }

(** {1 Condition 3: Branch Condition Symbols (Syntactic + Origin Tracking)} *)

(** Check Condition 3: Branch conditions don't constrain pre-loop symbols.

    This ensures that branching conditions within the loop don't constrain
    symbols that were read before the loop started, maintaining iteration
    independence.

    @param program The complete program as a list of IR nodes
    @param cache The episodicity cache containing event structures
    @param loop_id The identifier of the loop to check
    @return A condition result indicating satisfaction and any violations *)
let check_condition3_branch_conditions (program : ir_node list) cache
    (loop_id : int) : condition_result =
  Logs.debug (fun m -> m "Checking Condition 3 for Loop %d..." loop_id);
  let structure = cache.symbolic_structure in
    Logs.debug (fun m ->
        m "Symbolic Event Structure:\n%s"
          (show_symbolic_event_structure structure)
    );
    let violations = ref [] in
    let events_in_loop =
      SymbolicEventStructure.events_in_loop structure loop_id
    in
      Logs.debug (fun m ->
          m "  Found %d events in loop" (USet.size events_in_loop)
      );
      USet.iter
        (fun event ->
          (* Get predicates (branch conditions) for this event *)
          let event_preds =
            Hashtbl.find_opt structure.restrict event
            |> Option.value ~default:[]
            |> USet.of_list
          in
          (* Find events before the loop *)
          let events_before_loop =
            USet.set_minus
              (SymbolicEventStructure.events_po_before structure event)
              events_in_loop
          in
          (* Get predicates from before the loop *)
          let preds =
            USet.map
              (fun e ->
                Hashtbl.find_opt structure.restrict e
                |> Option.value ~default:[]
              )
              events_before_loop
            |> USet.map USet.of_list
            |> USet.flatten
            |> USet.set_minus event_preds
          in
          (* Extract symbols from predicates *)
          let symbols =
            USet.map Expr.get_symbols preds
            |> USet.map USet.of_list
            |> USet.flatten
          in
          (* Find symbols that originated before the loop *)
          let symbols_read_before_loop =
            USet.filter
              (fun sym ->
                match Hashtbl.find_opt structure.origin sym with
                | Some origin_event -> USet.mem events_before_loop origin_event
                | None -> false
              )
              symbols
          in
            Logs.debug (fun m ->
                m
                  "  Event %d: Found %d branch condition symbols read before \
                   loop"
                  event
                  (USet.size symbols_read_before_loop)
            );
            (* Record violations for constrained pre-loop symbols *)
            USet.iter
              (fun sym ->
                let violation =
                  BranchConditionViolation
                    (BranchConstraintsSymbol
                       ( sym,
                         Hashtbl.find_opt structure.origin sym
                         |> Option.value ~default:(-1),
                         Hashtbl.find_opt cache.symbolic_source_spans event
                       )
                    )
                in
                  violations := violation :: !violations
              )
              symbols_read_before_loop
        )
        events_in_loop;

      { satisfied = List.length !violations == 0; violations = !violations }

(** {1 Condition 4: Inter-iteration Ordering (Semantic)} *)

(** Check Condition 4: Events from prior iterations ordered before later
    iterations.

    This checks that all events from iteration i are ordered before all events
    from iteration i+1 by the transitive closure of (ppo ∪ dp), ensuring proper
    happens-before relationships across iterations.

    @param cache
      The episodicity cache containing event structures and executions
    @param loop_id The identifier of the loop to check
    @return A condition result indicating satisfaction and any violations *)
let check_condition4_iteration_ordering cache (loop_id : int) : condition_result
    =
  let violations = ref [] in

  let structure = cache.three_structure in
  let events_in_loop =
    SymbolicEventStructure.events_in_loop structure loop_id
  in
  (* Group events by iteration number *)
  let events_by_iteration = Hashtbl.create 10 in
    USet.iter
      (fun event ->
        match get_iteration_for_loop structure.loop_indices event loop_id with
        | Some iter ->
            let existing =
              Hashtbl.find_opt events_by_iteration iter
              |> Option.value ~default:(USet.create ())
            in
              Hashtbl.replace events_by_iteration iter (USet.add existing event)
        | None -> ()
      )
      events_in_loop;

    (* Compute (ppo ∪ dp)* for the loop *)
    let delta_loop = URelation.cross events_in_loop events_in_loop in
    let dp_ppo =
      List.map (fun exec -> USet.union exec.dp exec.ppo) cache.three_executions
      |> List.map (fun dp_ppo -> USet.intersection dp_ppo delta_loop)
      |> List.map URelation.transitive_closure
      |> List.fold_left USet.intersection delta_loop
    in
    let unordered_events = ref [] in
    let satisfied = ref true in

    (* Check ordering between consecutive iterations *)
    Hashtbl.iter
      (fun iter events_curr ->
        let next_iter = iter + 1 in
          match Hashtbl.find_opt events_by_iteration next_iter with
          | Some events_next ->
              USet.iter
                (fun e_curr ->
                  USet.iter
                    (fun e_next ->
                      if not (USet.mem dp_ppo (e_curr, e_next)) then (
                        let violation =
                          LoopConditionViolation
                            (LoopIterationOrderingViolation
                               ( iter,
                                 Hashtbl.find_opt cache.three_source_spans
                                   e_curr,
                                 Hashtbl.find_opt cache.three_source_spans
                                   e_next
                               )
                            )
                        in
                          violations := violation :: !violations;
                          satisfied := false
                      )
                    )
                    events_next
                )
                events_curr
          | None -> ()
      )
      events_by_iteration;

    { satisfied = !satisfied; violations = !violations }

(** {1 Main Episodicity Check} *)

(** Check if a specific loop is episodic by verifying all four conditions.

    @param ctx The Mordor context containing the program
    @param cache The episodicity cache with precomputed structures
    @param loop_id The identifier of the loop to check
    @return An optional loop episodicity result, or None if analysis fails *)
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

(** Main episodicity testing function called from the analysis pipeline.

    This function:
    + Collects all loop IDs from the program
    + Generates symbolic and concrete (3-iteration) event structures
    + Computes dependencies for the concrete executions
    + Checks episodicity for each loop
    + Stores results in the context

    @param lwt_ctx The Mordor context wrapped in Lwt
    @return The updated Mordor context with episodicity results *)
let step_test_episodicity (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match ctx.program_stmts with
    | Some program ->
        (* Collect all loop IDs from the program *)
        let loop_ids = collect_loop_ids program in
        let coherence_restrictions =
          {
            Coherence.coherent =
              ( try ctx.options.coherent with _ -> "imm"
              )
              (* default to IMM if not specified *);
          }
        in

        (* Generate symbolic event structure *)
        let* symbolic_structure, symbolic_source_spans =
          SymbolicLoopSemantics.interpret lwt_ctx
        in
          Logs.debug (fun m ->
              m "Symbolic event structure with symbolic loop semantics.\n%s\n\n"
                (show_symbolic_event_structure symbolic_structure)
          );
          (* Generate 3-iteration event structure *)
          let* three_structure, three_source_spans =
            StepCounterSemantics.interpret ~step_counter:3 lwt_ctx
          in
            (* Compute dependencies for 3-iteration executions *)
            let* _, three_executions =
              Symmrd.calculate_dependencies ~include_rf:false three_structure
                ~exhaustive:true ~restrictions:coherence_restrictions
            in
            let cache =
              {
                symbolic_structure;
                symbolic_source_spans;
                three_structure;
                three_source_spans;
                three_executions;
              }
            in

            let loop_episodicity_results = ref [] in

            (* Initialize episodicity table *)
            let is_episodic_table = Hashtbl.create 10 in

            (* Check each loop *)
            let* () =
              Lwt_list.iter_s
                (fun loop_id ->
                  Logs.info (fun m -> m "Analyzing Loop %d..." loop_id);
                  let* episodic_result =
                    check_loop_episodicity ctx cache loop_id
                  in
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
                        Logs.warn (fun m ->
                            m "Loop %d: Could not analyze" loop_id
                        );
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

(** Check if a specific loop is episodic.

    @param ctx The Mordor context containing analysis results
    @param loop_id The identifier of the loop to query
    @return Some true if episodic, Some false if not, None if not analyzed *)
let is_loop_episodic (ctx : mordor_ctx) (loop_id : int) : bool option =
  match ctx.is_episodic with
  | Some table -> Hashtbl.find_opt table loop_id
  | None -> None

(** Get all episodic loops from the analysis results.

    @param ctx The Mordor context containing analysis results
    @return A list of loop IDs that are episodic *)
let get_episodic_loops (ctx : mordor_ctx) : int list =
  match ctx.is_episodic with
  | Some table ->
      Hashtbl.fold
        (fun lid is_episodic acc -> if is_episodic then lid :: acc else acc)
        table []
  | None -> []

(** Get all non-episodic loops from the analysis results.

    @param ctx The Mordor context containing analysis results
    @return A list of loop IDs that are not episodic *)
let get_non_episodic_loops (ctx : mordor_ctx) : int list =
  match ctx.is_episodic with
  | Some table ->
      Hashtbl.fold
        (fun lid is_episodic acc -> if not is_episodic then lid :: acc else acc)
        table []
  | None -> []

(** Send episodicity results via a callback function.

    Serializes the episodicity results to JSON and sends them using the provided
    send function.

    @param send_func Function to send the JSON string (async)
    @param ctx The Mordor context wrapped in Lwt
    @return The unmodified Mordor context *)
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
