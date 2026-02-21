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
open Executions
open Expr
open Forwarding
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
  mutable program : ir_node list;
      (** The complete program as a list of IR nodes *)
  mutable symbolic_structure : symbolic_event_structure;
      (** Event structure with symbolic loop semantics *)
  mutable symbolic_source_spans : (int, source_span) Hashtbl.t;
      (** Source span mapping for symbolic events *)
  mutable symbolic_fwd_es_ctx : Forwarding.event_structure_context;
      (** Forwarding context for symbolic event structure *)
  mutable symbolic_justifications : justification uset;
      (** Justifications for symbolic event structure *)
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

module RegisterCondition = struct
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
                  traverse_nodes (body @ rest) written_before_read
                    must_not_write
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
  let check cache (loop_id : int) : condition_result Lwt.t =
    let violations = ref [] in
    let satisfied = ref true in
    let { program; _ } = cache in
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
      Lwt.return { satisfied = !satisfied; violations = !violations }
end

(** {1 Condition 2: Memory Read Sources (Semantic)} *)

module WriteCondition = struct
  (** Get the origin event for a symbol.

      @param structure The symbolic event structure
      @param symbol The symbol name to look up
      @return The event label that introduced this symbol, if any *)
  let get_symbol_origin (structure : symbolic_event_structure) (symbol : string)
      : int option =
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
  let check cache (loop_id : int) : condition_result Lwt.t =
    let { symbolic_structure; symbolic_source_spans; _ } = cache in
    let structure = symbolic_structure in
    let events_in_loop =
      SymbolicEventStructure.events_in_loop structure loop_id
    in
    let reads_in_loop =
      USet.intersection events_in_loop structure.read_events
    in
    let writes_in_loop =
      USet.intersection events_in_loop structure.write_events
    in
      (* filter writes on whether they're in the last iteration of every loop *)
      let* writes_in_loop =
        USet.async_filter
          (fun write_event ->
            (* exclude writes in the last iteration of the loop *)
            let loop_conditions =
              Hashtbl.find_opt structure.loop_indices write_event
              |> Option.value ~default:[]
              |> List.filter_map (fun lid ->
                  Hashtbl.find_opt structure.loop_conditions lid
              )
            in
            let write_valres =
              Hashtbl.find_opt structure.restrict write_event
              |> Option.value ~default:[]
            in
              let* can_continue =
                Lwt_list.filter_s
                  (fun expr -> Solver.is_sat (expr :: write_valres))
                  loop_conditions
              in
                Lwt.return (List.length can_continue > 0)
          )
          writes_in_loop
      in
      let violations = ref [] in
        let* () =
          USet.iter_async
            (fun read_event ->
              (* Find writes to same location not ⊑-before the read *)
              let* writes_in_loop_not_before_read =
                USet.async_filter
                  (fun write_event ->
                    (* exclude writes that are ⊑-before the read *)
                    if USet.mem structure.po (write_event, read_event) then
                      Lwt.return false
                    else
                      (* check if locations match *)
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
                             Hashtbl.find_opt symbolic_source_spans read_event,
                             Hashtbl.find_opt symbolic_source_spans write_event
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
end

(** {1 Condition 3: Branch Condition Symbols (Syntactic + Origin Tracking)} *)

module BranchCondition = struct
  (** Check Condition 3: Branch conditions don't constrain pre-loop symbols.

      This ensures that branching conditions within the loop don't constrain
      symbols that were read before the loop started, maintaining iteration
      independence.

      @param program The complete program as a list of IR nodes
      @param cache The episodicity cache containing event structures
      @param loop_id The identifier of the loop to check
      @return A condition result indicating satisfaction and any violations *)
  let check cache (loop_id : int) : condition_result Lwt.t =
    Logs.debug (fun m -> m "Checking Condition 3 for Loop %d..." loop_id);
    let { program; symbolic_structure; symbolic_source_spans; _ } = cache in
    let structure = symbolic_structure in
      Logs.debug (fun m ->
          m "Symbolic Event Structure:\n%s"
            (show_symbolic_event_structure structure)
      );
      let violations = ref [] in
      let events_in_loop =
        SymbolicEventStructure.events_in_loop structure loop_id
      in
      let branch_events_in_loop =
        USet.intersection events_in_loop structure.branch_events
      in
        Logs.debug (fun m ->
            m "  Found %d events in loop" (USet.size events_in_loop)
        );
        USet.iter
          (fun e ->
            (* Get predicates (branch conditions) for this event *)
            let cond =
              Hashtbl.find_opt structure.events e |> Option.get |> fun event ->
              event.cond |> Option.value ~default:(EBoolean true)
            in
            let symbols = Expr.get_symbols cond |> USet.of_list in
            (* TODO this is too restrictive, we only need to check if the
             branching condition constraints the symbol, not whether it contains
             the symbol. *)
            let symbols_read_before_loop =
              USet.filter
                (fun sym ->
                  match Hashtbl.find_opt structure.origin sym with
                  | Some origin_event ->
                      not (USet.mem events_in_loop origin_event)
                  | None -> false
                )
                symbols
            in
              Logs.debug (fun m ->
                  m
                    "  Event %d: Found %d branch condition symbols read before \
                     loop"
                    e
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
                           Hashtbl.find_opt symbolic_source_spans e
                         )
                      )
                  in
                    violations := violation :: !violations
                )
                symbols_read_before_loop
          )
          events_in_loop;

        Lwt.return
          { satisfied = List.length !violations == 0; violations = !violations }
end

(** {1 Condition 4: Inter-iteration Ordering (Semantic)} *)

module EventsCondition = struct
  (** Check Condition 4: Events from prior iterations ordered before later
      iterations.

      This checks that all events from iteration i are ordered before all events
      from iteration i+1 by the transitive closure of (ppo ∪ dp), ensuring
      proper happens-before relationships across iterations.

      @param cache
        The episodicity cache containing event structures and executions
      @param loop_id The identifier of the loop to check
      @return A condition result indicating satisfaction and any violations *)
  let check cache (loop_id : int) : condition_result Lwt.t =
    let {
      symbolic_structure;
      symbolic_fwd_es_ctx;
      symbolic_justifications;
      symbolic_source_spans;
      _;
    } =
      cache
    in
    let structure = symbolic_structure in
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
                Hashtbl.replace events_by_iteration iter
                  (USet.add existing event)
          | None -> ()
        )
        events_in_loop;

      (* Compute (ppo ∪ dp)* for the loop *)
      let delta_loop = URelation.cross events_in_loop events_in_loop in
      (* TODO use contextual predicates *)
      let fwd_es_ctx = symbolic_fwd_es_ctx in
        let* ppo_rmw = ForwardingContext.compute_ppo_rmw fwd_es_ctx [] in
        let ppo =
          fwd_es_ctx.ppo.ppo_sync
          |> USet.union fwd_es_ctx.ppo.ppo_base
          |> USet.union fwd_es_ctx.ppo.ppo_loc_base
          |> USet.union fwd_es_ctx.ppo.ppo_base
        in
        let dp =
          USet.fold
            (fun acc just ->
              Freeze.freeze_dp structure just |> USet.inplace_union acc
            )
            symbolic_justifications (USet.create ())
        in
        let dp_ppo = USet.union dp ppo |> URelation.transitive_closure in

        let ppo_iter =
          fwd_es_ctx.ppo.ppo_iter_sync
          |> USet.union fwd_es_ctx.ppo.ppo_iter_base
          |> USet.union fwd_es_ctx.ppo.ppo_iter_loc_base
          |> USet.union fwd_es_ctx.ppo.ppo_iter_base
        in
        let cross_iter_ppo =
          ppo_iter
          |> USet.union (URelation.compose [ dp_ppo; ppo_iter ])
          |> USet.union (URelation.compose [ ppo_iter; dp_ppo ])
          |> USet.union (URelation.compose [ dp_ppo; ppo_iter; dp_ppo ])
        in

        let unordered_pairs = USet.set_minus structure.po_iter cross_iter_ppo in

        let violations = ref [] in
        let satisfied = ref true in
          USet.iter
            (fun (e1, e2) ->
              let violation =
                LoopConditionViolation
                  (LoopIterationOrderingViolation
                     ( -1,
                       Hashtbl.find_opt symbolic_source_spans e1,
                       Hashtbl.find_opt symbolic_source_spans e2
                     )
                  )
              in
                violations := violation :: !violations;
                satisfied := false
            )
            unordered_pairs;

          Lwt.return { satisfied = !satisfied; violations = !violations }
end

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
      let* condition1 = RegisterCondition.check cache loop_id in
        let* condition2 = WriteCondition.check cache loop_id in
          let* condition3 = BranchCondition.check cache loop_id in
            let* condition4 = EventsCondition.check cache loop_id in

            let is_episodic =
              condition1.satisfied
              && condition2.satisfied
              && condition3.satisfied
              && condition4.satisfied
            in

            Lwt.return_some
              {
                loop_id;
                condition1;
                condition2;
                condition3;
                condition4;
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

        let symbolic_ctx =
          {
            ctx with
            options = { ctx.options with loop_semantics = Symbolic };
            structure = None;
            source_spans = None;
            fwd_es_ctx = None;
            justifications = None;
            executions = None;
            is_episodic = None;
          }
        in
          let* symbolic_ctx =
            Lwt.return symbolic_ctx
            |> Interpret.step_interpret
            |> Elaborations.step_generate_justifications
          in
          let symbolic_structure = Option.get symbolic_ctx.structure in
          let symbolic_source_spans = Option.get symbolic_ctx.source_spans in
          let symbolic_fwd_es_ctx = Option.get symbolic_ctx.fwd_es_ctx in
          let symbolic_justifications =
            Option.get symbolic_ctx.justifications
          in

          let cache =
            {
              program;
              symbolic_structure;
              symbolic_source_spans;
              symbolic_fwd_es_ctx;
              symbolic_justifications;
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
                      loop_episodicity_results :=
                        result :: !loop_episodicity_results;
                      Lwt.return_unit
                  | None ->
                      Logs.info (fun m -> m "Loop %d: Could not analyze" loop_id);
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
