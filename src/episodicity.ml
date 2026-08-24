(** {1 Episodicity Analysis Module}

    This module implements episodicity checks for loops based on Definition 4.1.
    A loop is episodic if it satisfies four conditions, named here as they are
    in the paper:

    + {b Register condition}: registers only accessed if written to ⊑-before
      within same iteration or before loop
    + {b Write condition}: reads must read from: (a) same-iteration writes, (b)
      cross-thread writes, or (c) read-don't-modify RMWs derived from such
      writes
    + {b Branching condition}: branching conditions don't constrain symbols read
      before the loop
    + {b Events condition}: events from prior iterations are ordered before
      later iterations by (ppo ∪ dp)*

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
  mutable structure : symbolic_event_structure;
      (** Event structure with symbolic loop semantics *)
  mutable source_spans : (int, source_span) Hashtbl.t;
      (** Source span mapping for symbolic events *)
  mutable fwd_es_ctx : Forwarding.event_structure_context;
      (** Forwarding context for symbolic event structure *)
  mutable justifications : justification list;
      (** Justifications for symbolic event structure *)
}

(** {1 Episodicity Conditions} *)

(** The four conditions of the {i Episodic Loops} definition, named as in the
    paper. The index of a condition is its position in the definition, and
    matches the [condition1] .. [condition4] fields of
    {!Context.loop_episodicity_result}. *)
type condition_kind =
  | RegisterConditionKind  (** Condition 1: register accesses *)
  | WriteConditionKind  (** Condition 2: sources a loop read may read from *)
  | BranchingConditionKind  (** Condition 3: what branching conditions pin *)
  | EventsConditionKind  (** Condition 4: ordering across iterations *)

(** The position of a condition in the definition.

    @param kind The condition.
    @return The condition's index, 1 to 4. *)
let condition_index = function
  | RegisterConditionKind -> 1
  | WriteConditionKind -> 2
  | BranchingConditionKind -> 3
  | EventsConditionKind -> 4

(** The condition at a given position in the definition.

    @param index The condition's index, 1 to 4.
    @return The condition, or [None] if the index names no condition. *)
let condition_of_index = function
  | 1 -> Some RegisterConditionKind
  | 2 -> Some WriteConditionKind
  | 3 -> Some BranchingConditionKind
  | 4 -> Some EventsConditionKind
  | _ -> None

(** The name of a condition as used in the paper.

    @param kind The condition.
    @return The condition's name. *)
let condition_name = function
  | RegisterConditionKind -> "register condition"
  | WriteConditionKind -> "write condition"
  | BranchingConditionKind -> "branching condition"
  | EventsConditionKind -> "events condition"

(** What a condition requires, phrased as in the paper.

    @param kind The condition.
    @return A one-sentence statement of the requirement. *)
let condition_statement = function
  | RegisterConditionKind ->
      "registers are only accessed if written ⊑-before within the same \
       iteration, or before the loop"
  | WriteConditionKind ->
      "reads within the loop read from a ⊑-earlier write of the same \
       iteration, a write before the loop, an independent write on another \
       thread, or a read-don't-modify-write derived from those"
  | BranchingConditionKind ->
      "the branching conditions of an iteration do not constrain values read \
       before the loop"
  | EventsConditionKind ->
      "events of prior iterations are ordered before events of later \
       iterations by (ppo ∪ dp)*"

(** A condition's name qualified by its index, e.g. ["branching condition (3)"].

    @param kind The condition.
    @return The name and index of the condition. *)
let describe_condition kind =
  Printf.sprintf "%s (%d)" (condition_name kind) (condition_index kind)

(** The conditions a result violates, in definition order.

    @param result A loop episodicity result.
    @return The kinds of the conditions that are not satisfied. *)
let violated_conditions (result : loop_episodicity_result) =
  List.filter_map
    (fun (kind, (condition : condition_result)) ->
      if condition.satisfied then None else Some kind
    )
    [
      (RegisterConditionKind, result.condition1);
      (WriteConditionKind, result.condition2);
      (BranchingConditionKind, result.condition3);
      (EventsConditionKind, result.condition4);
    ]

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

(** {1 Bisect Loops} *)

(** Loop bisection modifies the po and po_iter relations in event structures
    with symbolic loop semantics around a structure compatible bisection of the
    events under a given loop. The modification of po and po_iter simulates a
    refactoring of the loop body through a partial unravelling of the loop for
    the purpose of episodocity checks. *)
module Bisection = struct
  (** Perform loop bisection on the symbolic event structure for a given loop.

      This modifies the po and po_iter relations to reflect a refactoring of the
      loop body, simulating a partial unrolling of the loop. The events in the
      loop are partitioned into two sets (left and right), and the relations are
      updated to maintain consistency with this partitioning.

      @param structure The original symbolic event structure
      @param loop_id The identifier of the loop to bisect
      @param left The set of events in the left partition of the bisection
      @param right The set of events in the right partition of the bisection
      @return
        A new symbolic event structure with updated relations reflecting the
        bisection *)
  let bisect_loop structure loop_id left right =
    let { po; _ } = structure in
    let po =
      USet.set_minus po (URelation.cross left right)
      |> USet.union (URelation.cross right left)
    in
      { structure with po }

  (** Get the direct child loop ID of [evt_label] under [loop_id].

      Given an event's loop_indices list (a prefix-closed path of loop IDs),
      this returns the loop ID immediately following [loop_id] in that path, if
      any. This identifies which sub-loop group the event belongs to when
      bisecting at [loop_id].

      For example, if loop_indices for an event is [[1; 2; 3; 4]] and loop_id is
      2, this returns [Some 3], meaning the event is in the sub-loop group
      rooted at loop 3. If loop_indices is [[1; 2]] and loop_id is 2, this
      returns [None], meaning the event is directly in loop_id with no further
      nesting.

      @param loop_indices The loop_indices hashtable from the event structure
      @param evt_label The event label to look up
      @param loop_id The loop being bisected
      @return
        [Some child_loop_id] if event is nested under a child of loop_id, [None]
        if event is directly in loop_id *)
  let child_loop_of loop_indices evt_label loop_id =
    match Hashtbl.find_opt loop_indices evt_label with
    | None -> None
    | Some path ->
        let rec find_next = function
          | [] | [ _ ] -> None
          | x :: y :: _ when x = loop_id -> Some y
          | _ :: rest -> find_next rest
        in
          find_next path

  (** Check that each sub-loop group under [loop_id] is entirely on one side.

      Two events that share the same direct child loop under [loop_id] (i.e. are
      both in the same nested sub-loop) must not be split across [left] and
      [right]. Additionally, events directly in [loop_id] (child_loop = None)
      that share the same position in the loop_indices path must also not be
      split. This preserves the tree structure of nested loops: a sub-tree is
      either wholly left or wholly right.

      @param structure The symbolic event structure
      @param loop_id The loop being bisected
      @param left The proposed left partition
      @param right The proposed right partition
      @return [true] if no sub-loop group is split across left and right *)
  let nested_loops_unsplit structure loop_id left right =
    (* Build a map from child-loop-id -> (has_left, has_right).
       Only events that have a concrete child loop (Some child_id) are
       constrained: all events sharing the same child loop must be on
       the same side.  Events directly in loop_id with no further nesting
       (child = None) have no such constraint and are skipped. *)
    let group_sides : (int, bool * bool) Hashtbl.t = Hashtbl.create 8 in
    let record_side evt side =
      match child_loop_of structure.loop_indices evt loop_id with
      | None -> () (* directly in loop_id — no grouping constraint *)
      | Some child_id ->
          let l, r =
            try Hashtbl.find group_sides child_id
            with Not_found -> (false, false)
          in
          let updated =
            match side with
            | `Left -> (true, r)
            | `Right -> (l, true)
          in
            Hashtbl.replace group_sides child_id updated
    in
      USet.iter (fun evt -> record_side evt `Left) left;
      USet.iter (fun evt -> record_side evt `Right) right;
      (* A split group is one whose child loop appears on both sides *)
      Hashtbl.fold
        (fun _key (has_left, has_right) ok -> ok && not (has_left && has_right))
        group_sides true

  (** Check that no atomic read-modify-write is cut in half by the bisection.

      A bisection places an episode boundary inside the loop body, so the
      boundary has to fall between steps of the program. An RMW is one step: its
      read and its write cannot land in different episodes. Without this a
      rotation can carry the write of a CAS or a fetch-and-add into the next
      episode — not a boundary the source admits, and not one Condition 1 can be
      read against, since no rotation of the body expresses it.

      @param structure The symbolic event structure
      @param left The proposed left partition
      @param right The proposed right partition
      @return [true] if no RMW has its read in [left] and its write in [right]
  *)
  let rmw_unsplit (structure : symbolic_event_structure) left right =
    USet.values structure.rmw
    |> List.for_all (fun (read_event, _, write_event) ->
        not (USet.mem left read_event && USet.mem right write_event)
    )

  (** Generate all compatible bisections of the events in a loop.

      A bisection splits the loop's events so that every event of [left] is
      program-order before every event of [right]. That completeness is a severe
      constraint, and two facts follow from it.

      No two distinct splits of the same size can both be valid: if [x] were
      left in one and right in the other, and [y] the other way round, [x] and
      [y] would each have to be po-before the other. And a valid [left] of size
      [k] is exactly the events with fewer than [k] of the loop's events
      po-before them — an event of [left] has all its predecessors in [left], an
      event of [right] has all of [left] before it.

      So the candidates are the [|E|+1] prefixes of the events ranked by how
      many of the loop's events precede them, not the [2^|E|] subsets. That
      matters: the larger loop of hp-1 carries 48 events, because the loop body
      is duplicated across the branches of the loops around it, and
      materialising its power set is what made the analysis intractable. Nearly
      all of those subsets fail the first filter anyway — copies of a loop body
      under different branches conflict, so nothing can be split across them. *)
  let all_bisections structure loop_id =
    let events_in_loop = get_events_in_loop structure loop_id in
    let event_list = USet.to_list events_in_loop in
    let preceding event =
      List.length
        (List.filter
           (fun other -> USet.mem structure.po (other, event))
           event_list
        )
    in
    let ranked = List.map (fun event -> (preceding event, event)) event_list in
      List.init
        (List.length event_list + 1)
        (fun size ->
          ( size,
            ranked
            |> List.filter (fun (before, _) -> before < size)
            |> List.map snd
            |> USet.of_list
          )
        )
      |> List.filter (fun (size, left) -> USet.size left = size)
      |> List.map (fun (_, left) -> (left, USet.set_minus events_in_loop left))
      |> List.filter (fun (left, right) ->
          USet.subset (URelation.cross left right) structure.po
          && nested_loops_unsplit structure loop_id left right
          && rmw_unsplit structure left right
          && USet.size right > 0
      )
end

(** {1 Condition 1: Register Condition — Register Access Restriction
    (Syntactic)} *)

module RegisterCondition = struct
  (** Check if a register is written before it's read within a loop body.

      This implements Condition 1 of episodicity: registers are only accessed if
      they have been written to ⊑-before within the same iteration or before the
      loop starts.zR

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

  (** Every source span occurring in a node or in the nodes nested inside it.

      @param node The IR node.
      @return The spans of the node and of everything nested in it. *)
  let rec spans_of_node (node : ir_node) : source_span list =
    let nested =
      match node.stmt with
      | While { body; _ } | Do { body; _ } -> List.concat_map spans_of_node body
      | If { then_body; else_body; _ } ->
          List.concat_map spans_of_node then_body
          @ (else_body
            |> Option.value ~default:[]
            |> List.concat_map spans_of_node
            )
      | Labeled { stmt; _ } -> spans_of_node stmt
      | Threads { threads } ->
          List.concat_map (List.concat_map spans_of_node) threads
      | _ -> []
    in
      ( match node.annotations.source_span with
        | Some span -> [ span ]
        | None -> []
        )
      @ nested

  (** The loop body in the order a bisection rotates it into.

      A bisection puts the episode boundary inside the loop body: the events in
      [left] are the tail of the previous episode, so the iteration the
      bisection describes runs the statements after the boundary first and those
      before it after. Condition 1 is a property of statement order, so it has
      to be read against that order — checking it against source order while
      Conditions 2, 3 and 4 see the bisected [po] lets a rotation buy Condition
      2 without ever paying for it here.

      The boundary is located by source span: a statement lies before it if it
      owns an event of [left] belonging to this loop. A statement whose events
      straddle the boundary — only a read-modify-write can, its read on one side
      and its write on the other — is taken to lie before it, so such a
      bisection still rotates nothing here.

      @param source_spans The event-to-span table.
      @param events_in_loop The events of the loop being bisected.
      @param left The left partition of the bisection.
      @param body The loop body in source order.
      @return The body rotated to the bisection's iteration order. *)
  let rotate_body ~source_spans ~events_in_loop ~left (body : ir_node list) =
    let owns_left node =
      let spans = spans_of_node node in
        Hashtbl.fold
          (fun event span found ->
            found
            || List.mem span spans
               && USet.mem events_in_loop event
               && USet.mem left event
          )
          source_spans false
    in
    let _, boundary =
      List.fold_left
        (fun (index, boundary) node ->
          (index + 1, if owns_left node then index + 1 else boundary)
        )
        (0, 0) body
    in
    let rec split n before after =
      match after with
      | rest when n = 0 -> (List.rev before, rest)
      | [] -> (List.rev before, [])
      | node :: rest -> split (n - 1) (node :: before) rest
    in
    let before, after = split boundary [] body in
      after @ before

  (** Check Condition 1: Registers only accessed if written to ⊑-before.

      @param program The complete program as a list of IR nodes
      @param cache The episodicity cache (unused in this check)
      @param loop_id The identifier of the loop to check
      @return A condition result indicating satisfaction and any violations *)
  let check ?bisection cache (loop_id : int) : condition_result Lwt.t =
    let violations = ref [] in
    let satisfied = ref true in
    let { program; structure; source_spans; _ } = cache in
    let loop_nodes = find_loop_nodes program loop_id in
    let rotate body =
      match bisection with
      | None -> body
      | Some left ->
          let events_in_loop =
            SymbolicEventStructure.events_in_loop structure loop_id
          in
            rotate_body ~source_spans ~events_in_loop ~left body
    in
      List.iter
        (fun (node : ir_node) ->
          match node.stmt with
          | While { body; _ } | Do { body; _ } ->
              let result = check_register_accesses_in_loop (rotate body) in
                satisfied := !satisfied && result.satisfied;
                violations := result.violations @ !violations
          | _ -> ()
        )
        loop_nodes;
      Lwt.return { satisfied = !satisfied; violations = !violations }
end

(** {1 Condition 2: Write Condition — Memory Read Sources (Semantic)} *)

module WriteCondition = struct
  (** {2 Which way the aliasing question is asked}

      This condition reports a read that could take its value from a write of a
      previous iteration, which turns on whether the two are at the same
      location. Locations here are expressions over symbols, so "the same
      location" is a solver question, and there are two of them to ask.

      Possible equality — [Solver.expoteq], is [wloc = rloc] satisfiable —
      reports a pair whenever the program does not rule the aliasing out.
      Necessary equality — [Solver.exeq], is [wloc <> rloc] unsatisfiable —
      reports only where the aliasing is forced.

      The two are not interchangeable. The episodicity conditions are
      {e sufficient}: a loop that passes them is episodic, and the checker is
      read as a certificate. A pair not reported is a violation not found, so
      possible equality is the direction that keeps the certificate honest, and
      necessary equality is the direction that can call a loop episodic when it
      is not. That the loop {e might} carry a value across the boundary is
      already enough to disqualify it.

      Possible equality on its own is close to useless here, though. A location
      loaded out of memory is a free symbol, equal to anything as far as the
      solver is concerned, so every write in the loop is reported against every
      read through a pointer — on the CAS increment loop, a write to a freshly
      allocated node against a read of an entirely different cell.

      So the question stays the sound one and the imprecision is attacked
      directly, by {!may_read_from}: a symbol only holds an address because some
      write put it there, so ask which writes could have. That recovers the
      precision without giving up the direction. It costs a fixpoint over the
      structure rather than a single solver call, and it gives up nothing when
      it cannot resolve a symbol — it returns the plain aliasing answer.

      Two facts about allocations make it work, both asked of this query rather
      than recorded on the structure: distinct allocations are distinct
      addresses, and an allocation is not the 0 a program stores to mean "no
      allocation yet". Asserting the second over the whole verification is not
      harmless — it empties [cas_aba] and [rcu-inc-reclaim] of executions — so
      it is confined to the aliasing question, where it is what lets a write of
      a literal 0 be told apart from a write of a node.

      Both directions are pinned by tests in [test_episodicity.ml]: one loop
      whose aliasing is real but not forced, which necessary equality misses,
      and the CAS increment loop, which plain possible equality over-reports.
      Each fails under the other choice.

      There is a residual limit worth knowing. The condition asks about
      locations, not about read-from edges: it reports a write at a location a
      read could read, not a write that could actually justify that read under
      coherence. {!may_read_from} narrows the gap for addresses that arrive
      through memory; it does not close it. *)

  (** Get the origin event for a symbol.

      @param structure The symbolic event structure
      @param symbol The symbol name to look up
      @return The event label that introduced this symbol, if any *)
  let get_symbol_origin (structure : symbolic_event_structure) (symbol : string)
      : int option =
    Hashtbl.find_opt structure.origin symbol

  (** Whether a write's location can be the location a read reads from.

      [Solver.expoteq] asks only whether the two expressions {e can} be equal,
      and a location loaded out of memory is a free symbol that can be equal to
      anything — so on a program that reaches memory through pointers it says
      yes to almost every pair, and every write in the loop looks like a source
      for every read. Testing necessary equality instead would answer far fewer
      pairs, but in the unsound direction: a read that {e might} take its value
      from a previous iteration would stop being reported.

      So keep the possible-equality answer and sharpen it where the imprecision
      comes from. When the read's location is a symbol introduced by an earlier
      read, that symbol only holds an address because some write put the address
      there. Ask for such a write: one that can occur alongside this read, at
      the location the symbol was read from, carrying a value that can be the
      write's location.

      Every step falls back to the plain aliasing answer — an unresolvable
      symbol, a missing location, a write whose value is unknown — so ignorance
      never turns a possible alias into an impossible one.

      @param structure The symbolic event structure.
      @param sources The writes that can still be a source for a loop read.
      @param state Constraints the query is asked under.
      @param read_event The read whose location is [rloc].
      @param wloc The write's location.
      @param rloc The read's location.
      @return [true] if the write's location can be the read's. *)
  let may_read_from (structure : symbolic_event_structure) ~sources ~state
      read_event wloc rloc =
    (* A write can only be part of the execution that holds the read if the two
       do not conflict. *)
    let reachable write_event =
      not (USet.mem structure.conflict (write_event, read_event))
    in
    let rec symbol_can_be visited symbol =
      (* Revisiting a symbol adds no value it could not already take: this is
         the least fixpoint of "what can reach here", and a read-modify-write
         that stores back what it read is exactly such a cycle. *)
      (not (List.mem symbol visited))
      &&
      match Hashtbl.find_opt structure.origin symbol with
      | Some origin when USet.mem structure.read_events origin -> (
          match Events.get_loc structure origin with
          | Some origin_loc ->
              USet.exists
                (fun write_event ->
                  reachable write_event
                  &&
                  match
                    ( Events.get_loc structure write_event,
                      Events.get_val structure write_event
                    )
                  with
                  | Some write_loc, Some write_val ->
                      Solver.expoteq ~state write_loc origin_loc
                      && value_can_be (symbol :: visited) write_val
                  | _ -> true
                )
                sources
          | None -> true
        )
      | _ -> true
    and value_can_be visited value =
      match value with
      | ESymbol symbol when Hashtbl.mem structure.origin symbol ->
          symbol_can_be visited symbol
      | _ -> Solver.expoteq ~state value wloc
    in
      if Expr.equal wloc rloc then true
      else if not (Solver.expoteq ~state wloc rloc) then false
      else value_can_be [] rloc

  (** Check Condition 2: Reads must read from valid sources.

      Valid sources are:
      - Same-iteration writes (⊑-before the read)
      - Cross-thread writes
      - Read-don't-modify RMWs derived from such writes

      A write in the loop is a source for a read only if the two are at
      necessarily the same location; see the aliasing query below.

      @param cache The episodicity cache containing event structures
      @param loop_id The identifier of the loop to check
      @return
        A condition result (async) indicating satisfaction and any violations *)
  let check cache (loop_id : int) : condition_result Lwt.t =
    let { structure; source_spans; _ } = cache in
    let structure = structure in
    let events_in_loop =
      SymbolicEventStructure.events_in_loop structure loop_id
    in
    let reads_in_loop =
      USet.intersection events_in_loop structure.read_events
    in
    let writes_in_loop =
      USet.intersection events_in_loop structure.write_events
    in
      Logs_safe.debug (fun m ->
          let describe evt =
            Printf.sprintf "%d%s at %s" evt
              (if Events.is_rdmw structure evt then " (rdmw)" else "")
              (Events.get_loc structure evt
              |> Option.map show_expr
              |> Option.value ~default:"?"
              )
          in
          let list evts =
            USet.to_list evts
            |> List.sort compare
            |> List.map describe
            |> String.concat "; "
          in
            m "Loop %d: reads in loop [%s]; writes in loop [%s]." loop_id
              (list reads_in_loop) (list writes_in_loop)
      );
      (* Drop the writes that can only happen in a last iteration: with no
         iteration after them, no read of a later iteration can take its value
         from them, so they are not candidate sources.

         A write is kept when some enclosing loop can go round again after the
         iteration holding the write — an existential, because one further
         iteration of any enclosing loop is enough to produce a later read. The
         guards are those recorded at the end of the loop body, so they and the
         write's own restriction speak about the same iteration; a guard
         belonging to another occurrence of the loop simply fails to be
         satisfiable alongside that restriction.

         A loop with no recorded guard is kept, not dropped. Absence is not
         evidence of a last iteration: it says nothing about whether another
         iteration follows, and for a sufficient condition the safe reading is
         to leave the write in the candidate set. Dropping it instead empties
         the candidate set and makes the whole condition pass vacuously, which
         is how a missing guard turned into a soundness gap rather than a
         missing diagnosis. *)
      let* candidate_writes =
        USet.async_filter
          (fun write_event ->
            let enclosing_loops =
              Hashtbl.find_opt structure.loop_indices write_event
              |> Option.value ~default:[]
            in
            let unrecorded =
              enclosing_loops = []
              || List.exists
                   (fun lid -> not (Hashtbl.mem structure.loop_conditions lid))
                   enclosing_loops
            in
            let loop_conditions =
              enclosing_loops
              |> List.concat_map (fun lid ->
                  Hashtbl.find_opt structure.loop_conditions lid
                  |> Option.value ~default:[]
              )
            in
            let write_valres =
              Hashtbl.find_opt structure.restrict write_event
              |> Option.value ~default:[]
            in
            let can_continue =
              List.filter
                (fun expr -> Solver.is_sat (expr :: write_valres))
                loop_conditions
            in
              if unrecorded then
                Logs_safe.warn (fun m ->
                    m
                      "Loop %d: no continuation guard recorded for an \
                       enclosing loop of write %d; keeping it as a candidate \
                       source rather than treating it as a last-iteration \
                       write."
                      loop_id write_event
                );
              Lwt.return (unrecorded || List.length can_continue > 0)
          )
          writes_in_loop
      in
      (* Everything a loop read could still take its value from: every write in
         the structure, less the loop writes just ruled out as last-iteration
         ones. [may_read_from] asks this set whether an address could have
         reached a symbolic location. *)
      let sources =
        USet.set_minus structure.write_events
          (USet.set_minus writes_in_loop candidate_writes)
      in
      (* Asked of the aliasing query alone, not recorded on the structure: a
         program that stores 0 to mean "no allocation yet", as the CAS loops do,
         needs an allocation's address told apart from that 0, but asserting it
         over the whole verification changes which executions exist. *)
      let allocations_are_not_null =
        USet.to_list structure.malloc_events
        |> List.filter_map (Events.get_loc structure)
        |> List.map (fun loc -> Expr.binop loc "!=" (ENum Z.zero))
      in
      let writes_in_loop = candidate_writes in
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
                          (* Two locations count as one when they are
                             the read's location — see [may_read_from], which
                             keeps the possible-equality answer and sharpens it
                             by asking how an address could have reached a
                             symbolic location.

                             The query is asked under the structure's
                             constraints as well as the read's path condition:
                             those record what the program fixes about
                             locations — globals are pairwise distinct, and so
                             are distinct allocations. *)
                          let state =
                            (Hashtbl.find_opt structure.restrict read_event
                            |> Option.value ~default:[]
                            )
                            @ structure.constraints
                            @ allocations_are_not_null
                          in
                          let same_loc =
                            may_read_from structure ~sources ~state read_event
                              wloc rloc
                          in
                            if same_loc then
                              (* Only invalid if not a read-don't-modify RMW *)
                              Lwt.return
                                (not (Events.is_rdmw structure write_event))
                            else Lwt.return false
                      | _ -> Lwt.return false
                  )
                  writes_in_loop
              in
                Logs_safe.debug (fun m ->
                    let sources =
                      USet.to_list writes_in_loop_not_before_read
                      |> List.sort compare
                      |> List.map (fun w ->
                          Printf.sprintf "%d at %s" w
                            (Events.get_loc structure w
                            |> Option.map show_expr
                            |> Option.value ~default:"?"
                            )
                      )
                      |> String.concat "; "
                    in
                      m "Loop %d: read %d at %s may take its value from [%s]."
                        loop_id read_event
                        (Events.get_loc structure read_event
                        |> Option.map show_expr
                        |> Option.value ~default:"?"
                        )
                        sources
                );
                (* Record violations for invalid write sources *)
                USet.iter
                  (fun write_event ->
                    let violation =
                      WriteConditionViolation
                        (WriteFromPreviousIteration
                           ( Events.get_loc structure read_event
                             |> Option.map show_expr
                             |> Option.value ~default:"",
                             Hashtbl.find_opt source_spans read_event,
                             Hashtbl.find_opt source_spans write_event
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

(** {1 Condition 3: Branching Condition — Branch Condition Symbols (Syntactic
    and Origin Tracking)} *)

module BranchCondition = struct
  (** Check Condition 3: Branch conditions don't constrain pre-loop symbols.

      This ensures that branching conditions within the loop don't constrain
      symbols that were read before the loop started, maintaining iteration
      independence.

      {2 Jointly versus per branch}

      The definition asks this of the {e conjunction} of an iteration's
      branching conditions — [restrict(φ_ℓ, ∅) = ⊤] — not of each condition
      separately, because the property is not closed under conjunction: with a
      pre-loop [α] in [r0] and an in-loop [β] in [r1], [if (r1 = r0)] and a
      nested [if (r1 = 5)] each leave [α] free while together they force
      [α = 5].

      This checks each branching condition on its own, and is nonetheless at
      least as strong, because the test is syntactic rather than semantic. A
      symbol that the conjunction constrains must occur in some conjunct: if no
      condition mentions a pre-loop symbol then the conjunction mentions none,
      and a satisfiable formula entails nothing over symbols it does not
      mention. So flagging every condition that mentions a pre-loop symbol
      rejects everything the joint test rejects. The one assumption is that the
      conjunction is satisfiable — an unsatisfiable one entails everything — and
      the interpreter prunes unsatisfiable branches as it builds the structure.

      It rejects strictly more, though. A condition may mention a pre-loop
      symbol without constraining it: [if (r1 = r0)] on its own leaves [α] free,
      since [β] is, so the definition accepts a loop that this rejects. Deciding
      the definition exactly means asking [restrict(φ_ℓ, ∅) = ⊤] as a ∀∃ query
      over the conjunction — for every valuation of the pre-loop symbols, the
      conjunction is still satisfiable — rather than testing symbol occurrence.

      @param program The complete program as a list of IR nodes
      @param cache The episodicity cache containing event structures
      @param loop_id The identifier of the loop to check
      @return A condition result indicating satisfaction and any violations *)
  let check cache (loop_id : int) : condition_result Lwt.t =
    let { program; structure; source_spans; _ } = cache in
    let structure = structure in
      Logs_safe.debug (fun m ->
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
        Logs_safe.debug (fun m ->
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
            (* Occurrence, not constraint: sound but over-restrictive, and what
               makes the per-condition test cover the joint one. See above. *)
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
              Logs_safe.debug (fun m ->
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
                           Hashtbl.find_opt source_spans e
                         )
                      )
                  in
                    violations := violation :: !violations
                )
                symbols_read_before_loop
          )
          branch_events_in_loop;

        Lwt.return
          { satisfied = List.length !violations == 0; violations = !violations }
end

(** {1 Condition 4: Events Condition — Inter-iteration Ordering (Semantic)} *)

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
    let { structure; fwd_es_ctx; justifications; source_spans; _ } = cache in
    let structure = structure in
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
      let fwd_es_ctx = fwd_es_ctx in
      let ppo_rmw = ForwardingContext.compute_ppo_rmw fwd_es_ctx [] in
      let ppo =
        fwd_es_ctx.ppo.ppo_sync
        |> USet.union fwd_es_ctx.ppo.ppo_base
        |> USet.union fwd_es_ctx.ppo.ppo_loc_base
        |> USet.union fwd_es_ctx.ppo.ppo_base
      in
      let dp =
        List.fold_left
          (fun acc just ->
            Freeze.freeze_dp structure just |> USet.inplace_union acc
          )
          (USet.create ()) justifications
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
                     Hashtbl.find_opt source_spans e1,
                     Hashtbl.find_opt source_spans e2
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

(** Check if a specific bisection of a loop satisfies the episodicity
    conditions.

    This function takes a specific bisection of the loop's events and checks all
    four conditions for that bisection. It returns a detailed result indicating
    which conditions are satisfied and any violations found.

    @param ctx The Mordor context containing the program and analysis results
    @param cache The episodicity cache with precomputed structures
    @param loop_id The identifier of the loop to check
    @param left The set of events in the left partition of the bisection
    @param right The set of events in the right partition of the bisection
    @return A loop episodicity result indicating which conditions are satisfied
*)
let check_loop_bisection_episodicity (ctx : mordor_ctx) cache loop_id left right
    =
  let structure = Bisection.bisect_loop cache.structure loop_id left right in
  let ctx : mordor_ctx =
    {
      ctx with
      options = { ctx.options with loop_semantics = Symbolic };
      structure = Some structure;
      source_spans = None;
      fwd_es_ctx = None;
      justifications = None;
      executions = None;
      is_episodic = None;
    }
  in
    let* ctx = Lwt.return ctx |> Elaborations.step_generate_justifications in
    let fwd_es_ctx = Option.get ctx.fwd_es_ctx in
    let justifications = Option.get ctx.justifications in
    let cache = { cache with structure; fwd_es_ctx; justifications } in

    (* TODO generate new justifications and forwarding context for the
             bisection structure, or adapt the existing ones *)
    (* Log each condition by the name it carries in the paper, so a debug run
       reads as the definition does rather than as four opaque numbers. *)
    let check_condition kind check =
      Logs_safe.debug (fun m ->
          m "Loop %d: checking the %s — %s." loop_id (describe_condition kind)
            (condition_statement kind)
      );
      let* (result : condition_result) = check cache loop_id in
        Logs_safe.debug (fun m ->
            let violations = List.length result.violations in
            let verdict =
              if result.satisfied then "is satisfied"
              else
                Printf.sprintf "is violated (%d %s)" violations
                  (if violations = 1 then "violation" else "violations")
            in
              m "Loop %d: %s %s." loop_id (describe_condition kind) verdict
        );
        Lwt.return result
    in
      let* condition1 =
        check_condition RegisterConditionKind
          (RegisterCondition.check ~bisection:left)
      in
        let* condition2 =
          check_condition WriteConditionKind WriteCondition.check
        in
          let* condition3 =
            check_condition BranchingConditionKind BranchCondition.check
          in
            let* condition4 =
              check_condition EventsConditionKind EventsCondition.check
            in

            let is_episodic =
              condition1.satisfied
              && condition2.satisfied
              && condition3.satisfied
              && condition4.satisfied
            in

            (* Record the chosen bisection (the loop boundary) so the result can
             be related back to the program text. Events are sorted by label for
             a stable order, and annotated with their source span when known. *)
            let to_bisection_events evts =
              USet.to_list evts
              |> List.sort compare
              |> List.map (fun label ->
                  { label; span = Hashtbl.find_opt cache.source_spans label }
              )
            in

            Lwt.return
              {
                loop_id;
                condition1;
                condition2;
                condition3;
                condition4;
                is_episodic;
                bisection_left = to_bisection_events left;
                bisection_right = to_bisection_events right;
              }

(** Check if a specific loop is episodic by verifying all four conditions.

    This tests all bisections of the loop, starting from the trivial bisection
    without loop offset. The search terminates at the bisection with the least
    offset, i.e. the smallest left side, confirming episodicity.

    @param ctx The Mordor context containing the program
    @param cache The episodicity cache with precomputed structures
    @param loop_id The identifier of the loop to check
    @return An optional loop episodicity result, or None if analysis fails *)
let check_loop_episodicity (ctx : mordor_ctx) cache (loop_id : int) :
    loop_episodicity_result option Lwt.t =
  Bisection.all_bisections cache.structure loop_id
  |> Lwt_list.fold_left_s
       (fun acc (left, right) ->
         match (acc : loop_episodicity_result option) with
         | Some result when result.is_episodic -> Lwt.return (Some result)
         | _ ->
             let* result =
               check_loop_bisection_episodicity ctx cache loop_id left right
             in
               Lwt.return_some result
       )
       None

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
          let structure = Option.get symbolic_ctx.structure in
          let source_spans = Option.get symbolic_ctx.source_spans in
          let fwd_es_ctx = Option.get symbolic_ctx.fwd_es_ctx in
          let justifications = Option.get symbolic_ctx.justifications in

          let cache =
            { program; structure; source_spans; fwd_es_ctx; justifications }
          in

          let loop_episodicity_results = ref [] in

          (* Initialize episodicity table *)
          let is_episodic_table = Hashtbl.create 10 in

          (* Check each loop *)
          let* () =
            Lwt_list.iter_s
              (fun loop_id ->
                Logs_safe.info (fun m -> m "Analyzing Loop %d..." loop_id);
                let* episodic_result =
                  check_loop_episodicity symbolic_ctx cache loop_id
                in
                  match episodic_result with
                  | Some result ->
                      Logs_safe.info (fun m ->
                          let verdict =
                            match violated_conditions result with
                            | [] ->
                                "is episodic: register, write, branching and \
                                 events conditions all satisfied"
                            | violated ->
                                Printf.sprintf "is not episodic: %s violated"
                                  (violated
                                  |> List.map describe_condition
                                  |> String.concat ", "
                                  )
                          in
                            m "Loop %d %s." loop_id verdict
                      );
                      Hashtbl.add is_episodic_table loop_id result.is_episodic;
                      loop_episodicity_results :=
                        result :: !loop_episodicity_results;
                      Lwt.return_unit
                  | None ->
                      (* No compatible bisection of the loop's events exists —
                         typically because the loop contributes no events to the
                         symbolic event structure — so none of the four
                         conditions can be evaluated. *)
                      Logs_safe.info (fun m ->
                          m
                            "Loop %d: could not analyze — no compatible \
                             bisection of the loop's events, so the register, \
                             write, branching and events conditions were not \
                             evaluated."
                            loop_id
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
        Logs_safe.warn (fun m ->
            m "No program statements available for episodicity analysis"
        );
        Lwt.return ctx

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
