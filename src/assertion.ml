(** Assertion checking and refinement for symbolic memory model checking.

    This module implements validation of litmus test assertions against
    generated executions. It supports checking outcome assertions (allow/forbid
    with conditions), undefined behavior detection (use-after-free, unbounded
    pointer dereference), and refinement checking between programs. The module
    validates that executions satisfy specified conditions and memory model
    constraints. *)

open Context
open Events
open Eventstructures
open Executions
open Expr
open Ir
open Lwt.Syntax
open Lwt_utils
open Types
open Uset

(** {1 Assertion Result Type} *)

(** Result of checking an assertion against executions.

    Contains validity status, undefined behavior information, per-execution
    results for detailed analysis, and assertion instance tracking. *)
type assertion_result = {
  valid : bool;  (** Whether the assertion holds for all checked executions. *)
  ub : bool;  (** Whether any undefined behavior was detected. *)
  ub_reasons : ub_reason list;
      (** List of all undefined behavior instances found. *)
  checked_executions : execution_info list option;
      (** Per-execution results with satisfaction and UB status. *)
  assertion_instances : Context.assertion_instance list option;
      (** Detailed assertion instance tracking. *)
}

(** {1 Outcome Conversions} *)

(** [outcome_of_string s] converts string to outcome.

    @param s String representation ("allow" or "forbid").
    @return Corresponding outcome value.
    @raise Failure if string is invalid. *)
let outcome_of_string = function
  | "allow" -> Allow
  | "forbid" -> Forbid
  | s -> failwith ("Invalid outcome: " ^ s)

(** [string_of_outcome o] converts outcome to string.

    @param o The outcome.
    @return String representation. *)
let string_of_outcome = function
  | Allow -> "allow"
  | Forbid -> "forbid"

(** {1 Set Operations} *)

(** Set membership operations for assertions.

    Handles evaluation of assertions containing set membership tests like
    [(e1, e2) in .rf] which check if a pair exists in a relation. *)
module SetOperations = struct
  let is_set_operation = function
    | EBinOp (_, "in", _) | EBinOp (_, "notin", _) -> true
    | _ -> false

  (** [has_set_operation expr] checks if expression uses set operations.

      Recursively searches for ["in"] or ["notin"] operators.

      @param expr The expression to check.
      @return [true] if expression contains set membership tests. *)
  let rec has_set_operation expr =
    if is_set_operation expr then true
    else
      match expr with
      | EBinOp (e1, _, e2) -> has_set_operation e1 || has_set_operation e2
      | EUnOp (_, e) -> has_set_operation e
      | EOr lst -> List.exists has_set_operation lst
      | _ -> false

  (** [eval_tuple expr] evaluates tuple expression to event pair.

      Expects expression of form [(a, b)] where [a] and [b] are integers.

      @param expr Tuple expression.
      @return Pair of event IDs.
      @raise Failure if expression is not a valid tuple. *)
  let eval_tuple expr =
    match expr with
    | EBinOp (ENum a, ",", ENum b) -> (Z.to_int a, Z.to_int b)
    | _ -> failwith "Invalid tuple in set membership: expected (int, int)"

  (** [pair_in_execution execution (a, b)] tests whether both events are in the
      execution.

      A relation only relates events the execution contains, so a membership
      test naming an event it does not execute is asking about a pair that
      cannot be in any relation. Such an execution neither witnesses nor
      contradicts the test, and answering [(a, b) notin .dp] with [true] there
      would let it contradict a forbid it says nothing about.

      An event elided by forwarding or write elision is the exception, and it is
      the one the question is usually about. It {e was} executed -- the read
      happened and its value came from the write it was forwarded from -- and
      what the elision removed is exactly its dependency. Treating it as absent
      answers [(2,3) notin .dp] with [false] on the execution that demonstrates
      the dependency being dropped, which is the observation
      [avoidoota/listing10.lit] exists to make. [delta = fwd u we] is on the
      execution, so its right-hand side is the elided set.

      @param execution The execution.
      @param pair The event pair under test.
      @return [true] if both events are executed, elided or otherwise. *)
  let pair_in_execution (execution : symbolic_execution) (a, b) =
    let elided = USet.union execution.fwd execution.we |> URelation.pi_2 in
    let ran ev = USet.mem execution.e ev || USet.mem elided ev in
      ran a && ran b

  (** [eval_set_expr expr structure execution] evaluates set membership
      directly.

      Handles expressions like [(w,r) in .rf] by looking up the relation and
      checking membership. Supports boolean combinations.

      @param expr The set membership expression.
      @param structure The event structure.
      @param execution The execution.
      @return [true] if expression evaluates to true.
      @raise Failure if expression cannot be evaluated. *)
  let rec eval_set_expr expr structure execution =
    match expr with
    | EBinOp (tuple_expr, "in", EVar set_name) ->
        let pair = eval_tuple tuple_expr in
          pair_in_execution execution pair
          &&
          let rel = Execution.get_relation set_name structure execution in
            USet.mem rel pair
    | EBinOp (tuple_expr, "notin", EVar set_name) ->
        let pair = eval_tuple tuple_expr in
          pair_in_execution execution pair
          &&
          let rel = Execution.get_relation set_name structure execution in
            not (USet.mem rel pair)
    | EBinOp (e1, "&&", e2) ->
        eval_set_expr e1 structure execution
        && eval_set_expr e2 structure execution
    | EBinOp (e1, "||", e2) ->
        eval_set_expr e1 structure execution
        || eval_set_expr e2 structure execution
    | EUnOp ("!", e) -> not (eval_set_expr e structure execution)
    | _ -> true
end

(** {1 Assertion Instance Tracking} *)

(** Helper functions for tracking assertion instances and their details. *)
module AssertionInstanceTracking = struct
  (** [extract_set_memberships expr structure execution] extracts all set
      membership tests from an expression and their results.

      @param expr The expression to analyze.
      @param structure The event structure.
      @param execution The execution.
      @return List of set membership information. *)
  let rec extract_set_memberships expr structure execution =
    match expr with
    | EBinOp (tuple_expr, op, EVar set_name) when op = "in" || op = "notin" ->
        let pair = SetOperations.eval_tuple tuple_expr in
        let rel = Execution.get_relation set_name structure execution in
        let is_member = USet.mem rel pair in
        let result =
          SetOperations.pair_in_execution execution pair
          && if op = "in" then is_member else not is_member
        in
          [
            {
              Context.relation_name = set_name;
              event_pair = pair;
              member = result;
            };
          ]
    | EBinOp (e1, _, e2) ->
        extract_set_memberships e1 structure execution
        @ extract_set_memberships e2 structure execution
    | EUnOp (_, e) -> extract_set_memberships e structure execution
    | EOr lst ->
        List.concat_map
          (fun e -> extract_set_memberships e structure execution)
          lst
    | _ -> []

  (** [create_instance_detail expr structure execution result] creates detailed
      information about an assertion instance.

      @param expr Optional expression being evaluated.
      @param structure The event structure.
      @param execution The execution.
      @param result Whether the assertion held.
      @return Assertion instance detail record. *)
  let create_instance_detail expr_opt structure execution result =
    let instantiated_expr = expr_opt in
    let set_memberships =
      match expr_opt with
      | Some expr -> extract_set_memberships expr structure execution
      | None -> []
    in
      { Context.instantiated_expr; set_memberships; result }

  (** [create_witnessed exec_id detail] creates a witnessed assertion instance.

      @param exec_id Execution ID that witnessed the assertion.
      @param detail Details of what was witnessed.
      @return Witnessed assertion instance. *)
  let create_witnessed exec_id detail = Context.Witnessed { exec_id; detail }

  (** [create_contradicted exec_id detail] creates a contradicted assertion
      instance.

      @param exec_id Execution ID that contradicted the assertion.
      @param detail Details of the contradiction.
      @return Contradicted assertion instance. *)
  let create_contradicted exec_id detail =
    Context.Contradicted { exec_id; detail }
end

(** {1 JSON Serialization} *)

(** JSON serialization for undefined behavior reasons.

    Converts UB reasons to JSON format for reporting and analysis. *)
module JSONSerialization = struct
  (** Event pair type for JSON serialization. *)
  type event_pair = int * int [@@deriving yojson]

  (** JSON format for use-after-free violations. *)
  type uaf_json = { uaf : event_pair list } [@@deriving yojson]

  (** JSON format for unbounded pointer dereference violations. *)
  type upd_json = { upd : event_pair list } [@@deriving yojson]

  (** JSON union type for UB reasons. *)
  type ub_reason_json = UAF_json of uaf_json | UPD_json of upd_json
  [@@deriving yojson]

  (** [ub_reason_to_yojson ub_reason] converts UB reason to Yojson.

      @param ub_reason The UB reason to convert.
      @return Yojson representation. *)
  let ub_reason_to_yojson (ub_reason : ub_reason) : Yojson.Safe.t =
    match ub_reason with
    | UAF uaf_reasons ->
        let pairs = USet.fold (fun acc pair -> pair :: acc) uaf_reasons [] in
          uaf_json_to_yojson { uaf = pairs }
    | UPD upd_reasons ->
        let pairs = USet.fold (fun acc pair -> pair :: acc) upd_reasons [] in
          upd_json_to_yojson { upd = pairs }

  (** [ub_reason_to_json ub_reason] converts UB reason to JSON string.

      @param ub_reason The UB reason.
      @return JSON string. *)
  let ub_reason_to_json (ub_reason : ub_reason) : string =
    Yojson.Safe.to_string (ub_reason_to_yojson ub_reason)

  (** [ub_reasons_to_yojson ub_reasons] converts list to Yojson.

      @param ub_reasons List of UB reasons.
      @return Yojson list. *)
  let ub_reasons_to_yojson (ub_reasons : ub_reason list) : Yojson.Safe.t =
    `List (List.map ub_reason_to_yojson ub_reasons)

  (** [ub_reasons_to_json ub_reasons] converts list to JSON string.

      @param ub_reasons List of UB reasons.
      @return JSON string. *)
  let ub_reasons_to_json (ub_reasons : ub_reason list) : string =
    Yojson.Safe.to_string (ub_reasons_to_yojson ub_reasons)
end

(** {1 Event Location Helper} *)

(** [get_event_location structure execution event_label] extracts location
    symbol.

    Gets the location expression for an event, applies RF substitutions, and
    extracts the resulting symbol if unique.

    @param structure The event structure.
    @param execution The execution.
    @param event_label Event ID.
    @return [Some symbol] if location is a single symbol, [None] otherwise. *)
let get_event_location structure execution event_label =
  match get_loc structure event_label with
  | None -> None
  | Some loc_expr ->
      let substituted =
        Hashtbl.fold
          (fun var value acc -> Expr.subst acc var value)
          execution.fix_rf_map loc_expr
      in
      let symbols = Expr.get_symbols substituted in
        if List.length symbols = 1 then Some (List.hd symbols) else None

(** {1 Undefined Behavior Validation} *)

(** Undefined behavior detection.

    Checks for memory safety violations including use-after-free (UAF) and
    unbounded pointer dereference (UPD). Uses happens-before relation to
    determine if accesses are properly ordered relative to allocations/frees. *)
module UBValidation = struct
  (** [find_related_events pointer_symbol structure execution all_events] finds
      events using a pointer.

      Returns all events that access the same memory location as the given
      pointer symbol.

      @param pointer_symbol The pointer symbol to match.
      @param structure The event structure.
      @param execution The execution.
      @param all_events Set of events to search.
      @return Set of events accessing the pointer location. *)
  let find_related_events pointer_symbol structure execution all_events =
    USet.filter
      (fun e ->
        match get_event_location structure execution e with
        | Some loc_sym -> loc_sym = pointer_symbol
        | None -> false
      )
      all_events

  (** [find_events_not_before target_event happens_before events] finds
      unordered events.

      Returns events that don't happen-before the target event, meaning they
      could execute concurrently or after it.

      @param target_event The reference event.
      @param happens_before The happens-before relation.
      @param events Set of candidate events.
      @return Events not ordered before target. *)
  let find_events_not_before target_event happens_before events =
    USet.filter
      (fun e -> not (USet.mem happens_before (e, target_event)))
      events

  (** Use-after-free detection. *)
  module UAF = struct
    (** [check structure execution ub_reasons pointer_map rhb
         all_alloc_read_writes] detects use-after-free violations.

        For reads, this finds all rf-pairs where the read is reading from a
        free. This precisely pins down the read-after-free and helps discern the
        memory model, e.g. rc11 which does not admit as many uaf as smrd. For
        writes, this uses a pessimistic approximation where free-write pairs are
        identified which are not in rhb relation.

        @param structure The event structure.
        @param execution The execution.
        @param ub_reasons Mutable reference to accumulate UB instances.
        @param pointer_map Map from malloc events to symbols.
        @param rhb Happens-before relation.
        @param all_alloc_read_writes All pointer-related events. *)
    let check structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes =
      let all_frees = USet.intersection structure.free_events execution.e in
      let all_pointer_writes =
        all_alloc_read_writes |> USet.intersection structure.write_events
      in
      let all_pointer_reads =
        all_alloc_read_writes |> USet.intersection structure.read_events
      in
      let uaf =
        USet.fold
          (fun acc free ->
            (* Get the location symbol that was freed *)
            let free_loc_symbol =
              match get_event_location structure execution free with
              | Some sym -> sym
              | None -> ""
            in
            (* Find all events using the same location *)
            let related_events =
              find_related_events free_loc_symbol structure execution
                all_pointer_writes
            in
            (* Find events that DON'T happen before free (admits use-after-free) *)
            (* UAF is admitted when use is not ordered before free: (use, free) NOT in rhb *)
            let uaf_events = find_events_not_before free rhb related_events in
              (* Add all (free, use) pairs to accumulator *)
              USet.fold
                (fun acc2 use_event -> USet.add acc2 (free, use_event))
                uaf_events acc
          )
          all_frees (USet.create ())
        |> USet.union
             (USet.filter
                (fun (w, r) -> USet.mem structure.free_events w)
                execution.rf
             )
      in
        if USet.size uaf > 0 then ub_reasons := UAF uaf :: !ub_reasons
  end

  (** Unbounded pointer dereference detection. *)
  module UPD = struct
    (** [check structure execution ub_reasons pointer_map rhb
         all_alloc_read_writes] detects unbounded pointer dereferences.

        For each allocation, finds all dereferences of the same pointer that
        don't happen-after the allocation. These represent potential access to
        uninitialized or deallocated memory. UPD is admitted when: (alloc, use)
        NOT in happens-before.

        @param structure The event structure.
        @param execution The execution.
        @param ub_reasons Mutable reference to accumulate UB instances.
        @param pointer_map Map from malloc events to symbols.
        @param rhb Happens-before relation.
        @param all_alloc_read_writes All pointer-related events. *)
    let check structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes =
      let all_alloc = USet.intersection structure.malloc_events execution.e in
      let all_pointer_read_writes =
        USet.difference all_alloc_read_writes all_alloc
      in
      (* Find pointer dereferences that occur before allocation *)
      let upd =
        USet.fold
          (fun acc alloc ->
            (* Get the location symbol of the allocation *)
            match get_event_location structure execution alloc with
            | None -> acc
            | Some alloc_symbol ->
                let related_events =
                  find_related_events alloc_symbol structure execution
                    all_pointer_read_writes
                in
                (* Find events that DON'T happen after alloc (admits unbounded dereference) *)
                (* UPD is admitted when use is not ordered after alloc: (alloc, use) NOT in rhb *)
                let unbounded_events =
                  USet.filter
                    (fun e -> not (USet.mem rhb (alloc, e)))
                    related_events
                in
                  (* Add all (alloc, use) pairs to accumulator *)
                  USet.fold
                    (fun acc2 use_event -> USet.add acc2 (alloc, use_event))
                    unbounded_events acc
          )
          all_alloc (USet.create ())
      in
        if USet.size upd > 0 then ub_reasons := UPD upd :: !ub_reasons
  end

  (** [check_all structure execution ub_reasons pointer_map rhb
       all_alloc_read_writes] runs all UB checks.

      Executes both UAF and UPD detection on the execution, accumulating all
      violations in [ub_reasons].

      @param structure The event structure.
      @param execution The execution.
      @param ub_reasons Mutable reference to accumulate all UB instances.
      @param pointer_map Map from malloc events to symbols.
      @param rhb Happens-before relation.
      @param all_alloc_read_writes All pointer-related events. *)
  let check_all structure execution ub_reasons pointer_map rhb
      all_alloc_read_writes =
    UAF.check structure execution ub_reasons pointer_map rhb
      all_alloc_read_writes;
    UPD.check structure execution ub_reasons pointer_map rhb
      all_alloc_read_writes
end

(** {1 Execution Analysis} *)

(** Analysis utilities for executions.

    Builds derived relations and extracts information needed for assertion
    checking and UB detection. *)
module ExecutionAnalysis = struct
  (** [build_happens_before structure execution] constructs happens-before
      relation.

      Computes: rhb = (ppo ∪ fj ∪ dp ∪ rf)+ ∩ (E × E) Also adds reflexive edges
      for all events.

      @param structure The event structure.
      @param execution The execution.
      @return The reflexive, transitive happens-before relation. *)
  let build_happens_before structure execution =
    let rhb_base =
      USet.union
        (USet.union execution.ppo structure.fj)
        (USet.union execution.dp execution.rf)
    in
    let rhb_trans = URelation.transitive_closure rhb_base in
    (* Add reflexive edges: (e, e) for all e in e *)
    let rhb = USet.create () in
      USet.iter (fun e -> USet.add rhb (e, e) |> ignore) execution.e;
      USet.iter (fun edge -> USet.add rhb edge |> ignore) rhb_trans;
      rhb

  (** [extract_pointers structure execution] gets pointer info from mallocs.

      Extracts the location values from all malloc events in the execution.

      @param structure The event structure.
      @param execution The execution.
      @return Set of [(event_id, location_value)] pairs. *)
  let extract_pointers structure execution =
    USet.map
      (fun label ->
        ( label,
          get_loc structure label
          |> Option.map Expr.to_value
          |> Option.join
          |> Option.get
        )
      )
      (USet.intersection structure.malloc_events execution.e)

  (** [build_pointer_map pointers fix_rf_map] creates pointer symbol map.

      Builds a map from malloc event IDs to their symbolic location names after
      applying RF substitutions.

      @param pointers Set of [(event_id, value)] pairs from mallocs.
      @param fix_rf_map RF value substitution map.
      @return Hash table mapping event IDs to location symbols. *)
  let build_pointer_map pointers fix_rf_map =
    let pointer_map = Hashtbl.create (USet.size pointers) in
      USet.iter
        (fun (event_label, loc_value) ->
          let substituted =
            Hashtbl.fold
              (fun var value acc -> Expr.subst acc var value)
              fix_rf_map (Expr.of_value loc_value)
          in
          (* Extract symbol if it's a single symbol *)
          let symbols = Expr.get_symbols substituted in
            if List.length symbols = 1 then
              Hashtbl.add pointer_map event_label (List.hd symbols)
        )
        pointers;
      pointer_map

  (** [get_alloc_read_write_events structure execution pointer_map] finds
      pointer accesses.

      Returns all events (malloc, read, write) that access the locations
      identified by pointer symbols from malloc events.

      @param structure The event structure.
      @param execution The execution.
      @param pointer_map Map from malloc events to symbols.
      @return Set of all events accessing pointer locations. *)
  let get_alloc_read_write_events structure execution pointer_map =
    (* Get all pointer symbols from malloc events *)
    let pointer_symbols =
      Hashtbl.fold (fun _label symbol acc -> symbol :: acc) pointer_map []
      |> List.sort_uniq String.compare
    in

    (* Find all events (malloc, read, write) that access these pointer locations *)
    USet.filter
      (fun event_label ->
        match get_event_location structure execution event_label with
        | Some loc_sym -> List.mem loc_sym pointer_symbols
        | None -> false
      )
      execution.e

  (** [build_rf_conditions structure execution] creates RF equality constraints.

      For each read-from edge, creates constraints that the read value equals
      the written value, including any restrictions on the write.

      @param structure The event structure.
      @param execution The execution.
      @return List of RF-related constraints. *)
  let build_rf_conditions structure execution =
    let rf_conditions = ref [] in
      USet.iter
        (fun (write_id, read_id) ->
          let read_event = Hashtbl.find structure.events read_id in
          let read_rval =
            match read_event.rval with
            | Some rv -> rv
            | None -> VVar ("r" ^ string_of_int read_id)
          in
          let rf_value =
            let rval_str = Value.to_string read_rval in
              match Hashtbl.find_opt execution.fix_rf_map rval_str with
              | Some v -> v
              | None -> Expr.of_value read_rval
          in
          let restriction =
            match Hashtbl.find_opt structure.restrict write_id with
            | Some r -> r
            | None -> []
          in
          let equality = EBinOp (Expr.of_value read_rval, "=", rf_value) in
            rf_conditions := restriction @ [ equality ] @ !rf_conditions
        )
        execution.rf;
      !rf_conditions
end

(** {1 Condition Checking} *)

(** Condition evaluation for assertions.

    Handles both set membership expressions and regular boolean conditions,
    using appropriate evaluation strategies for each. *)
module ConditionChecker = struct
  (** [check_with_set_operations cond_expr rf_conditions structure execution]
      evaluates set membership conditions.

      Directly evaluates expressions like [(w,r) in .rf] by checking relation
      membership, then validates RF constraints with solver.

      @param cond_expr The condition expression.
      @param rf_conditions RF equality constraints.
      @param structure The event structure.
      @param execution The execution.
      @return Promise of [true] if condition holds. *)
  let check_with_set_operations cond_expr rf_conditions structure execution =
    try
      let set_result =
        SetOperations.eval_set_expr cond_expr structure execution
      in
        (* Still check rf_conditions with solver if needed *)
        if List.length rf_conditions > 0 then
          let rf_ok = Solver.is_sat rf_conditions in
            set_result && rf_ok
        else set_result
    with Failure msg ->
      Logs_safe.err (fun m -> m "Error evaluating set expression: %s" msg);
      false

  (** [check_with_solver cond_expr rf_conditions execution] uses SMT solver.

      Evaluates condition by substituting final register values and checking
      satisfiability with RF constraints.

      @param cond_expr The condition expression.
      @param rf_conditions RF equality constraints.
      @param execution The execution.
      @return Promise of [true] if satisfiable. *)
  let check_with_solver cond_expr rf_conditions structure execution =
    Logs_safe.debug (fun m ->
        m "Checking condition with solver: %s\n%s" (show_expr cond_expr)
          (show_symbolic_execution execution)
    );

    let cond_expr =
      Expr.evaluate_conjunction [ cond_expr ]
      |> List.filter (fun conjunct ->
          not (SetOperations.is_set_operation conjunct)
      )
    in

    let writes = Execution.get_writes_in_rhb_order structure execution in

    (* Registers first, so what is left naming a location really is one. *)
    let cond_after_registers =
      List.map (Expr.evaluate ~env:(Hashtbl.find_opt execution.final_env))
        cond_expr
    in

    (* The locations this condition asks about.  Every [EVar] the register
       substitution did not consume is one: [@x] is [EVar "x"] by the time it
       reaches here, and so is a bare global. *)
    let asked_locations =
      List.concat_map Expr.extract_variables cond_after_registers
      |> List.filter (fun v -> not (String.length v > 0 && v.[0] = '.'))
      |> List.sort_uniq String.compare
    in

    (* The memory state this execution ends in, for the locations asked about.

       [writes] is in rhb order, so replacing as we go leaves the last write to
       each location.  A write counts for a location when its own location
       expression *must* equal it under the execution's path predicates --
       [Solver.exeq], not [expoteq].  That is what carries aliasing: a write
       through a pointer has a symbolic location, and it lands on [x] exactly in
       those executions whose predicates pin the pointer to [x].  An execution
       that leaves the aliasing open is genuinely both cases and contributes
       nothing, which is the conservative answer.

       Before this, the match was [Some (EVar var)] and everything else was
       dropped, so a region reached through a pointer had no entry at all
       (github #5). *)
    let last_writes_to_variables = Hashtbl.create (List.length writes) in
      List.iter
        (fun w ->
          let event = Hashtbl.find structure.events w in
            match (event.loc, event.wval) with
            | Some (EVar var), Some wval ->
                Hashtbl.replace last_writes_to_variables var wval
            | Some loc, Some wval ->
                List.iter
                  (fun var ->
                    if Solver.exeq ~state:execution.ex_p loc (EVar var) then
                      Hashtbl.replace last_writes_to_variables var wval
                  )
                  asked_locations
            | _ -> ()
        )
        writes;
      let inst_cond_expr =
        List.map
          (Expr.evaluate ~env:(Hashtbl.find_opt last_writes_to_variables))
          cond_after_registers
      in
      (* The execution's own path predicates have to hold alongside the
         condition.  Asking the solver about the condition and the rf equalities
         alone leaves every register the rf edges do not pin free, so a
         condition the execution's values contradict still comes back sat. *)
      let query = inst_cond_expr @ rf_conditions @ execution.ex_p in
      let is_sat = Solver.is_sat query in
        Logs_safe.debug (fun m -> m "Solver result: %b" is_sat);
        is_sat

  (** [check_condition cond_expr structure execution] checks if condition holds.

      Dispatches to appropriate checker based on expression type.

      @param cond_expr The condition to check.
      @param structure The event structure.
      @param execution The execution.
      @return Promise of [true] if condition is satisfied. *)
  let check_condition cond_expr structure execution =
    let rf_conditions =
      ExecutionAnalysis.build_rf_conditions structure execution
    in
    let set_valid =
      check_with_set_operations cond_expr rf_conditions structure execution
    in
    let solver_valid =
      check_with_solver cond_expr rf_conditions structure execution
    in
      set_valid && solver_valid
end

(** {1 Refinement Checking} *)

(** Refinement checking between programs.

    Verifies that one program refines another by checking that every execution
    of the refined program can be matched with an execution of the original. *)
module Refinement = struct
  (** Result of refinement checking. *)
  type refinement_result = {
    structure : symbolic_event_structure;
        (** The refined program's structure. *)
    executions : symbolic_execution list;
        (** The refined program's executions. *)
    events : (int, event) Hashtbl.t;  (** Event table. *)
    valid : bool;  (** Whether refinement holds. *)
  }

  (** One program of a chain, run through the pipeline. *)
  type run = {
    run_structure : symbolic_event_structure;
    run_executions : symbolic_execution list;
    run_address_registers : string uset;
        (** Registers the program uses as addresses. *)
  }

  (** [address_registers program] names the registers a program uses as
      addresses: allocated by [malloc], taken as the address of a dereference,
      or freed.

      These are not observable behaviour. An allocation address is chosen by the
      allocator, so two runs that allocate at different addresses exhibit the
      same behaviour, and the address domain is unbounded -- enumerating it does
      not terminate. What a pointer points *at* is observed through the
      registers the program loads out of it, which are kept. *)
  let address_registers (program : Context.ir_node list) =
    let acc = USet.create () in
    let add_expr e =
      List.iter (fun v -> USet.add acc v |> ignore) (Expr.extract_variables e)
    in
    let rec walk_nodes nodes = List.iter walk_node nodes
    and walk_node (node : Context.ir_node) =
      match node.stmt with
      | Threads { threads } -> List.iter walk_nodes threads
      | If { then_body; else_body; _ } ->
          walk_nodes then_body;
          Option.iter walk_nodes else_body
      | While { body; _ } | Do { body; _ } -> walk_nodes body
      | Labeled { stmt; _ } -> walk_node stmt
      | RegMalloc { register; _ } -> USet.add acc register |> ignore
      | RegisterRefAssign { register; _ } -> USet.add acc register |> ignore
      | Free { register } -> USet.add acc register |> ignore
      | DerefLoad { address; _ } | DerefStore { address; _ } -> add_expr address
      | Cas { address; _ } | Fadd { address; _ } -> add_expr address
      | _ -> ()
    in
      walk_nodes program;
      acc

  (** How many distinct observations we are willing to enumerate for one
      execution before giving up. The refinement programs are small; a run that
      exceeds this is telling us the observable state is not finite enough to
      decide this way, and we say so rather than guess. *)
  let observation_cap = 512

  (** [run_program options litmus] runs one program of the chain through the
      pipeline and returns its structure and coherent executions.

      This is what was missing. [do_check_refinement] used to compare a hardcoded
      empty result against itself, so no program in the chain was ever
      interpreted (github #85). *)
  let run_program (options : Context.options) (litmus : Context.ir_litmus) =
    let ctx =
      Context.make_context
        { options with model = options.model }
        ~step_counter:options.step_counter ()
    in
      Option.iter (fun name -> ctx.litmus_name <- name) litmus.config.name;
      (* The model is the chain's, applied once by [do_check_refinement], not
         each program's own. Re-applying it here would reset [ubopt] from the
         chain's [UB11] back to the head program's "undefined". *)
      ctx.litmus_defacto <- Some litmus.config.defacto;
      ctx.litmus_constraints <- Some litmus.config.constraints;
      ctx.program_stmts <- Some litmus.program;
      (* No assertion: the chain's own outcome is what we are deciding, and
         [step_check_assertions] is not part of this pipeline anyway. *)
      ctx.assertions <- None;
      let%lwt ctx =
        Lwt.return ctx
        |> Interpret.step_interpret
        |> Elaborations.step_generate_justifications
        |> Executions.step_calculate_dependencies
      in
        match (ctx.structure, ctx.executions) with
        | Some structure, Some executions ->
            Lwt.return
              (Some
                 {
                   run_structure = structure;
                   run_executions = USet.to_list executions;
                   run_address_registers = address_registers litmus.program;
                 }
              )
        | _ ->
            Logs_safe.err (fun m ->
                m "Refinement: a program in the chain produced no executions"
            );
            Lwt.return None

  (** [allocations structure] pairs each allocation's address symbol with its
      index in program order.

      An allocation address is a symbol the model constrains only by
      distinctness, so its integer value is not observable behaviour and
      enumerating it does not terminate. What *is* observable is which
      allocation a register points at, and program order gives the two programs
      of a chain a correspondence between their allocations. *)
  let allocations (structure : symbolic_event_structure) =
    USet.values structure.malloc_events
    |> List.sort compare
    |> List.filteri (fun _ _ -> true)
    |> List.mapi (fun i label ->
        match Hashtbl.find_opt structure.events label with
        | Some { rval = Some addr; _ } -> Some (Expr.of_value addr, i)
        | _ -> None
    )
    |> List.filter_map Fun.id

  (** [observable_registers run] names the registers a run's executions end
      with.

      [final_env] is the register environment merged over the terminal events,
      so it is the program's observable state. *)
  let observable_registers run =
    List.fold_left
      (fun acc (exec : symbolic_execution) ->
        Hashtbl.fold (fun reg _ acc -> USet.add acc reg) exec.final_env acc
      )
      (USet.create ()) run.run_executions
    |> USet.filter (fun reg -> not (USet.mem run.run_address_registers reg))

  (** The name under which the solver reports register [reg]'s value.

      A fresh variable rather than the register's own symbolic expression, so
      that the model is guaranteed to bind it even when the execution's
      predicates leave the underlying symbols free. *)
  let obs_var reg = EVar ("$obs$" ^ reg)

  (** [observations structure exec regs] is the set of concrete observations
      [exec] admits, one per assignment of values to [regs].

      Returns [None] if the enumeration did not terminate within
      {!observation_cap} -- the caller must not read that as "no observations".

      Enumeration rather than a containment query, because a source execution's
      internal symbols would have to be existentially quantified to ask
      "is every observation of [t] an observation of some [s]" directly, and the
      solver interface here has no quantifiers. The programs are small enough
      that enumerating is exact. *)
  let observations structure (exec : symbolic_execution) regs =
    let rf_conditions =
      ExecutionAnalysis.build_rf_conditions structure exec
    in
    let value_of reg =
      Expr.evaluate ~env:(Hashtbl.find_opt exec.final_env) (EVar reg)
    in
    let bindings =
      List.map (fun reg -> (reg, EBinOp (obs_var reg, "=", value_of reg))) regs
    in
    let base = exec.ex_p @ rf_conditions @ List.map snd bindings in
    (* A register this execution pins to an allocation's address is reported by
       which allocation it is, not by the address's integer value. Both because
       the integer is not observable -- the allocator picks it -- and because
       leaving it to the enumeration below would not terminate: nothing bounds
       an address but distinctness from the other allocations. *)
    let allocs = allocations structure in
    let pinned, free =
      List.partition_map
        (fun reg ->
          let value = value_of reg in
            match
              List.find_opt
                (fun (addr, _) -> Solver.exeq ~state:base value addr)
                allocs
            with
            | Some (_, i) -> Left (reg, "@alloc" ^ string_of_int i)
            | None -> Right reg
        )
        regs
    in
    let regs = free in
    let rec loop acc blocked n =
      if n > observation_cap then (
        Logs_safe.err (fun m ->
            m
              "Refinement: execution %d still admits new observations after \
               %d; at least one of [%s] is unconstrained, so its behaviour \
               cannot be enumerated"
              exec.id observation_cap (String.concat "; " regs)
        );
        None
      )
      else
        match Solver.quick_solve (base @ blocked) with
        | None -> Some acc
        | Some _ when regs = [] ->
            (* Every observable is pinned to an allocation; that is the single
               observation, and there is nothing to enumerate. *)
            Some [ List.sort compare pinned ]
        | Some model ->
            let point =
              List.map
                (fun reg ->
                  (reg, Solver.concrete_value model ("$obs$" ^ reg))
                )
                regs
            in
              if List.exists (fun (_, v) -> Option.is_none v) point then (
                (* A register the model does not pin is not an observation we
                   can compare; treat the execution as undecidable rather than
                   inventing one. *)
                Logs_safe.err (fun m ->
                    m
                      "Refinement: execution %d leaves [%s] unbound, so its \
                       observation is not a value"
                      exec.id
                      (String.concat "; "
                         (List.filter_map
                            (fun (r, v) -> if Option.is_none v then Some r else None)
                            point
                         )
                      )
                );
                None
              )
              else
                let block =
                  EOr
                    (List.map
                       (fun (reg, v) ->
                         EBinOp
                           (obs_var reg, "!=", Expr.of_value (Option.get v))
                       )
                       point
                    )
                in
                let key =
                  List.map
                    (fun (reg, v) ->
                      (reg, Expr.to_string (Expr.of_value (Option.get v)))
                    )
                    point
                  @ pinned
                  |> List.sort compare
                in
                  loop (key :: acc) (block :: blocked) (n + 1)
    in
      loop [] [] 0

  (** [run_observations run regs] is every observation the run admits, or [None]
      if any execution could not be enumerated. *)
  let run_observations run regs =
    List.fold_left
      (fun acc exec ->
        match acc with
        | None -> None
        | Some seen -> (
            match observations run.run_structure exec regs with
            | None -> None
            | Some points -> Some (List.rev_append points seen)
          )
      )
      (Some []) run.run_executions

  (** [check_refinement source target] holds when every observation of [target]
      is an observation of [source].

      That is refinement in the usual sense: the transformation may remove
      behaviours, never introduce one. The observable interface is the registers
      the two programs have in common; a register only one of them has is
      internal to it and says nothing about the pair. *)
  let check_refinement source target =
    let source_regs = observable_registers source in
    let target_regs = observable_registers target in
    let regs =
      USet.union source_regs target_regs |> USet.values
      |> List.sort String.compare
    in
    let only_in name a b =
      USet.filter (fun r -> not (USet.mem b r)) a
      |> USet.values |> List.sort String.compare
      |> function
      | [] -> None
      | rs -> Some (name ^ ": " ^ String.concat ", " rs)
    in
      Logs_safe.info (fun m ->
          m "Refinement: comparing on %d observable register(s): [%s]"
            (List.length regs) (String.concat "; " regs)
      );
      (* The two programs have to end in the same registers to be comparable at
         all. Taking the intersection instead would make two programs with no
         register in common refine each other vacuously, which is the same shape
         of empty verdict github #85 is about. *)
      match
        List.filter_map Fun.id
          [
            only_in "only in the source" source_regs target_regs;
            only_in "only in the target" target_regs source_regs;
          ]
      with
      | _ :: _ as diffs ->
          Logs_safe.info (fun m ->
              m
                "Refinement: the programs do not end in the same registers                  (%s), so the target has a behaviour the source has not"
                (String.concat "; " diffs)
          );
          Some false
      | [] -> (
      match
        (run_observations source regs, run_observations target regs)
      with
      | Some source_points, Some target_points ->
          let source_set =
            List.map
              (fun p ->
                String.concat ","
                  (List.map (fun (r, v) -> r ^ "=" ^ v) p)
              )
              source_points
            |> List.sort_uniq String.compare
          in
          let missing =
            List.filter
              (fun p ->
                let key =
                  String.concat ","
                    (List.map (fun (r, v) -> r ^ "=" ^ v) p)
                in
                  not (List.mem key source_set)
              )
              target_points
          in
            List.iter
              (fun p ->
                Logs_safe.info (fun m ->
                    m "Refinement: target behaviour not in source: %s"
                      (String.concat ", "
                         (List.map (fun (r, v) -> r ^ " = " ^ v) p)
                      )
                )
              )
              missing;
            Some (missing = [])
      | _ ->
          Logs_safe.err (fun m ->
              m
                "Refinement: could not enumerate the observable behaviours \
                 (cap %d); the chain is not decided"
                observation_cap
          );
          None
      )

  (** [collect_chain acc ast] collects programs in chained assertion.

      Recursively extracts all programs from a chained refinement assertion.

      @param acc Accumulator for collected ASTs.
      @param ast Current AST.
      @return List of all ASTs in refinement chain. *)
  let rec collect_chain acc ast =
    match ast.assertions with
    | Chained { rest; _ } :: _ -> collect_chain (ast :: acc) rest
    | _ -> List.rev (ast :: acc)

  (** [chain_outcomes ast] is the outcome asserted at each link of the chain.

      A chain [p1 ~~>[o1] p2 ~~>[o2] p3] carries its own outcome at every arrow,
      and each is about the pair it sits between. The previous code read only
      the first. *)
  let rec chain_outcomes ast =
    match ast.assertions with
    | Chained { outcome; rest; _ } :: _ -> outcome :: chain_outcomes rest
    | _ -> []

  (** [do_check_refinement options ast] decides a chained refinement assertion.

      Each program in the chain is run through the pipeline and compared with
      its predecessor. A link asserting [allow] passes when the refinement
      holds, one asserting [forbid] when it does not.

      @param options The analysis options to run each program under.
      @param ast The litmus test AST with chained assertions.
      @return Promise of refinement result. *)
  let do_check_refinement (options : Context.options) ast =
    let tests = collect_chain [] ast in
    let outcomes = chain_outcomes ast in
    (* A chain names its model on the arrow -- [%% ~~> [UB11=allow] %%] -- and
       [step_parse_litmus] only applies the model of an [Outcome] or a [Model]
       assertion, so a chain's never reached the options. [UB11] in particular
       gates the [e / !r -> e] rewrite that its own tests are about. *)
    let options =
      match ast.assertions with
      | Chained { model; _ } :: _ when model <> "" ->
          let probe = Context.make_context { options with model } () in
            Context.apply_model_options probe model;
            probe.options
      | _ -> options
    in
    let%lwt runs = Lwt_list.map_s (run_program options) tests in
      match
        List.fold_left
          (fun acc r -> match (acc, r) with Some xs, Some x -> Some (x :: xs) | _ -> None)
          (Some []) runs
      with
      | None ->
          Logs_safe.err (fun m ->
              m "Refinement: chain not decided, a program produced no executions"
          );
          Lwt.return
            {
              structure = SymbolicEventStructure.create ();
              executions = [];
              events = Hashtbl.create 0;
              valid = false;
            }
      | Some rev_runs ->
          let runs = List.rev rev_runs in
          let last = List.nth runs (List.length runs - 1) in
          let rec walk rs os all_pass =
            match (rs, os) with
            | source :: (target :: _ as rest), outcome :: os' ->
                let holds = check_refinement source target in
                let link_pass =
                  match holds with
                  | None -> false
                  | Some h -> h = (outcome = Allow)
                in
                  Logs_safe.info (fun m ->
                      m "Refinement link: holds=%s asserted=%s -> %b"
                        (match holds with
                         | None -> "undecided"
                         | Some h -> string_of_bool h)
                        (match outcome with Allow -> "allow" | Forbid -> "forbid")
                        link_pass
                  );
                  walk rest os' (all_pass && link_pass)
            | _ -> all_pass
          in
          let all_pass = walk runs outcomes true in
            Lwt.return
              {
                structure = last.run_structure;
                executions = last.run_executions;
                events = last.run_structure.events;
                valid = all_pass;
              }
end

(** {1 Per-Execution Assertion Checking} *)

(** Checking assertions against individual executions.

    Evaluates conditions and detects UB for a single execution. *)
module PerExecutionChecker = struct
  (** [should_skip_condition already_satisfied is_ub_assertion] checks if skip.

      Skips condition checking if already satisfied or for UB-only assertions.

      @param already_satisfied Whether condition already holds.
      @param is_ub_assertion Whether this is a UB assertion.
      @return [true] if condition checking should be skipped. *)
  let should_skip_condition already_satisfied is_ub_assertion =
    already_satisfied || is_ub_assertion

  (** [check_outcome_assertion outcome condition structure execution
       already_satisfied] checks assertion on execution.

      Evaluates both the condition and runs UB detection for an execution.
      Returns assertion instance detail.

      @param outcome Expected outcome (Allow/Forbid).
      @param condition Condition to check.
      @param structure The event structure.
      @param execution The execution.
      @param already_satisfied Mutable reference tracking satisfaction.
      @return Promise of [(satisfied, ub_reasons, instance_detail_opt)] tuple.
  *)
  let check_outcome_assertion outcome condition structure execution
      already_satisfied =
    (* Determine if this is a UB assertion *)
    let is_ub_assertion =
      match condition with
      | Ir.CondUB -> true
      | Ir.CondExpr _ -> false
    in

    (* Extract condition expression if present *)
    let condition_expr_opt =
      match condition with
      | Ir.CondUB -> None
      | Ir.CondExpr expr -> Some expr
    in

    (* Build execution analysis components *)
    let rhb = ExecutionAnalysis.build_happens_before structure execution in
    let pointers = ExecutionAnalysis.extract_pointers structure execution in
    let pointer_map =
      ExecutionAnalysis.build_pointer_map pointers execution.fix_rf_map
    in
    let all_alloc_read_writes =
      ExecutionAnalysis.get_alloc_read_write_events structure execution
        pointer_map
    in

    (* Check for undefined behavior *)
    let ub_reasons = ref [] in
      UBValidation.check_all structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes;

      (* Check condition if needed *)
      if should_skip_condition !already_satisfied is_ub_assertion then
        (!already_satisfied, !ub_reasons, None)
      else
        match condition_expr_opt with
        | None -> failwith "Unexpected missing condition expression"
        | Some cond_expr ->
            let conds_satisfied =
              ConditionChecker.check_condition cond_expr structure execution
            in
            (* Check extended assertions (currently always true) *)
            let extended_ok = true in
            let final_satisfied = conds_satisfied && extended_ok in
              already_satisfied := final_satisfied;
              (* Create instance detail *)
              let detail =
                AssertionInstanceTracking.create_instance_detail
                  (Some cond_expr) structure execution final_satisfied
              in
                (!already_satisfied, !ub_reasons, Some detail)

  (** [check assertion execution structure already_satisfied ~exhaustive] checks
      single execution.

      @param assertion The assertion to check.
      @param execution The execution.
      @param structure The event structure.
      @param already_satisfied Mutable reference for satisfaction tracking.
      @param exhaustive Whether checking exhaustively.
      @return Promise of [(satisfied, ub_reasons, instance_detail_opt)] tuple.
      @raise Failure if assertion type is unexpected. *)
  let check assertion execution structure already_satisfied ~exhaustive =
    match assertion with
    | Outcome { outcome; condition; model } ->
        check_outcome_assertion outcome condition structure execution
          already_satisfied
    | _ -> failwith "unexpected assertion to be checked per execution"
end

(** {1 Main Assertion Checking} *)

(** Main assertion checking logic.

    Coordinates checking assertions across all executions, combining results and
    determining overall validity. *)
module AssertionChecker = struct
  (** [empty_result ?valid ()] creates empty assertion result.

      @param valid Optional validity value (default: true).
      @return Empty assertion result. *)
  let empty_result ?(valid = true) () =
    {
      valid;
      ub = false;
      ub_reasons = [];
      checked_executions = None;
      assertion_instances = None;
    }

  (** [run_ub_validation_on_execution structure execution] validates one
      execution.

      @param structure The event structure.
      @param execution The execution.
      @return List of UB reasons found. *)
  let run_ub_validation_on_execution structure execution =
    let rhb = ExecutionAnalysis.build_happens_before structure execution in
    let pointers = ExecutionAnalysis.extract_pointers structure execution in
    let pointer_map =
      ExecutionAnalysis.build_pointer_map pointers execution.fix_rf_map
    in
    let all_alloc_read_writes =
      ExecutionAnalysis.get_alloc_read_write_events structure execution
        pointer_map
    in
    let ub_reasons = ref [] in
      UBValidation.check_all structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes;
      !ub_reasons

  (** [run_ub_validation_all executions structure] validates all executions.

      @param executions List of executions.
      @param structure The event structure.
      @return Promise of [(all_ub_reasons, execution_results)] pair. *)
  let run_ub_validation_all executions structure =
    let all_ub_reasons = ref [] in
    let execution_results = ref [] in
    let%lwt () =
      lwt_piter
        (fun execution ->
          let ub_reasons = run_ub_validation_on_execution structure execution in
            all_ub_reasons := ub_reasons @ !all_ub_reasons;
            execution_results :=
              { exec_id = execution.id; satisfied = false; ub_reasons }
              :: !execution_results;
            Lwt.return ()
        )
        executions
    in
      Lwt.return (!all_ub_reasons, !execution_results)

  (** [check_model_assertion model executions structure] checks model assertion.

      For model-only assertions, just runs UB validation.

      @param model The memory model name.
      @param executions List of executions.
      @param structure The event structure.
      @return Promise of assertion result. *)
  let check_model_assertion model executions structure =
    Logs_safe.info (fun m -> m "Using memory model: %s" model);
    (* Run UB validation even for model assertions *)
    let%lwt ub_reasons, execution_results =
      run_ub_validation_all executions structure
    in
    let ub = List.length ub_reasons > 0 in
      Lwt.return
        {
          valid = true;
          ub;
          ub_reasons = List.rev ub_reasons;
          checked_executions = Some execution_results;
          assertion_instances = None;
        }

  (** [handle_no_executions exhaustive outcome] handles empty execution list.

      @param exhaustive Whether checking exhaustively.
      @param outcome Expected outcome.
      @return [Some result] if handled, [None] to continue.
      @raise Failure if exhaustive and no executions. *)
  let handle_no_executions exhaustive outcome =
    if exhaustive then Lwt.fail_with "No executions"
    else if outcome = Forbid then Lwt.return (Some (empty_result ()))
    else Lwt.return None

  (** [process_executions assertion executions structure] checks all executions.

      @param assertion The assertion to check.
      @param executions List of executions.
      @param structure The event structure.
      @return
        Promise of [(satisfied, ub_reasons, results, instances)] quadruple. *)
  let process_executions assertion executions structure =
    let ub_reasons = ref [] in
    let satisfied = ref false in
    let execution_results = ref [] in
    let assertion_instances = ref [] in

    (* Extract outcome from assertion *)
    let outcome =
      match assertion with
      | Outcome { outcome; _ } -> outcome
      | _ -> Allow
    in

    let%lwt () =
      lwt_piter
        (fun execution ->
          let exec_satisfied, local_ub_reasons, detail_opt =
            PerExecutionChecker.check assertion execution structure satisfied
              ~exhaustive:true
          in
            ub_reasons := local_ub_reasons @ !ub_reasons;
            execution_results :=
              {
                exec_id = execution.id;
                satisfied = exec_satisfied;
                ub_reasons = local_ub_reasons;
              }
              :: !execution_results;

            (* Track assertion instance only for executions that witness/contradict *)
            ( match detail_opt with
            | Some detail ->
                if outcome = Allow && exec_satisfied then
                  (* Allow assertion witnessed by this execution *)
                  let instance =
                    AssertionInstanceTracking.create_witnessed execution.id
                      detail
                  in
                    assertion_instances := instance :: !assertion_instances
                else if outcome = Forbid && exec_satisfied then
                  (* Forbid assertion contradicted by this execution *)
                  let instance =
                    AssertionInstanceTracking.create_contradicted execution.id
                      detail
                  in
                    assertion_instances := instance :: !assertion_instances
                  (* Otherwise: execution doesn't witness/contradict, don't track it *)
            | None ->
                (* For UB assertions (detail_opt is None), create instances based
                   on UB presence so the UI can navigate to the execution graph. *)
                if local_ub_reasons <> [] then
                  let detail =
                    AssertionInstanceTracking.create_instance_detail None
                      structure execution true
                  in
                    if outcome = Allow then
                      (* allow (ub) witnessed by this UB execution *)
                      let instance =
                        AssertionInstanceTracking.create_witnessed execution.id
                          detail
                      in
                        assertion_instances := instance :: !assertion_instances
                    else
                      (* forbid (ub) contradicted by this UB execution *)
                      let instance =
                        AssertionInstanceTracking.create_contradicted
                          execution.id detail
                      in
                        assertion_instances := instance :: !assertion_instances
            );

            Lwt.return ()
        )
        executions
    in

    Lwt.return
      (!satisfied, !ub_reasons, !execution_results, !assertion_instances)

  (** [compute_validity outcome is_ub_assertion satisfied expected ub]
      determines final validity.

      @param outcome Expected outcome.
      @param is_ub_assertion Whether UB assertion.
      @param satisfied Whether condition satisfied.
      @param expected Expected satisfaction value.
      @param ub Whether UB detected.
      @return Final validity result. *)
  let compute_validity outcome is_ub_assertion satisfied expected ub =
    if is_ub_assertion then
      (* For "allow (ub)", valid if UB found; for "forbid (ub)", valid if no UB *)
      ub = (outcome = Allow)
    else
      (* For regular assertions, check if condition was satisfied *)
      satisfied = expected

  (** [check_outcome_assertion outcome condition model executions structure
       ~exhaustive] checks outcome assertion.

      @param outcome Expected outcome (Allow/Forbid).
      @param condition Condition to check.
      @param model Optional memory model.
      @param executions List of executions.
      @param structure The event structure.
      @param exhaustive Whether checking exhaustively.
      @return Promise of assertion result. *)
  let check_outcome_assertion outcome condition model executions structure
      ~exhaustive =
    Logs_safe.info (fun m ->
        m "Checking assertion: %s (%s)"
          (string_of_outcome outcome)
          ( match condition with
          | Ir.CondUB -> "ub"
          | Ir.CondExpr expr -> Expr.to_string expr
          )
    );

    let is_ub_assertion =
      match condition with
      | Ir.CondUB -> true
      | Ir.CondExpr _ -> false
    in

    (* Short-circuit only when there are truly no executions to process.  Any
       assertion with executions in hand has to visit them: a forbid is
       contradicted by an execution satisfying its condition, and visiting the
       executions is the only way Witnessed / Contradicted instances get
       synthesised. *)
    let%lwt early_result =
      if executions = [] then handle_no_executions exhaustive outcome
      else Lwt.return None
    in

    match early_result with
    | Some result -> Lwt.return result
    | None ->
        let expected = outcome = Allow in

        (* Process all executions *)
        let%lwt satisfied, ub_reasons, execution_results, assertion_instances =
          process_executions
            (Outcome { outcome; condition; model })
            executions structure
        in

        (* Compute final result *)
        let ub = List.length ub_reasons > 0 in
        let valid =
          compute_validity outcome is_ub_assertion satisfied expected ub
        in

        Logs_safe.info (fun m -> m "Assertion result: valid=%b, ub=%b" valid ub);

        Lwt.return
          {
            valid;
            ub;
            ub_reasons = List.rev ub_reasons;
            checked_executions = Some execution_results;
            assertion_instances = Some assertion_instances;
          }

  (** [check_chained_assertion model outcome rest executions structure] checks
      chained refinement.

      @param model Optional memory model.
      @param outcome Expected outcome.
      @param rest Rest of refinement chain.
      @param executions List of executions.
      @param structure The event structure.
      @return Promise of assertion result. *)
  let check_chained_assertion ~options ~program ~config model outcome rest
      executions structure =
    Logs_safe.info (fun m ->
        m "Performing refinement check for chained assertion"
    );

    (* Run UB validation on all executions *)
    let%lwt ub_reasons, execution_results =
      run_ub_validation_all executions structure
    in
    let ub = List.length ub_reasons > 0 in

    (* The head of the chain is the program this context already ran, so hand
       [do_check_refinement] the real thing rather than the empty placeholder
       it used to build. Without the program and its config the first link had
       nothing to compare against. *)
    let%lwt result =
      Refinement.do_check_refinement options
        {
          config;
          program;
          assertions = [ Chained { model; outcome; rest } ];
        }
    in
      Lwt.return
        {
          valid = result.valid;
          ub;
          ub_reasons = List.rev ub_reasons;
          checked_executions = Some execution_results;
          assertion_instances = None;
        }

  (** [check assertion executions structure ~exhaustive] main checking function.

      Dispatches to appropriate checker based on assertion type.

      @param assertion The assertion to check.
      @param executions List of executions.
      @param structure The event structure.
      @param exhaustive Whether to check exhaustively.
      @return Promise of assertion result. *)
  let check ?ctx assertion executions structure ~exhaustive =
    match assertion with
    | Model { model } -> check_model_assertion model executions structure
    | Outcome { outcome; condition; model } ->
        check_outcome_assertion outcome condition model executions structure
          ~exhaustive
    | Chained { model; outcome; rest } -> (
        (* A chain needs the source program itself, which only the context has.
           Without one there is nothing to compare and we say so, rather than
           returning a verdict read off the allow/forbid keyword (github #85). *)
        match ctx with
        | None ->
            Logs_safe.err (fun m ->
                m
                  "Refinement assertion reached the checker without a                    context; the chain cannot be decided"
            );
            Lwt.return
              {
                valid = false;
                ub = false;
                ub_reasons = [];
                checked_executions = None;
                assertion_instances = None;
              }
        | Some (ctx : mordor_ctx) ->
            check_chained_assertion ~options:ctx.options
              ~program:(Option.value ctx.program_stmts ~default:[])
              ~config:
                {
                  name = Some ctx.litmus_name;
                  model = None;
                  values = [];
                  defacto = Option.value ctx.litmus_defacto ~default:[];
                  constraints =
                    Option.value ctx.litmus_constraints ~default:[];
                }
              model outcome rest executions structure
      )
end

(** {1 Public API} *)

(** [check_assertion assertion executions structure ~exhaustive] checks
    assertion.

    Main entry point for assertion checking.

    @param assertion The assertion to validate.
    @param executions List of symbolic executions.
    @param structure The symbolic event structure.
    @param exhaustive Whether to check exhaustively.
    @return Promise of assertion result. *)
let check_assertion = AssertionChecker.check

(** JSON serialization functions for UB reasons. *)

(** [ub_reason_to_yojson ub] converts UB reason to Yojson. *)
let ub_reason_to_yojson = JSONSerialization.ub_reason_to_yojson

(** [ub_reason_to_json ub] converts UB reason to JSON string. *)
let ub_reason_to_json = JSONSerialization.ub_reason_to_json

(** [ub_reasons_to_yojson ubs] converts UB reason list to Yojson. *)
let ub_reasons_to_yojson = JSONSerialization.ub_reasons_to_yojson

(** [ub_reasons_to_json ubs] converts UB reason list to JSON string. *)
let ub_reasons_to_json = JSONSerialization.ub_reasons_to_json

(** [step_check_assertions ctx] checks assertions in verification context.

    Pipeline step that validates assertions against generated executions. Always
    runs UB detection, even without explicit assertions.

    @param ctx The verification context (as promise).
    @return Updated context with assertion results. *)
let step_check_assertions (ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let%lwt ctx = ctx in
    match (ctx.structure, ctx.executions) with
    | Some structure, Some executions ->
        let execution_list = USet.to_list executions in
          let* assertion_result =
            match ctx.assertions with
            | None ->
                (* Even without assertions, run UB validation *)
                let%lwt ub_reasons, execution_results =
                  AssertionChecker.run_ub_validation_all execution_list
                    structure
                in
                let ub = List.length ub_reasons > 0 in
                  Lwt.return
                    {
                      valid = true;
                      ub;
                      ub_reasons = List.rev ub_reasons;
                      checked_executions = Some execution_results;
                      assertion_instances = None;
                    }
            | Some assertions ->
                check_assertion ~ctx assertions execution_list structure
                  ~exhaustive:ctx.options.exhaustive
          in
            ctx.valid <- Some assertion_result.valid;
            ctx.undefined_behaviour <- Some assertion_result.ub;
            ctx.checked_executions <- assertion_result.checked_executions;
            ctx.assertion_instances <- assertion_result.assertion_instances;
            Lwt.return ctx
    | _ ->
        Logs_safe.err (fun m ->
            m "Event structure or executions not available for assertion check."
        );
        Lwt.return ctx

(** {1 Send Assertion Results} *)

(** Message format for sending assertion results. *)
type assertion_results_message = {
  valid : bool;
  instances : assertion_instance list;
}
[@@deriving yojson]

(** [step_send_assertion_results lwt_ctx ~send_data] sends assertion results.

    Pipeline step that serializes assertion results to JSON and sends them to
    the client.

    @param lwt_ctx The verification context (as promise).
    @param send_data Function to send string data (returns promise).
    @return Unchanged context after sending results. *)
let step_send_assertion_results ~(send_data : string -> unit Lwt.t)
    (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let%lwt ctx = lwt_ctx in
    match (ctx.valid, ctx.assertion_instances) with
    | Some valid, Some instances ->
        let message = { valid; instances } in
        let result_json =
          Yojson.Safe.to_string (assertion_results_message_to_yojson message)
        in
        let%lwt () = send_data result_json in
          Lwt.return ctx
    | _ -> Lwt.return ctx
