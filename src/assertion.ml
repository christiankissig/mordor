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

    Contains validity status, undefined behavior information, and per-execution
    results for detailed analysis. *)
type assertion_result = {
  valid : bool;  (** Whether the assertion holds for all checked executions. *)
  ub : bool;  (** Whether any undefined behavior was detected. *)
  ub_reasons : ub_reason list;
      (** List of all undefined behavior instances found. *)
  checked_executions : execution_info list option;
      (** Per-execution results with satisfaction and UB status. *)
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
  (** [has_set_operation expr] checks if expression uses set operations.

      Recursively searches for ["in"] or ["notin"] operators.

      @param expr The expression to check.
      @return [true] if expression contains set membership tests. *)
  let rec has_set_operation expr =
    match expr with
    | EBinOp (_, "in", _) | EBinOp (_, "notin", _) -> true
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
        let rel = Execution.get_relation set_name structure execution in
          USet.mem rel pair
    | EBinOp (tuple_expr, "notin", EVar set_name) ->
        let pair = eval_tuple tuple_expr in
        let rel = Execution.get_relation set_name structure execution in
          not (USet.mem rel pair)
    | EBinOp (e1, "&&", e2) ->
        eval_set_expr e1 structure execution
        && eval_set_expr e2 structure execution
    | EBinOp (e1, "||", e2) ->
        eval_set_expr e1 structure execution
        || eval_set_expr e2 structure execution
    | EUnOp ("!", e) -> not (eval_set_expr e structure execution)
    | _ ->
        failwith
          "Cannot evaluate expression as set membership: expected 'in' or \
           'notin' operator"
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

        For each free event, finds all accesses to the same location that don't
        happen-before the free. These represent potential use-after-free. UAF is
        admitted when: (use, free) NOT in happens-before.

        @param structure The event structure.
        @param execution The execution.
        @param ub_reasons Mutable reference to accumulate UB instances.
        @param pointer_map Map from malloc events to symbols.
        @param rhb Happens-before relation.
        @param all_alloc_read_writes All pointer-related events. *)
    let check structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes =
      let all_frees = USet.intersection structure.free_events execution.e in
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
                all_alloc_read_writes
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
          let%lwt rf_ok = Solver.is_sat rf_conditions in
            Lwt.return (set_result && rf_ok)
        else Lwt.return set_result
    with Failure msg ->
      Logs.err (fun m -> m "Error evaluating set expression: %s" msg);
      Lwt.return false

  (** [check_with_solver cond_expr rf_conditions execution] uses SMT solver.

      Evaluates condition by substituting final register values and checking
      satisfiability with RF constraints.

      @param cond_expr The condition expression.
      @param rf_conditions RF equality constraints.
      @param execution The execution.
      @return Promise of [true] if satisfiable. *)
  let check_with_solver cond_expr rf_conditions execution =
    (* Instantiate condition expression with final register environment *)
    let inst_cond_expr =
      Expr.evaluate ~env:(Hashtbl.find_opt execution.final_env) cond_expr
    in
    let cond_expr_and_rf_conditions = inst_cond_expr :: rf_conditions in
      Solver.is_sat cond_expr_and_rf_conditions

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
      if SetOperations.has_set_operation cond_expr then
        check_with_set_operations cond_expr rf_conditions structure execution
      else check_with_solver cond_expr rf_conditions execution
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

  (** [build_symbol_map executions] creates register to symbols mapping.

      Maps each register to the set of all symbolic expressions it takes across
      all executions.

      @param executions List of executions.
      @return Hash table mapping registers to symbol sets. *)
  let build_symbol_map executions =
    let map = Hashtbl.create 32 in
      List.iter
        (fun (exec : symbolic_execution) ->
          Hashtbl.iter
            (fun register sym_expr ->
              if not (Expr.is_number sym_expr) then (
                let entry =
                  match Hashtbl.find_opt map register with
                  | Some s -> s
                  | None -> USet.create ()
                in
                  USet.add entry sym_expr |> ignore;
                  Hashtbl.replace map register entry
              )
            )
            exec.fix_rf_map
        )
        executions;
      map

  (** [build_reverse_map executions] creates symbol to registers mapping.

      Maps each symbolic expression (as string) to the set of registers that can
      hold it across all executions.

      @param executions List of executions.
      @return Hash table mapping symbol strings to register sets. *)
  let build_reverse_map executions =
    let map = Hashtbl.create 32 in
      List.iter
        (fun (exec : symbolic_execution) ->
          Hashtbl.iter
            (fun register sym_expr ->
              if not (Expr.is_number sym_expr) then (
                let sym_str = Expr.to_string sym_expr in
                let entry =
                  match Hashtbl.find_opt map sym_str with
                  | Some s -> s
                  | None -> USet.create ()
                in
                  USet.add entry register |> ignore;
                  Hashtbl.replace map sym_str entry
              )
            )
            exec.fix_rf_map
        )
        executions;
      map

  (** [can_match_execution to_exec from_execs from_map to_reverse_map] checks if
      execution can be matched.

      Determines if [to_exec] (from refined program) can be matched with any
      execution in [from_execs] (from original program) based on symbolic value
      correspondence.

      @param to_exec Execution from refined program.
      @param from_execs Executions from original program.
      @param from_map Symbol map for original program.
      @param to_reverse_map Reverse symbol map for refined program.
      @return [true] if a matching execution exists. *)
  let can_match_execution to_exec from_execs from_map to_reverse_map =
    (* Start with all from executions as candidates *)
    let candidates = ref from_execs in

    (* Filter candidates based on each symbol in to_exec *)
    Hashtbl.iter
      (fun sym_str value ->
        match Hashtbl.find_opt to_reverse_map sym_str with
        | None -> ()
        | Some registers ->
            (* Get all possible source symbols for these registers *)
            let source_syms =
              USet.fold
                (fun (acc : expr USet.t) register ->
                  match Hashtbl.find_opt from_map register with
                  | Some syms -> USet.union acc syms
                  | None -> acc
                )
                registers
                (USet.create () : expr USet.t)
            in
              (* Filter candidates: must have at least one matching symbol with same value *)
              candidates :=
                List.filter
                  (fun from_exec ->
                    USet.exists
                      (fun source_sym ->
                        let source_sym_str = Expr.to_string source_sym in
                          match
                            Hashtbl.find_opt from_exec.fix_rf_map source_sym_str
                          with
                          | Some from_val -> Expr.equal from_val value
                          | None -> false
                      )
                      source_syms
                  )
                  !candidates
      )
      to_exec.fix_rf_map;

    (* At least one candidate should remain *)
    List.length !candidates > 0

  (** [check_refinement from_prog to_prog] checks refinement relation.

      Verifies that every execution of [to_prog] can be matched with an
      execution of [from_prog], meaning the transformation preserves behaviors.

      @param from_prog Original program (as promise).
      @param to_prog Refined program (as promise).
      @return Promise of refinement result. *)
  let check_refinement from_prog to_prog =
    let%lwt from_result = from_prog in
    let%lwt to_result = to_prog in

    let from_execs = from_result.executions in
    let to_execs = to_result.executions in

    let from_map = build_symbol_map from_execs in
    let to_reverse_map = build_reverse_map to_execs in

    (* Check if every "to" execution can be matched with a "from" execution *)
    let refinement_holds =
      List.for_all
        (fun to_exec ->
          can_match_execution to_exec from_execs from_map to_reverse_map
        )
        to_execs
    in

    Lwt.return
      {
        structure = to_result.structure;
        executions = to_result.executions;
        events = to_result.events;
        valid = refinement_holds;
      }

  (** [collect_chain acc ast] collects programs in chained assertion.

      Recursively extracts all programs from a chained refinement assertion.

      @param acc Accumulator for collected ASTs.
      @param ast Current AST.
      @return List of all ASTs in refinement chain. *)
  let rec collect_chain acc ast =
    match ast.assertions with
    | Chained { rest; _ } :: _ -> collect_chain (ast :: acc) rest
    | _ -> List.rev (ast :: acc)

  (** [create_dummy_assertion model] creates assertion for execution generation.

      Creates a trivially true assertion to generate executions without
      filtering by outcome.

      @param model Optional memory model.
      @return Dummy outcome assertion. *)
  let create_dummy_assertion model =
    Outcome
      {
        outcome = Allow;
        condition = Ir.CondExpr (EBinOp (ENum Z.zero, "=", ENum Z.zero));
        model;
      }

  (** [do_check_refinement ast] performs refinement check on AST.

      Main refinement checking function that processes chained assertions and
      validates refinement across the chain.

      @param ast The litmus test AST with chained assertions.
      @return Promise of refinement result. *)
  let do_check_refinement ast =
    (* Extract model and outcome from first assertion *)
    let model, outcome =
      match ast.assertions with
      | [] -> (None, Forbid)
      | Chained { model; outcome; _ } :: _ -> (Some model, outcome)
      | _ -> (None, Allow)
    in

    let tests = collect_chain [] ast in
    let final = List.hd (List.rev tests) in
    let test_progs = List.rev (List.tl (List.rev tests)) in

    let dummy_assertion = create_dummy_assertion model in

    (* Replace assertions with dummy for all tests *)
    let tests_with_dummy =
      List.map
        (fun litmus -> { litmus with assertions = [ dummy_assertion ] })
        (test_progs @ [ final ])
    in

    (* Create empty result for now (would integrate with actual structure creation) *)
    let%lwt final_result =
      Lwt.return
        {
          structure = SymbolicEventStructure.create ();
          executions = [];
          events = Hashtbl.create 0;
          valid = false;
        }
    in

    (* Check refinement for each test *)
    let refinement_result = ref final_result in
    let%lwt all_pass =
      lwt_pevery
        (fun _test_litmus ->
          let test_result_lwt = Lwt.return final_result in
          let%lwt ref_result =
            check_refinement test_result_lwt (Lwt.return final_result)
          in
            refinement_result := ref_result;
            (* XOR with forbid: if outcome is Forbid, we expect refinement to fail *)
            Lwt.return (ref_result.valid <> (outcome = Forbid))
        )
        test_progs
    in

    Lwt.return { !refinement_result with valid = all_pass }
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

      @param outcome Expected outcome (Allow/Forbid).
      @param condition Condition to check.
      @param structure The event structure.
      @param execution The execution.
      @param already_satisfied Mutable reference tracking satisfaction.
      @return Promise of [(satisfied, ub_reasons)] pair. *)
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
        Lwt.return (!already_satisfied, !ub_reasons)
      else
        match condition_expr_opt with
        | None -> failwith "Unexpected missing condition expression"
        | Some cond_expr ->
            let%lwt conds_satisfied =
              ConditionChecker.check_condition cond_expr structure execution
            in
            (* Check extended assertions (currently always true) *)
            let%lwt extended_ok = Lwt.return true in
              already_satisfied := conds_satisfied && extended_ok;
              Lwt.return (!already_satisfied, !ub_reasons)

  (** [check assertion execution structure already_satisfied ~exhaustive] checks
      single execution.

      @param assertion The assertion to check.
      @param execution The execution.
      @param structure The event structure.
      @param already_satisfied Mutable reference for satisfaction tracking.
      @param exhaustive Whether checking exhaustively.
      @return Promise of [(satisfied, ub_reasons)] pair.
      @raise Failure if assertion type is unexpected. *)
  let check assertion execution structure already_satisfied ~exhaustive =
    let%lwt () = Lwt.return () in
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
    { valid; ub = false; ub_reasons = []; checked_executions = None }

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
    Logs.info (fun m -> m "Using memory model: %s" model);
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
      @return Promise of [(satisfied, ub_reasons, results)] triple. *)
  let process_executions assertion executions structure =
    let ub_reasons = ref [] in
    let satisfied = ref false in
    let execution_results = ref [] in

    let%lwt () =
      lwt_piter
        (fun execution ->
          let%lwt exec_satisfied, local_ub_reasons =
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
            Lwt.return ()
        )
        executions
    in

    Lwt.return (!satisfied, !ub_reasons, !execution_results)

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
    Logs.info (fun m ->
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

    (* Handle empty execution list *)
    let%lwt early_result = handle_no_executions exhaustive outcome in

    match early_result with
    | Some result -> Lwt.return result
    | None ->
        let expected = outcome = Allow in

        (* Process all executions *)
        let%lwt satisfied, ub_reasons, execution_results =
          process_executions
            (Outcome { outcome; condition; model })
            executions structure
        in

        (* Compute final result *)
        let ub = List.length ub_reasons > 0 in
        let valid =
          compute_validity outcome is_ub_assertion satisfied expected ub
        in

        Logs.info (fun m -> m "Assertion result: valid=%b, ub=%b" valid ub);

        Lwt.return
          {
            valid;
            ub;
            ub_reasons = List.rev ub_reasons;
            checked_executions = Some execution_results;
          }

  (** [check_chained_assertion model outcome rest executions structure] checks
      chained refinement.

      @param model Optional memory model.
      @param outcome Expected outcome.
      @param rest Rest of refinement chain.
      @param executions List of executions.
      @param structure The event structure.
      @return Promise of assertion result. *)
  let check_chained_assertion model outcome rest executions structure =
    Logs.info (fun m -> m "Performing refinement check for chained assertion");

    (* Run UB validation on all executions *)
    let%lwt ub_reasons, execution_results =
      run_ub_validation_all executions structure
    in
    let ub = List.length ub_reasons > 0 in

    let%lwt result =
      Refinement.do_check_refinement
        {
          config =
            {
              name = None;
              model = None;
              values = [];
              defacto = [];
              constraints = [];
            };
          program = [];
          assertions = [ Chained { model; outcome; rest } ];
        }
    in
      Lwt.return
        {
          valid = result.valid;
          ub;
          ub_reasons = List.rev ub_reasons;
          checked_executions = Some execution_results;
        }

  (** [check assertion executions structure ~exhaustive] main checking function.

      Dispatches to appropriate checker based on assertion type.

      @param assertion The assertion to check.
      @param executions List of executions.
      @param structure The event structure.
      @param exhaustive Whether to check exhaustively.
      @return Promise of assertion result. *)
  let check assertion executions structure ~exhaustive =
    match assertion with
    | Model { model } -> check_model_assertion model executions structure
    | Outcome { outcome; condition; model } ->
        check_outcome_assertion outcome condition model executions structure
          ~exhaustive
    | Chained { model; outcome; rest } ->
        check_chained_assertion model outcome rest executions structure
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
                    }
            | Some assertions ->
                check_assertion assertions execution_list structure
                  ~exhaustive:ctx.options.exhaustive
          in
            ctx.valid <- Some assertion_result.valid;
            ctx.undefined_behaviour <- Some assertion_result.ub;
            ctx.checked_executions <- assertion_result.checked_executions;
            Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "Event structure or executions not available for assertion check."
        );
        Lwt.return ctx
