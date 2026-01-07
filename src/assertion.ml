open Context
open Events
open Executions
open Expr
open Ir
open Lwt.Syntax
open Lwt_utils
open Types
open Uset

type ir_assertion = unit Ir.ir_assertion
type ir_litmus = unit Ir.ir_litmus

(** Assertion checking and refinement for symbolic memory model checking *)

(** {1 Assertion Result Type} *)

type assertion_result = {
  valid : bool;
  ub : bool;
  ub_reasons : ub_reason list;
  checked_executions : execution_info list option;
}

(** {1 Outcome Conversions} *)

let outcome_of_string = function
  | "allow" -> Allow
  | "forbid" -> Forbid
  | s -> failwith ("Invalid outcome: " ^ s)

let string_of_outcome = function
  | Allow -> "allow"
  | Forbid -> "forbid"

(** {1 Set Operations} *)

module SetOperations = struct
  (** Check if expression contains set membership operations *)
  let rec has_set_operation expr =
    match expr with
    | EBinOp (_, "in", _) | EBinOp (_, "notin", _) -> true
    | EBinOp (e1, _, e2) -> has_set_operation e1 || has_set_operation e2
    | EUnOp (_, e) -> has_set_operation e
    | EOr lst -> List.exists (List.exists has_set_operation) lst
    | _ -> false

  (** Evaluate tuple to pair of integers *)
  let eval_tuple expr =
    match expr with
    | EBinOp (ENum a, ",", ENum b) -> (Z.to_int a, Z.to_int b)
    | _ -> failwith "Invalid tuple in set membership: expected (int, int)"

  (** Evaluate set membership expression directly *)
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

module JSONSerialization = struct
  type event_pair = int * int [@@deriving yojson]
  type uaf_json = { uaf : event_pair list } [@@deriving yojson]
  type upd_json = { upd : event_pair list } [@@deriving yojson]

  type ub_reason_json = UAF_json of uaf_json | UPD_json of upd_json
  [@@deriving yojson]

  let ub_reason_to_yojson (ub_reason : ub_reason) : Yojson.Safe.t =
    match ub_reason with
    | UAF uaf_reasons ->
        let pairs = USet.fold (fun acc pair -> pair :: acc) uaf_reasons [] in
          uaf_json_to_yojson { uaf = pairs }
    | UPD upd_reasons ->
        let pairs = USet.fold (fun acc pair -> pair :: acc) upd_reasons [] in
          upd_json_to_yojson { upd = pairs }

  let ub_reason_to_json (ub_reason : ub_reason) : string =
    Yojson.Safe.to_string (ub_reason_to_yojson ub_reason)

  let ub_reasons_to_yojson (ub_reasons : ub_reason list) : Yojson.Safe.t =
    `List (List.map ub_reason_to_yojson ub_reasons)

  let ub_reasons_to_json (ub_reasons : ub_reason list) : string =
    Yojson.Safe.to_string (ub_reasons_to_yojson ub_reasons)
end

(** {1 Event Location Helper} *)

(** Get location of an event as a symbol string *)
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

module UBValidation = struct
  (** Find events using the same location as a given pointer symbol *)
  let find_related_events pointer_symbol structure execution all_events =
    USet.filter
      (fun e ->
        match get_event_location structure execution e with
        | Some loc_sym -> loc_sym = pointer_symbol
        | None -> false
      )
      all_events

  (** Find events that don't happen before a given event *)
  let find_events_not_before target_event happens_before events =
    USet.filter
      (fun e -> not (USet.mem happens_before (e, target_event)))
      events

  (** Use-after-free validation *)
  module UAF = struct
    let check structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes =
      let all_frees = USet.intersection structure.free_events execution.ex_e in
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

  (** Unbounded pointer dereference validation *)
  module UPD = struct
    let check structure execution ub_reasons pointer_map rhb
        all_alloc_read_writes =
      let all_alloc =
        USet.intersection structure.malloc_events execution.ex_e
      in
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

  (** Run all UB checks on an execution *)
  let check_all structure execution ub_reasons pointer_map rhb
      all_alloc_read_writes =
    UAF.check structure execution ub_reasons pointer_map rhb
      all_alloc_read_writes;
    UPD.check structure execution ub_reasons pointer_map rhb
      all_alloc_read_writes
end

(** {1 Execution Analysis} *)

module ExecutionAnalysis = struct
  (** Build happens-before relation (rhb) for an execution rhb = (ppo ∪ fj ∪ dp
      ∪ rf)+ ∩ (E × E) *)
  let build_happens_before structure execution =
    let rhb_base =
      USet.union
        (USet.union execution.ppo structure.fj)
        (USet.union execution.dp execution.rf)
    in
    let rhb_trans = URelation.transitive_closure rhb_base in
    (* Add reflexive edges: (e, e) for all e in ex_e *)
    let rhb = USet.create () in
      USet.iter (fun e -> USet.add rhb (e, e) |> ignore) execution.ex_e;
      USet.iter (fun edge -> USet.add rhb edge |> ignore) rhb_trans;
      rhb

  (** Extract pointer information from malloc events *)
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
      (USet.intersection structure.malloc_events execution.ex_e)

  (** Build pointer map with substitutions from fix_rf_map *)
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

  (** Get all events that use pointers - includes malloc events AND read/write
      events accessing those locations *)
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
      execution.ex_e

  (** Build rf (reads-from) conditions to be checked by solver *)
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

module ConditionChecker = struct
  (** Check condition expression with set operations *)
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

  (** Check condition expression using solver *)
  let check_with_solver cond_expr rf_conditions execution =
    (* Instantiate condition expression with final register environment *)
    let inst_cond_expr =
      Expr.evaluate cond_expr (fun reg ->
          Hashtbl.find_opt execution.final_env reg
      )
    in
    let cond_expr_and_rf_conditions = inst_cond_expr :: rf_conditions in
      Solver.is_sat cond_expr_and_rf_conditions

  (** Check if condition is satisfied *)
  let check_condition cond_expr structure execution =
    let rf_conditions =
      ExecutionAnalysis.build_rf_conditions structure execution
    in
      if SetOperations.has_set_operation cond_expr then
        check_with_set_operations cond_expr rf_conditions structure execution
      else check_with_solver cond_expr rf_conditions execution
end

(** {1 Refinement Checking} *)

module Refinement = struct
  type refinement_result = {
    structure : symbolic_event_structure;
    executions : symbolic_execution list;
    events : (int, event) Hashtbl.t;
    valid : bool;
  }

  (** Build symbol map: register -> set of symbolic expressions *)
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

  (** Build reverse symbol map: symbol_string -> set of registers *)
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

  (** Check if a to_exec can be matched with any from_exec *)
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

  (** Check refinement between two programs *)
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

  (** Collect all programs in a chained assertion *)
  let rec collect_chain acc ast =
    match ast.assertions with
    | Chained { rest; _ } :: _ -> collect_chain (ast :: acc) rest
    | _ -> List.rev (ast :: acc)

  (** Create dummy assertion for execution generation *)
  let create_dummy_assertion model =
    Outcome
      {
        outcome = Allow;
        condition = Ir.CondExpr (EBinOp (ENum Z.zero, "=", ENum Z.zero));
        model;
      }

  (** Perform refinement checking on AST *)
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
          structure =
            {
              e = USet.create ();
              events = Hashtbl.create 256;
              po = USet.create ();
              po_iter = USet.create ();
              rmw = USet.create ();
              lo = USet.create ();
              restrict = Hashtbl.create 0;
              cas_groups = Hashtbl.create 0;
              pwg = [];
              fj = USet.create ();
              p = Hashtbl.create 0;
              constraint_ = [];
              conflict = USet.create ();
              origin = Hashtbl.create 256;
              write_events = USet.create ();
              read_events = USet.create ();
              rlx_write_events = USet.create ();
              rlx_read_events = USet.create ();
              fence_events = USet.create ();
              branch_events = USet.create ();
              malloc_events = USet.create ();
              free_events = USet.create ();
            };
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

module PerExecutionChecker = struct
  (** Check if we should skip condition checking *)
  let should_skip_condition already_satisfied is_ub_assertion =
    already_satisfied || is_ub_assertion

  (** Check assertion for a single execution *)
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

  (** Check assertion for a single execution *)
  let check assertion execution structure already_satisfied ~exhaustive =
    let%lwt () = Lwt.return () in
      match assertion with
      | Outcome { outcome; condition; model } ->
          check_outcome_assertion outcome condition structure execution
            already_satisfied
      | _ -> failwith "unexpected assertion to be checked per execution"
end

(** {1 Main Assertion Checking} *)

module AssertionChecker = struct
  (** Create empty assertion result *)
  let empty_result ?(valid = true) () =
    { valid; ub = false; ub_reasons = []; checked_executions = None }

  (** Run UB validation on a single execution *)
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

  (** Run UB validation on all executions *)
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

  (** Check model assertion *)
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

  (** Handle non-exhaustive forbid case with no executions *)
  let handle_no_executions exhaustive outcome =
    if exhaustive then Lwt.fail_with "No executions"
    else if outcome = Forbid then Lwt.return (Some (empty_result ()))
    else Lwt.return None

  (** Process all executions and collect results *)
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

  (** Compute final validity based on outcome and results *)
  let compute_validity outcome is_ub_assertion satisfied expected ub =
    if is_ub_assertion then
      (* For "allow (ub)", valid if UB found; for "forbid (ub)", valid if no UB *)
      ub = (outcome = Allow)
    else
      (* For regular assertions, check if condition was satisfied *)
      satisfied = expected

  (** Check outcome assertion *)
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

  (** Check chained assertion *)
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

  (** Main assertion checking function *)
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

(** Main assertion checking function *)
let check_assertion = AssertionChecker.check

(** JSON serialization functions *)
let ub_reason_to_yojson = JSONSerialization.ub_reason_to_yojson

let ub_reason_to_json = JSONSerialization.ub_reason_to_json
let ub_reasons_to_yojson = JSONSerialization.ub_reasons_to_yojson
let ub_reasons_to_json = JSONSerialization.ub_reasons_to_json

(** Step function for checking assertions in context *)
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
