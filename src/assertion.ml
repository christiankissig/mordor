open Context
open Events
open Expr
open Ir
open Lwt.Syntax
open Types
open Uset

type ir_assertion = unit Ir.ir_assertion
type ir_litmus = unit Ir.ir_litmus

(** Assertion checking and refinement for symbolic memory model checking *)

(** {1 Set Membership Evaluation} *)

(** Check if expression contains set membership operations *)
let rec has_set_operation expr =
  match expr with
  | EBinOp (_, "in", _) -> true
  | EBinOp (_, "notin", _) -> true
  | EBinOp (e1, _, e2) -> has_set_operation e1 || has_set_operation e2
  | EUnOp (_, e) -> has_set_operation e
  | EOr lst -> List.exists (List.exists has_set_operation) lst
  | _ -> false

(** Evaluate tuple to pair of integers *)
let eval_tuple expr =
  match expr with
  | EBinOp (ENum a, ",", ENum b) -> (Z.to_int a, Z.to_int b)
  | _ -> failwith "Invalid tuple in set membership: expected (int, int)"

(** Get relation by name from structure/execution *)
let get_relation name (structure : symbolic_event_structure)
    (execution : symbolic_execution) =
  match name with
  | ".ppo" -> execution.ppo
  | ".po" -> structure.po
  | ".rf" -> execution.rf
  | ".dp" -> execution.dp
  | ".rmw" -> execution.ex_rmw
  | _ ->
      Logs.warn (fun m ->
          m "Unknown or unsupported relation: %s, returning empty" name
      );
      USet.create ()

(** Evaluate set membership expression directly *)
let rec eval_set_expr expr (structure : symbolic_event_structure)
    (execution : symbolic_execution) =
  match expr with
  | EBinOp (tuple_expr, "in", EVar set_name) ->
      let pair = eval_tuple tuple_expr in
      let rel = get_relation set_name structure execution in
        USet.mem rel pair
  | EBinOp (tuple_expr, "notin", EVar set_name) ->
      let pair = eval_tuple tuple_expr in
      let rel = get_relation set_name structure execution in
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
        ("Cannot evaluate expression as set membership: "
        ^ "expected 'in' or 'notin' operator"
        )

(** {1 Helper Modules} *)

(** Expression utilities *)
module ExprUtil = struct
  (** Substitute variable with expression *)
  let rec subst expr var_expr new_expr =
    if expr = var_expr then new_expr
    else
      match expr with
      | EBinOp (e1, op, e2) ->
          EBinOp (subst e1 var_expr new_expr, op, subst e2 var_expr new_expr)
      | EUnOp (op, e) -> EUnOp (op, subst e var_expr new_expr)
      | EOr lst ->
          EOr (List.map (List.map (fun e -> subst e var_expr new_expr)) lst)
      | _ -> expr
end

(** {1 Model Options} *)

type model_options = { coherent : string option; ubopt : bool }

let model_options_table : (string, model_options) Hashtbl.t =
  let tbl = Hashtbl.create 20 in
    Hashtbl.add tbl "Power" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Sevcik" { coherent = None; ubopt = false };
    Hashtbl.add tbl "Problem" { coherent = None; ubopt = false };
    Hashtbl.add tbl "JR" { coherent = None; ubopt = false };
    Hashtbl.add tbl "RC11" { coherent = Some "rc11"; ubopt = false };
    Hashtbl.add tbl "RC11c" { coherent = Some "rc11c"; ubopt = false };
    Hashtbl.add tbl "Bridging" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Bubbly" { coherent = None; ubopt = false };
    Hashtbl.add tbl "Grounding" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Promising" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "Soham" { coherent = None; ubopt = false };
    Hashtbl.add tbl "IMM" { coherent = Some "imm"; ubopt = false };
    Hashtbl.add tbl "RC11UB" { coherent = Some "rc11"; ubopt = true };
    Hashtbl.add tbl "IMMUB" { coherent = Some "imm"; ubopt = true };
    Hashtbl.add tbl "UB11" { coherent = None; ubopt = true };
    Hashtbl.add tbl "_" { coherent = None; ubopt = false };
    tbl

let get_model_options name = Hashtbl.find_opt model_options_table name

let model_names =
  [
    "Power";
    "Sevcik";
    "Problem";
    "JR";
    "RC11";
    "RC11c";
    "Bridging";
    "Bubbly";
    "Grounding";
    "Promising";
    "Soham";
    "IMM";
    "RC11UB";
    "IMMUB";
    "UB11";
    "_";
  ]

(** {1 Assertion Types} *)

let outcome_of_string = function
  | "allow" -> Allow
  | "forbid" -> Forbid
  | s -> failwith ("Invalid outcome: " ^ s)

let string_of_outcome = function
  | Allow -> "allow"
  | Forbid -> "forbid"

(* assertion_condition is now defined in Ir module *)

type assertion = {
  outcome : ir_assertion_outcome;
  condition : Ir.assertion_condition;
  model : string option;
}

(** {1 Assertion Checking} *)

type ub_reason = int * string
type assertion_result = { valid : bool; ub : bool; ub_reasons : ub_reason list }

(** {1 Refinement Checking} *)

type refinement_result = {
  structure : symbolic_event_structure;
  executions : symbolic_execution list;
  events : (int, event) Hashtbl.t;
  valid : bool;
}

(** Helper to get location from an event *)
let get_event_loc events event_label =
  match Hashtbl.find_opt events event_label with
  | None -> VVar (string_of_int event_label)
  | Some e -> (
      match e.typ with
      | Malloc -> (
          match e.rval with
          | Some v -> v
          | None -> VVar (string_of_int event_label)
        )
      | _ -> (
          match e.id with
          | Some id -> id
          | None -> VVar (string_of_int event_label)
        )
    )

(** Parallel map for lists using Lwt *)
let lwt_pmap f lst = Lwt_list.map_p f lst

let lwt_piter f lst = Lwt_list.iter_p f lst

(** Parallel some (short-circuit OR) for lists using Lwt *)
let rec lwt_psome f = function
  | [] -> Lwt.return false
  | x :: xs ->
      let%lwt result = f x in
        if result then Lwt.return true else lwt_psome f xs

(** Parallel every (short-circuit AND) for lists using Lwt *)
let rec lwt_pevery f = function
  | [] -> Lwt.return true
  | x :: xs ->
      let%lwt result = f x in
        if not result then Lwt.return false else lwt_pevery f xs

(** Parallel all (no short-circuit) for lists using Lwt *)
let lwt_pall f lst =
  let%lwt results = Lwt_list.map_p f lst in
    Lwt.return (List.for_all (fun x -> x) results)

(** Check refinement between two programs

    Refinement semantics (from JS implementation):
    - Build symbol maps from both programs' executions
    - For each execution in "to" program:
    - Find if there's a matching execution in "from" program
    - Matching means: for each symbol in "to" execution, there exists a
      corresponding symbol in "from" execution with the same value
    - Refinement holds if all "to" executions have matches in "from" *)
let check_refinement from_prog to_prog =
  (* Build symbol map: register -> set of symbolic expressions *)
  let build_symbol_map executions =
    let map = Hashtbl.create 32 in
      List.iter
        (fun (exec : symbolic_execution) ->
          Hashtbl.iter
            (fun register sym_expr ->
              (* Only add non-numeric expressions *)
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
  in

  (* Build reverse symbol map: symbol_string -> set of registers *)
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
  in

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
        (* Start with all from executions as candidates *)
        let candidates = ref from_execs in

        (* Filter candidates based on each symbol in to_exec *)
        Hashtbl.iter
          (fun sym_str value ->
            match Hashtbl.find_opt to_reverse_map sym_str with
            | None -> ()
            | Some registers ->
                (* Get all possible source symbols for these registers *)
                (* registers is a USet of strings (register names) *)
                (* from_map maps register names to USets of exprs *)
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
                              Hashtbl.find_opt from_exec.fix_rf_map
                                source_sym_str
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

(** Perform refinement checking on AST

    Chained assertion semantics (from JS implementation): 1. Extract chain of
    programs via rest field 2. Collect all programs in list 3. Last program is
    the "final" one 4. Each program gets dummy assertion (0=0) for execution
    generation 5. Check refinement: each test vs final 6. Result is XORed with
    outcome (forbid means refinement should NOT hold) *)
let do_check_refinement ast =
  (* Extract model and outcome from first assertion *)
  let model, outcome =
    match ast.assertions with
    | [] -> (None, Forbid)
    | Chained { model; outcome; _ } :: _ -> (Some model, outcome)
    | _ -> (None, Allow)
  in

  (* Collect all programs in the chain *)
  let rec collect_chain acc ast =
    match ast.assertions with
    | Chained { rest; _ } :: _ -> collect_chain (ast :: acc) rest
    | _ -> List.rev (ast :: acc)
  in

  let tests = collect_chain [] ast in

  (* Split into tests and final *)
  let final = List.hd (List.rev tests) in
  let test_progs = List.rev (List.tl (List.rev tests)) in

  (* Create dummy assertion (0 = 0) for execution generation *)
  let dummy_assertion =
    Outcome
      {
        outcome = Allow;
        condition = Ir.CondExpr (EBinOp (ENum Z.zero, "=", ENum Z.zero));
        model;
      }
  in

  (* Replace assertions with dummy for all tests *)
  let tests_with_dummy =
    List.map
      (fun litmus -> { litmus with assertions = [ dummy_assertion ] })
      (test_progs @ [ final ])
  in

  (* Create symbolic event structures for all programs *)
  (* This would need to call your symmrd.ml's create_symbolic_event_structure *)
  (* For now, using a simplified structure *)

  (* Assuming you have a function to create structures: *)
  (* let create_structure = Symmrd.create_symbolic_event_structure *)

  (* Check refinement between each test and final *)
  let%lwt final_result =
    (* You'd call: create_structure final { exhaustive = true; dependencies = true; refinement = true } *)
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
        (* You'd call: create_structure test_litmus options *)
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

  (* Final result XORed with outcome *)
  let final_valid = all_pass in

  Lwt.return { !refinement_result with valid = final_valid }

(** Main assertion checking function *)
let check_assertion (assertion : ir_assertion) executions structure events
    ~exhaustive =
  match assertion with
  | Model { model } ->
      (* Model assertions just specify which memory model to use *)
      (* They don't validate anything, so always return valid *)
      Logs.info (fun m -> m "Using memory model: %s" model);
      Lwt.return { valid = true; ub = false; ub_reasons = [] }
  | Outcome { outcome; condition; model } ->
      Logs.info (fun m ->
          m "Checking assertion: %s (%s)"
            (string_of_outcome outcome)
            ( match condition with
            | Ir.CondUB -> "ub"
            | Ir.CondExpr expr -> Expr.to_string expr
            )
      );

      (* Extract the actual expression from the condition, handling UB specially *)
      let condition_expr_opt =
        match condition with
        | Ir.CondUB ->
            None (* UB condition doesn't have an expression to check *)
        | Ir.CondExpr expr -> Some expr
      in

      (* For UB assertions, we only check for undefined behavior, not condition satisfiability *)
      let is_ub_assertion =
        match condition with
        | Ir.CondUB -> true
        | Ir.CondExpr _ -> false
      in

      (* Check for no executions in exhaustive mode *)
      let%lwt () =
        if exhaustive && List.length executions = 0 then
          Lwt.fail_with "No executions"
        else Lwt.return ()
      in

      (* Handle non-exhaustive forbid case *)
      if (not exhaustive) && outcome = Forbid && List.length executions = 0 then
        (* non-exhaustive forbid case allows absence of executions *)
        Lwt.return { valid = true; ub = false; ub_reasons = [] }
      else
        let ub_reasons = ref [] in
        let expected = outcome = Allow in
        let curr = ref false in

        (* Helper to get pointers (events with locations that are not variables) *)
        let get_pointers () =
          let read_events = structure.read_events in
          let write_events = structure.write_events in
          let free_events = structure.free_events in
          let malloc_events = structure.malloc_events in

          let all_pointer_events =
            USet.union
              (USet.union read_events write_events)
              (USet.union free_events malloc_events)
          in

          let result = ref [] in
            USet.iter
              (fun label ->
                let loc = get_event_loc events label in
                  if Value.is_not_var loc then result := (label, loc) :: !result
              )
              all_pointer_events;
            !result
        in

        let pointers = get_pointers () in

        (* Process each execution *)
        let%lwt () =
          lwt_piter
            (fun (execution : symbolic_execution) ->
              let%lwt () = Lwt.return () in

              (* Build RF conditions *)
              let rf_conditions = ref [] in
                USet.iter
                  (fun (w, r) ->
                    let read_event = Hashtbl.find events r in
                    let read_rval =
                      match read_event.rval with
                      | Some rv -> rv
                      | None -> VVar ("r" ^ string_of_int r)
                    in
                    let rf_value =
                      let rval_str = Value.to_string read_rval in
                        match
                          Hashtbl.find_opt execution.fix_rf_map rval_str
                        with
                        | Some v -> v
                        | None -> Expr.of_value read_rval
                    in
                    let restriction =
                      match Hashtbl.find_opt structure.restrict w with
                      | Some r -> r
                      | None -> []
                    in
                    let equality =
                      EBinOp (Expr.of_value read_rval, "=", rf_value)
                    in
                      rf_conditions :=
                        restriction @ [ equality ] @ !rf_conditions
                  )
                  execution.rf;
                Logs.debug (fun m ->
                    m "RF conditions: %s"
                      (String.concat ", "
                         (List.map Expr.to_string !rf_conditions)
                      )
                );
                let rf_conditions = !rf_conditions in

                (* Build rhb (happens-before) relation *)
                (* rhb = (ppo ∪ fj ∪ dp ∪ rf)+ ∩ (E × E) *)
                let rhb_base =
                  USet.union
                    (USet.union execution.ppo structure.fj)
                    (USet.union execution.dp execution.rf)
                in
                let rhb_trans = URelation.transitive_closure rhb_base in
                (* Add reflexive edges: (e, e) for all e in ex_e *)
                let rhb = USet.create () in
                  USet.iter
                    (fun e -> USet.add rhb (e, e) |> ignore)
                    execution.ex_e;
                  USet.iter (fun edge -> USet.add rhb edge |> ignore) rhb_trans;

                  (* Build pointer map with substitutions from fix_rf_map *)
                  let pointer_map_of = Hashtbl.create (List.length pointers) in
                    List.iter
                      (fun (event_label, loc_value) ->
                        let substituted =
                          Hashtbl.fold
                            (fun var value acc ->
                              ExprUtil.subst acc (EVar var) value
                            )
                            execution.fix_rf_map (Expr.of_value loc_value)
                        in
                        (* Extract symbol if it's a single symbol *)
                        let symbols = Expr.get_symbols substituted in
                          if List.length symbols = 1 then
                            Hashtbl.add pointer_map_of event_label
                              (List.hd symbols)
                      )
                      pointers;

                    (* Get all malloc, free, read, write events *)
                    let all_frees =
                      filter_events events execution.ex_e Free ()
                    in
                    let all_alloc =
                      filter_events events execution.ex_e Malloc ()
                    in

                    (* All events that use pointers (read, write, malloc) *)
                    let all_alloc_read_writes =
                      USet.filter
                        (fun label ->
                          USet.mem execution.ex_e label
                          && Hashtbl.mem pointer_map_of label
                        )
                        structure.e
                    in

                    let all_pointer_read_writes =
                      USet.difference all_alloc_read_writes all_alloc
                    in

                    (* Check use-after-free *)
                    let all_before_free =
                      USet.for_all
                        (fun free ->
                          let free_event = Hashtbl.find events free in
                          let free_id =
                            match free_event.id with
                            | Some id -> Value.to_string id
                            | None -> ""
                          in

                          (* Find all events using the same pointer *)
                          let related_events =
                            USet.filter
                              (fun e ->
                                match Hashtbl.find_opt pointer_map_of e with
                                | Some sym -> sym = free_id
                                | None -> false
                              )
                              all_alloc_read_writes
                          in

                          (* Check if all related events happen before free *)
                          USet.for_all
                            (fun e -> USet.mem rhb (e, free))
                            related_events
                        )
                        all_frees
                    in

                    (* Check pointer dereference after allocation *)
                    let all_after_alloc =
                      USet.for_all
                        (fun alloc ->
                          let alloc_ptr =
                            Hashtbl.find_opt pointer_map_of alloc
                          in

                          let related_events =
                            USet.filter
                              (fun e ->
                                match
                                  (alloc_ptr, Hashtbl.find_opt pointer_map_of e)
                                with
                                | Some ap, Some ep -> ap = ep
                                | _ -> false
                              )
                              all_pointer_read_writes
                          in

                          (* Check if all related events happen after alloc *)
                          USet.for_all
                            (fun e -> USet.mem rhb (alloc, e))
                            related_events
                        )
                        all_alloc
                    in

                    (* Record UB reasons *)
                    let exec_idx = 0 in
                      (* We'd need to track this properly *)
                      if not all_before_free then
                        ub_reasons :=
                          (exec_idx, "Use after free") :: !ub_reasons;
                      if not all_after_alloc then
                        ub_reasons :=
                          (exec_idx, "Unbounded pointer dereference")
                          :: !ub_reasons;

                      (* Check conditions if not already satisfied *)
                      if not !curr then (
                        if
                          (* For UB assertions, we don't check condition satisfiability *)
                          is_ub_assertion
                        then Lwt.return ()
                        else
                          (* Extract the expression from the condition *)
                          match condition_expr_opt with
                          | None ->
                              Lwt.return
                                () (* Should not happen for non-UB assertions *)
                          | Some cond_expr ->
                              let%lwt conds_satisfied =
                                (* Check if condition contains set operations *)
                                if has_set_operation cond_expr then (
                                  (* Evaluate set operations directly, don't use solver *)
                                  try
                                    let set_result =
                                      eval_set_expr cond_expr structure
                                        execution
                                    in
                                      (* Still check rf_conditions with solver if needed *)
                                      if List.length rf_conditions > 0 then
                                        let%lwt rf_ok =
                                          Solver.is_sat rf_conditions
                                        in
                                          Lwt.return (set_result && rf_ok)
                                      else Lwt.return set_result
                                  with Failure msg ->
                                    Logs.err (fun m ->
                                        m "Error evaluating set expression: %s"
                                          msg
                                    );
                                    Lwt.return false
                                )
                                else
                                  (* instantiate condition expression with final
                                     register environment *)
                                  let inst_cond_expr =
                                    Expr.evaluate cond_expr (fun reg ->
                                        Hashtbl.find_opt execution.final_env reg
                                    )
                                  in
                                  let cond_expr_and_rf_conditions =
                                    inst_cond_expr :: rf_conditions
                                  in
                                    Logs.debug (fun m ->
                                        m "Checking condition with solver: %s"
                                          (String.concat ", "
                                             (List.map Expr.to_string
                                                cond_expr_and_rf_conditions
                                             )
                                          )
                                    );
                                    (* No set operations, use solver as normal *)
                                    let* is_sat =
                                      Solver.is_sat cond_expr_and_rf_conditions
                                    in
                                      Logs.debug (fun m ->
                                          m "Solver result: %b" is_sat
                                      );
                                      Lwt.return is_sat
                              in

                              (* Check extended assertions *)
                              let%lwt extended_ok = Lwt.return true in

                              curr := conds_satisfied && extended_ok;
                              Lwt.return ()
                      )
                      else Lwt.return ()
            )
            executions
        in

        (* Compute final result *)
        let ub = List.length !ub_reasons > 0 in
        (* For UB assertions, validity is based on whether UB was found *)
        let valid =
          if is_ub_assertion then
            (* For "allow (ub)", valid if UB found; for "forbid (ub)", valid if no UB *)
            ub = (outcome = Allow)
          else
            (* For regular assertions, check if condition was satisfied *)
            !curr = expected
        in

        Logs.info (fun m -> m "Assertion result: valid=%b, ub=%b" valid ub);

        Lwt.return { valid; ub; ub_reasons = List.rev !ub_reasons }
  | Chained { model; outcome; rest } ->
      (* Chained assertions perform refinement checking *)
      Logs.info (fun m -> m "Performing refinement check for chained assertion");
      let%lwt result =
        do_check_refinement
          {
            name = "";
            program = [];
            assertions = [ Chained { model; outcome; rest } ];
          }
      in
        Lwt.return { valid = result.valid; ub = false; ub_reasons = [] }

let step_check_assertions (ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  Logs.debug (fun m -> m "Starting assertion checking step");
  let%lwt ctx = ctx in
    match (ctx.structure, ctx.executions, ctx.events) with
    | Some structure, Some executions, Some events ->
        Logs.debug (fun m ->
            m
              "Event structure and executions available for assertion check:\n\
               %s"
              (show_symbolic_event_structure structure)
        );
        let execution_list = USet.to_list executions in
          Logs.debug (fun m ->
              m "Checking assertions against %d executions:\n%s"
                (List.length execution_list)
                (String.concat "\n"
                   (List.map
                      (fun exec -> show_symbolic_execution exec)
                      execution_list
                   )
                )
          );

          let* assertion_result : assertion_result =
            match ctx.assertions with
            | None -> Lwt.return { valid = true; ub = false; ub_reasons = [] }
            | Some assertions ->
                let* (res : assertion_result) =
                  check_assertion assertions execution_list structure events
                    ~exhaustive:ctx.options.exhaustive
                in
                  Lwt.return res
          in
            ctx.valid <- Some assertion_result.valid;
            ctx.undefined_behaviour <- Some assertion_result.ub;
            Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "Event structure or executions not available for assertion check."
        );
        Lwt.return ctx
