open Context
open Expr
open Ir
open Types
open Uset
open Events
open Lwt.Syntax

type ir_assertion = unit Ir.ir_assertion
type ir_litmus = unit Ir.ir_litmus

(** Assertion checking and refinement for symbolic memory model checking *)

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

type assertion_condition = CondExpr of expr | CondUB

type assertion = {
  outcome : ir_assertion_outcome;
  condition : assertion_condition;
  model : string option;
}

(** {1 Assertion Checking} *)

type ub_reason = int * string
type assertion_result = { valid : bool; ub : bool; ub_reasons : ub_reason list }

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

(** Main assertion checking function *)
let check_assertion (assertion : ir_assertion) executions structure events
    ~exhaustive =
  match assertion with
  | Outcome { outcome; condition; model } ->
      (* Check for no executions in exhaustive mode *)
      let%lwt () =
        if exhaustive && List.length executions = 0 then
          Lwt.fail_with "No executions"
        else Lwt.return ()
      in

      (* Handle non-exhaustive forbid case *)
      let%lwt () =
        if (not exhaustive) && outcome = Forbid && List.length executions = 0
        then Lwt.return ()
        else Lwt.return ()
      in

      if (not exhaustive) && outcome = Forbid && List.length executions = 0 then
        Lwt.return { valid = true; ub = false; ub_reasons = [] }
      else
        let ub_reasons = ref [] in
        let expected = outcome = Allow in
        let curr = ref false in

        (* Helper to get pointers (events with locations that are not variables) *)
        let get_pointers () =
          let read_events = filter_events events structure.e Read in
          let write_events = filter_events events structure.e Write in
          let free_events = filter_events events structure.e Free in
          let malloc_events = filter_events events structure.e Malloc in

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
                    let all_frees = filter_events events execution.ex_e Free in
                    let all_alloc =
                      filter_events events execution.ex_e Malloc
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
                        let%lwt conds_satisfied =
                          Solver.is_sat (condition :: rf_conditions)
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
        let valid = !curr = expected in

        Lwt.return { valid; ub; ub_reasons = List.rev !ub_reasons }
  | _ -> Lwt.fail_with "Unsupported assertion type"

(** {1 Refinement Checking} *)

type refinement_result = {
  structure : symbolic_event_structure;
  executions : symbolic_execution list;
  events : (int, event) Hashtbl.t;
  valid : bool;
}

(** Check refinement between two programs *)
let check_refinement _from_prog _to_prog =
  (* This is a placeholder implementation *)
  (* The actual implementation would:
     1. Create symbolic event structures for both programs
     2. Generate executions for both
     3. Build symbol maps
     4. Check that every execution of to_prog has a corresponding
        execution in from_prog with compatible RF mappings
  *)
  (* Placeholder structure *)
  let dummy_structure =
    {
      e = USet.create ();
      po = USet.create ();
      po_iter = USet.create ();
      rmw = USet.create ();
      lo = USet.create ();
      restrict = Hashtbl.create 0;
      cas_groups = Hashtbl.create 0;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
    }
  in

  Lwt.return
    {
      structure = dummy_structure;
      executions = [];
      events = Hashtbl.create 0;
      valid = false;
    }

(** Perform refinement checking on AST *)
let do_check_refinement _ast =
  (* This is a placeholder implementation *)
  (* The actual implementation would:
     1. Extract the chain of programs from the AST
     2. Create test assertions for each program
     3. Check refinement between consecutive programs
     4. Return the final result
  *)
  (* Placeholder structure *)
  let dummy_structure =
    {
      e = USet.create ();
      po = USet.create ();
      po_iter = USet.create ();
      rmw = USet.create ();
      lo = USet.create ();
      restrict = Hashtbl.create 0;
      cas_groups = Hashtbl.create 0;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
    }
  in

  Lwt.return
    {
      structure = dummy_structure;
      executions = [];
      events = Hashtbl.create 0;
      valid = false;
    }

let step_check_assertions (ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let%lwt ctx = ctx in
    match (ctx.structure, ctx.executions, ctx.events) with
    | Some structure, Some executions, Some events ->
        let execution_list = USet.to_list executions in
          let* assertion_result : assertion_result =
            match ctx.assertions with
            | None | Some [] ->
                Lwt.return { valid = true; ub = false; ub_reasons = [] }
            | Some assertions ->
                Lwt_list.fold_left_s
                  (fun (acc : assertion_result) (assertion : ir_assertion) ->
                    let* (res : assertion_result) =
                      check_assertion assertion execution_list structure events
                        ~exhaustive:ctx.options.exhaustive
                    in
                      if not res.valid then Lwt.return res
                      else
                        Lwt.return
                          {
                            valid = acc.valid && res.valid;
                            ub = acc.ub || res.ub;
                            ub_reasons = acc.ub_reasons @ res.ub_reasons;
                          }
                  )
                  { valid = true; ub = false; ub_reasons = [] }
                  assertions
          in
            ctx.valid <- Some assertion_result.valid;
            ctx.undefined_behaviour <- Some assertion_result.ub;
            Lwt.return ctx
    | _ ->
        Logs.err (fun m ->
            m "Event structure or executions not available for assertion check."
        );
        Lwt.return ctx
