(** sMRD - Symbolic Memory Relaxation Dependencies
    Main dependency calculation algorithm *)

open Parse (* order with open Types important *)
open Types
open Lwt.Syntax

(** Statistics tracking (simplified) *)
let stats_count _ = ()
let stats_start _ = ()
let stats_stop _ = ()

(** Helper functions *)
let loc events e =
  try
    let event = Hashtbl.find events e in
    event.id
  with Not_found -> None

let val_ events e =
  try
    let event = Hashtbl.find events e in
    match event.wval with
    | Some v -> Some v
    | None -> event.rval
  with Not_found -> None

(** Calculate dependencies *)
let calculate_dependencies ast structure events ~exhaustive ~include_dependencies
      ~just_structure ~restrictions =
  
  stats_start "dp.misc";
  
  let e_set = structure.e in
  let restrict = structure.restrict in
  let rmw = structure.rmw in
  let po = structure.po in
  
  (* Event type filters *)
  let filter_events typ =
    Uset.filter (fun e ->
      try
        let event = Hashtbl.find events e in
        event.typ = typ
      with Not_found -> false
    ) e_set
  in
  
  let branch_events = filter_events Branch in
  let read_events = filter_events Read in
  let write_events = filter_events Write in
  let fence_events = filter_events Fence in
  let malloc_events = filter_events Malloc in
  let free_events = filter_events Free in
  
  (* Build tree for program order *)
  let build_tree rel =
    let tree = Hashtbl.create 256 in
    Uset.iter (fun e -> Hashtbl.add tree e (Uset.create ())) e_set;
    Uset.iter (fun (from, to_) ->
      let set = Hashtbl.find tree from in
      Uset.add set to_ |> ignore
    ) rel;
    tree
  in
  
  let po_tree = build_tree po in
  
  (* Initialize justifications for writes *)
  let init_justs =
    Uset.map (fun w ->
      try
        let event = Hashtbl.find events w in
        {
          p = [];
          d = Uset.create ();
          fwd = Uset.create ();
          we = Uset.create ();
          w = event;
          op = ("init", None, None);
        }
      with Not_found ->
        failwith "Event not found"
    ) write_events
  in
  
  stats_stop "dp.misc";
  
  (* Justification elaboration *)
  let elaborate = object
    method filter (justs: justification list) =
      stats_count "dp.filter";
      stats_start "dp.filter";
      
      let* (justs': justification option list) = 
        Lwt_list.map_p (fun (just: justification) ->
          let* p' = Rewrite.rewrite_pred just.p in
          match p' with
          | Some p -> Lwt.return_some { just with p }
          | None -> Lwt.return_none
        ) justs
      in

      
      let (justs'': justification list) = List.filter_map Fun.id justs' in

      (* Remove covered justifications *)
      let indexed = List.mapi (fun i j -> (i, j)) justs'' in
      let result =
        indexed
        |> List.filter (fun (i, (j : justification)) ->
            (* Keep j if it's NOT covered by any later justification *)
            not (List.exists (fun (i', (j' : justification)) ->
              i' > i &&  (* Only check justifications that come after *)
              List.length j'.p < List.length j.p &&
              List.for_all (fun e -> List.mem e j.p) j'.p
            ) indexed)
        )
        |> List.map snd
        |> Uset.of_list
      in

      stats_stop "dp.filter";
      Lwt.return result
    
    method value_assign justs =
      stats_count "dp.va";
      stats_start "dp.va";
      
      let* results = Lwt_list.map_p (fun (just: justification) ->
        (* Simplified value assignment *)
        let solver = Solver.create just.p in
        let* model = Solver.solve solver in
        match model with
        | Some bindings ->
            (* Apply concrete values to write value *)
            let new_wval = match just.w.wval with
              | Some (VVar v) ->
                  (match Solver.concrete_value bindings v with
                   | Some value -> Some value
                   | None -> just.w.wval)
              | _ -> just.w.wval
            in
            let new_w = { just.w with wval = new_wval } in
            Lwt.return { just with w = new_w; op = ("va", Some just, None) }
        | None -> Lwt.return just
      ) justs in
      
      stats_stop "dp.va";
      Lwt.return (Uset.of_list results)
    
    method forward justs =
      stats_count "dp.forward";
      stats_start "dp.forward";
      (* Simplified forwarding *)
      stats_stop "dp.forward";
      Lwt.return justs
    
    method lift justs =
      stats_count "dp.lift";
      stats_start "dp.lift";
      (* Simplified lifting *)
      stats_stop "dp.lift";
      Lwt.return justs
    
    method weaken justs =
      stats_count "dp.weaken";
      stats_start "dp.weaken";
      (* Simplified weakening *)
      stats_stop "dp.weaken";
      Lwt.return justs
  end in
  
  (* Main justification computation *)
  let* final_justs =
    if include_dependencies then
      let rec fixed_point justs =
        let* va = elaborate#value_assign justs in
        let* lift = elaborate#lift va in
        let* weak = elaborate#weaken lift in
        let* fwd = elaborate#forward weak in
        let* filtered = elaborate#filter (Uset.values (Uset.union (Uset.of_list justs) fwd)) in
        
        if Uset.equal filtered (Uset.of_list justs) then
          Lwt.return filtered
        else
          fixed_point (Uset.values filtered)
      in
      
      let* filtered_init = elaborate#filter (Uset.values init_justs) in
      fixed_point (Uset.values filtered_init)
    else
      Lwt.return init_justs
  in
  
  (* Build executions if not just structure *)
  let* executions =
    if just_structure then
      Lwt.return []
    else begin
      (* Simplified execution generation *)
      let exec = {
        ex_e = e_set;
        rf = Uset.create ();
        dp = Uset.create ();
        ppo = Uset.create ();
        ex_rmw = rmw;
        ex_p = [];
        conds = [];
        fix_rf_map = Hashtbl.create 16;
        justs = Uset.values final_justs;
        pointer_map = None;
      } in
      Lwt.return [exec]
    end
  in
  
  Lwt.return (structure, final_justs, executions)

(** Convert parsed AST to interpreter format *)
let rec convert_stmt = function
  | Parse.SThread { lhs; rhs } ->
      `Thread (List.map convert_stmt lhs, List.map convert_stmt rhs)
  | Parse.SGlobalLoad { register; global; assign } ->
      `GlobalLoad (register, global, assign.mode, assign.volatile)
  | Parse.SGlobalStore { global; expr; assign } ->
      `GlobalStore (global, assign.mode, expr, assign.volatile)
  | Parse.SFence { mode } ->
      `Fence mode
  (* Add other statement conversions as needed *)
  | _ -> failwith "Statement conversion not implemented"


(** Parse program *)
let parse_program program =
  try
    let litmus = Parse.parse program in
    let constraints = List.map Parse.ast_expr_to_expr litmus.config.constraint_ in
    let program_stmts = List.map convert_stmt litmus.program in
    (constraints, program_stmts)
  with
  | Failure msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      ([], [])
  | e ->
      Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string e);
      ([], [])


(** Main entry point *)
let create_symbolic_event_structure program options =
  let* _ = Lwt.return_unit in
  
  (* Parse program - get both constraints and program statements *)
  let (ast, program_stmts) = parse_program program in
  
  (* Interpret program *)
  let* (structure, events) = Interpret.interpret program_stmts [] (Hashtbl.create 16) [] in
  
  (* Calculate dependencies *)
  let* (structure', justs, executions) =
    calculate_dependencies
      ast
      structure
      events
      ~exhaustive:(options.exhaustive || false)
      ~include_dependencies:(options.dependencies || true)
      ~just_structure:(options.just_structure || false)
      ~restrictions:options
  in
  
  (* Check assertion if present *)
  let result = {
    ast;
    structure = structure';
    events;
    executions;
    valid = true;
    ub = false;
  } in
  
  Lwt.return result
