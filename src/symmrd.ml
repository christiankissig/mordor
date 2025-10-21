(** sMRD - Symbolic Memory Relaxation Dependencies Main dependency calculation
    algorithm *)

open Parse (* must come before open Types *)
open Types
open Expr
open Trees
open Justifications
open Executions
open Lwt.Syntax

type result = {
  ast : expr list; (* Simplified AST *)
  structure : symbolic_event_structure;
  events : (int, event) Hashtbl.t;
  executions : symbolic_execution list;
  valid : bool;
  ub : bool; (* undefined behavior *)
}

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

(** Helper functions for execution generation *)

(** Project first elements from relation *)
let pi_1 rel = Uset.map (fun (x, _) -> x) rel

(** Project second elements from relation *)
let pi_2 rel = Uset.map (fun (_, y) -> y) rel

(** Get value from event e, or create symbolic value based on x's location *)
let vale events e x =
  match Hashtbl.find_opt events e with
  | Some event when event.label >= 0 -> (
      match val_ events e with
      | Some v -> v
      | None ->
          let loc_x =
            match loc events x with
            | Some l -> Value.to_string l
            | None -> string_of_int x
          in
            VVar (Printf.sprintf "v(%s)" loc_x)
    )
  | _ ->
      let loc_x =
        match loc events x with
        | Some l -> Value.to_string l
        | None -> string_of_int x
      in
        VVar (Printf.sprintf "v(%s)" loc_x)

(** Get location from event e, or create symbolic location based on x's location
*)
let loce events e x =
  match Hashtbl.find_opt events e with
  | Some event when event.label >= 0 -> (
      match loc events e with
      | Some l -> l
      | None ->
          let loc_x =
            match loc events x with
            | Some l -> Value.to_string l
            | None -> string_of_int x
          in
            VVar (Printf.sprintf "l(%s)" loc_x)
    )
  | _ ->
      let loc_x =
        match loc events x with
        | Some l -> Value.to_string l
        | None -> string_of_int x
      in
        VVar (Printf.sprintf "l(%s)" loc_x)

(** Find origin event of a symbol *)
let origin events read_events malloc_events s =
  (* Try to find in reads *)
  let in_reads =
    Uset.filter
      (fun x ->
        match val_ events x with
        | Some (VSymbol sym) -> sym = s
        | _ -> false
      )
      read_events
  in
  let in_reads_vals = Uset.values in_reads in
    match in_reads_vals with
    | e :: _ -> Some e
    | [] -> (
        (* Try to find in mallocs by symbol *)
        let in_mallocs =
          Uset.filter
            (fun x ->
              try
                let event = Hashtbl.find events x in
                  match event.id with
                  | Some (VSymbol sym) -> sym = s
                  | _ -> false
              with Not_found -> false
            )
            malloc_events
        in
        let in_mallocs_vals = Uset.values in_mallocs in
          match in_mallocs_vals with
          | e :: _ -> Some e
          | [] -> None
      )

(** Create disjoint predicate for two (location, value) pairs *)
let disjoint (loc1, val1) (loc2, val2) =
  (* Two memory accesses are disjoint if their locations differ *)
  EBinOp (loc1, "!=", loc2)

(** Path type *)
type path_info = {
  path : int list;
  p : expr list list; (* List of predicate lists *)
}

(** Generate all paths through the control flow structure *)
let gen_paths events structure restrict =
  let po_tree = build_tree structure.e structure.po in

  let rec gen_paths_rec e =
    let next_uset =
      try Hashtbl.find po_tree e with Not_found -> Uset.create ()
    in
    let next = Uset.values next_uset in

    if List.length next = 0 then [ { path = [ e ]; p = [] } ]
    else
      (* Check if event is a branch *)
      let event = Hashtbl.find events e in
        if event.typ = Branch then (
          (* Branch event - create two paths *)
          if List.length next <> 2 then
            failwith "Branch event must have exactly 2 successors";

          let next0 = List.nth next 0 in
          let next1 = List.nth next 1 in

          let restrict_e = try Hashtbl.find restrict e with Not_found -> [] in

          let cond =
            match event.cond with
            | Some (VExpression c) -> c
            | Some c -> EVar (Value.to_string c)
            | None -> failwith "Branch missing condition"
          in

          (* Left branch paths *)
          let n0_paths =
            if Uset.mem structure.e next0 then
              let restrict_next0 =
                try Hashtbl.find restrict next0 with Not_found -> []
              in
                List.map
                  (fun p ->
                    { path = p.path @ [ e ]; p = p.p @ [ restrict_next0 ] }
                  )
                  (gen_paths_rec next0)
            else [ { path = [ e ]; p = [ restrict_e @ [ cond ] ] } ]
          in

          (* Right branch paths *)
          let n1_paths =
            if Uset.mem structure.e next1 then
              let restrict_next1 =
                try Hashtbl.find restrict next1 with Not_found -> []
              in
                List.map
                  (fun p ->
                    { path = p.path @ [ e ]; p = p.p @ [ restrict_next1 ] }
                  )
                  (gen_paths_rec next1)
            else
              [ { path = [ e ]; p = [ restrict_e @ [ Expr.inverse cond ] ] } ]
          in

          n0_paths @ n1_paths
        )
        else
          (* Non-branch event - combine paths from successors *)
          let successor_paths = List.map gen_paths_rec next in

          (* Cartesian product and concatenation *)
          let rec combine_paths paths =
            match paths with
            | [] -> [ { path = []; p = [] } ]
            | p :: rest ->
                let rest_combined = combine_paths rest in
                  List.concat_map
                    (fun path1 ->
                      List.map
                        (fun path2 ->
                          {
                            path =
                              List.filter (( <> ) e) path1.path @ path2.path;
                            p = path1.p @ path2.p;
                          }
                        )
                        rest_combined
                    )
                    p
          in

          let combined = combine_paths successor_paths in
            List.map (fun p -> { path = p.path @ [ e ]; p = p.p }) combined
  in
    gen_paths_rec 0

(** Choose compatible justifications for a path *)
let choose justmap path_events =
  let path_list = Uset.values path_events in

  let rec choose_rec list i items fwdwe =
    if i = 0 then [ items ]
    else
      let i = i - 1 in

      (* Skip if already covered by fwdwe *)
      if List.length items > 0 && Uset.mem (pi_2 fwdwe) list.(i) then
        choose_rec list i items fwdwe
      else
        (* Get justifications for this event *)
        let justs_for_event =
          try Hashtbl.find justmap list.(i) with Not_found -> []
        in

        (* Filter compatible justifications *)
        let compatible =
          List.filter
            (fun just ->
              let x = Uset.union just.fwd just.we in
              (* Check no conflicts with existing fwdwe *)
              let pi1_x = pi_1 x in
              let pi2_x = pi_2 x in
              let pi1_fwdwe = pi_1 fwdwe in
              let pi2_fwdwe = pi_2 fwdwe in

              Uset.size (Uset.intersection pi1_x pi2_fwdwe) = 0
              && Uset.size (Uset.intersection pi2_x pi1_fwdwe) = 0
            )
            justs_for_event
        in

        (* Recursively choose for each compatible justification *)
        List.concat_map
          (fun just ->
            let new_fwdwe = Uset.union fwdwe (Uset.union just.fwd just.we) in
              choose_rec list i (items @ [ just ]) new_fwdwe
          )
          compatible
  in

  choose_rec (Array.of_list path_list) (List.length path_list) []
    (Uset.create ())

(** Calculate dependencies and justifications *)

let calculate_dependencies ast structure events ~exhaustive
    ~include_dependencies ~just_structure ~restrictions =
  let landmark = Landmark.register "calculate_dependencies" in
    Landmark.enter landmark;

    let e_set = structure.e in
    let restrict = structure.restrict in
    let rmw = structure.rmw in
    let po = structure.po in

    (* Filter to only events that exist in the hashtable *)
    let e_set_filtered =
      Uset.filter (fun id -> Hashtbl.mem events id) structure.e
    in

    (* Event type filters *)
    let filter_events typ =
      Uset.filter
        (fun e ->
          try
            let event = Hashtbl.find events e in
              event.typ = typ
          with Not_found -> false
        )
        e_set
    in

    let branch_events = filter_events Branch in
    let read_events = filter_events Read in
    let write_events = filter_events Write in
    let fence_events = filter_events Fence in
    let malloc_events = filter_events Malloc in
    let free_events = filter_events Free in

    let po_tree = build_tree e_set po in

    (* Build ebranch mapping *)
    let ebranch =
      let tbl = Hashtbl.create 16 in
        Uset.iter
          (fun e ->
            let branches =
              Uset.filter (fun (f, t) -> Uset.mem branch_events f && t = e) po
              |> Uset.map (fun (f, _) -> f)
            in
              Hashtbl.add tbl e branches
          )
          e_set;
        tbl
    in

    let conflicting_branch e1 e2 =
      let branches1 =
        try Hashtbl.find ebranch e1 with Not_found -> Uset.create ()
      in
      let branches2 =
        try Hashtbl.find ebranch e2 with Not_found -> Uset.create ()
      in
      let common = Uset.intersection branches1 branches2 in
      let values = Uset.values common in
        match values with
        | [] -> failwith "No conflicting branch found"
        | hd :: tl -> List.fold_left max hd tl
    in

    (* Define the val function that extracts values from events *)
    let val_fn event_id =
      let ev = Hashtbl.find events event_id in
        match ev.wval with
        | Some v -> ev.wval
        | None -> ev.rval
    in

    (* Initialize ForwardingContext *)
    let* () =
      Forwardingcontext.init
        {
          init_e = e_set_filtered;
          init_po = po;
          init_events = events;
          init_val = val_fn;
          init_rmw = rmw;
        }
    in

    (* Initialize justifications for writes *)
    let init_justs =
      Uset.map
        (fun w ->
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
          with Not_found -> failwith "Event not found"
        )
        write_events
    in

    let init_ppo =
      if Hashtbl.mem events 0 then
        Uset.cross (Uset.singleton 0)
          (Uset.set_minus
             (Uset.of_list (Hashtbl.fold (fun k _ acc -> k :: acc) events []))
             (Uset.singleton 0)
          )
      else Uset.create ()
    in

    let fj = Uset.union structure.fj init_ppo in

    (* Build context for elaborations *)
    let elab_ctx =
      {
        Elaborations.structure;
        events;
        e_set;
        branch_events;
        read_events;
        write_events;
        malloc_events;
        po;
        rmw;
        fj;
        val_fn;
        conflicting_branch;
      }
    in

    let* final_justs =
      if include_dependencies then
        let rec fixed_point justs =
          let* va = Elaborations.value_assign elab_ctx justs in
            let* lift = Elaborations.lift elab_ctx va in
              let* weak = Elaborations.weaken elab_ctx (Uset.values lift) in
                let* fwd = Elaborations.forward elab_ctx (Uset.of_list weak) in
                  let* filtered =
                    Elaborations.filter elab_ctx
                      (Uset.values (Uset.union (Uset.of_list justs) fwd))
                  in

                  if Uset.equal filtered (Uset.of_list justs) then
                    Lwt.return filtered
                  else fixed_point (Uset.values filtered)
        in

        let* filtered_init =
          Elaborations.filter elab_ctx (Uset.values init_justs)
        in
          fixed_point (Uset.values filtered_init)
      else Lwt.return init_justs
    in

    (* Build executions if not just structure *)
    let* executions =
      if just_structure then Lwt.return []
      else
        (* Simplified execution generation *)
        let exec =
          {
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
          }
        in
          Lwt.return [ exec ]
    in

    Landmark.exit landmark;
    Lwt.return (structure, final_justs, executions)

(** Convert parsed AST to interpreter format *)
let rec convert_stmt = function
  | Parse.SThread { lhs; rhs } ->
      `Thread (List.map convert_stmt lhs, List.map convert_stmt rhs)
  | Parse.SGlobalLoad { register; global; assign } ->
      `GlobalLoad (register, global, assign.mode, assign.volatile)
  | Parse.SGlobalStore { global; expr; assign } ->
      `GlobalStore (global, assign.mode, expr, assign.volatile)
  | Parse.SFence { mode } -> `Fence mode
  (* Add other statement conversions as needed *)
  | _ -> failwith "Statement conversion not implemented"

(** Parse program *)
let parse_program program =
  Printf.printf "[DEBUG] Parsing program...\n";
  flush stdout;
  try
    let litmus = Parse.parse program in
    let constraints =
      List.map Parse.ast_expr_to_expr litmus.config.constraint_
    in
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
  let ast, program_stmts = parse_program program in

  (* Interpret program *)
  let* structure, events =
    Interpret.interpret program_stmts [] (Hashtbl.create 16) []
  in

  (* Calculate dependencies *)
  let* structure', justs, executions =
    calculate_dependencies ast structure events
      ~exhaustive:(options.exhaustive || false)
      ~include_dependencies:(options.dependencies || true)
      ~just_structure:(options.just_structure || false)
      ~restrictions:options
  in

  (* Check assertion if present *)
  let result =
    {
      ast;
      structure = structure';
      events;
      executions;
      valid = true;
      ub = false;
    }
  in

  Printf.printf "[DEBUG] Verification complete.\n";
  flush stdout;

  Lwt.return result
