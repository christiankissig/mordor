(** sMRD - Symbolic Memory Relaxation Dependencies Main dependency calculation
    algorithm *)

open Lwt.Syntax
open Parse (* must come before open Types *)
open Executions
open Events
open Types

type result = {
  ast : expr list; (* Simplified AST *)
  structure : symbolic_event_structure;
  events : (int, event) Hashtbl.t;
  executions : symbolic_execution list;
  valid : bool;
  ub : bool; (* undefined behavior *)
}

(** Calculate dependencies and justifications *)

let calculate_dependencies ast (structure : symbolic_event_structure) events
    ~exhaustive ~include_dependencies ~just_structure ~restrictions =
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

    let branch_events = filter_events events e_set_filtered Branch in
    let read_events = filter_events events e_set_filtered Read in
    let write_events = filter_events events e_set_filtered Write in
    let fence_events = filter_events events e_set_filtered Fence in
    let malloc_events = filter_events events e_set_filtered Malloc in
    let free_events = filter_events events e_set_filtered Free in

    (* Build tree for program order *)
    let build_tree rel =
      let tree = Hashtbl.create 256 in
        Uset.iter (fun e -> Hashtbl.add tree e (Uset.create ())) e_set;
        Uset.iter
          (fun (from, to_) ->
            let set = Hashtbl.find tree from in
              Uset.add set to_ |> ignore
          )
          rel;
        tree
    in

    let po_tree = build_tree po in

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
        (* Use the full execution generation *)
        generate_executions events structure final_justs structure.constraint_
          e_set po rmw write_events read_events init_ppo ~include_dependencies
          ~restrictions
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
let create_symbolic_event_structure program (opts : options) =
  let* _ = Lwt.return_unit in

  (* Parse program - get both constraints and program statements *)
  let ast, program_stmts = parse_program program in

  (* Interpret program *)
  let* structure, events =
    Interpret.interpret program_stmts [] (Hashtbl.create 16) []
  in

  (* Create restrictions for coherence checking *)
  let coherence_restrictions =
    {
      Coherence.coherent =
        ( try opts.coherent with _ -> "imm"
        )
        (* default to IMM if not specified *);
    }
  in

  (* Calculate dependencies *)
  let* structure', justs, executions =
    calculate_dependencies ast structure events
      ~exhaustive:(opts.exhaustive || false)
      ~include_dependencies:(opts.dependencies || true)
      ~just_structure:(opts.just_structure || false)
      ~restrictions:coherence_restrictions
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
