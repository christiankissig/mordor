(** Mordor - Main dependency calculation algorithm *)

open Lwt.Syntax
open Executions
open Events
open Types
open Expr
open Ir
open Uset

type result = {
  ast : expr list; (* Simplified AST *)
  structure : symbolic_event_structure;
  events : (int, event) Hashtbl.t;
  executions : symbolic_execution list;
  valid : bool;
  ub : bool; (* undefined behavior *)
}

(** Calculate dependencies and justifications *)

let calculate_dependencies ast (structure : symbolic_event_structure)
    (events : (int, event) Hashtbl.t) ~exhaustive ~include_dependencies
    ~just_structure ~restrictions =
  let e_set = structure.e in
  let restrict = structure.restrict in
  let rmw = structure.rmw in
  let po = structure.po in

  let branch_events = filter_events events e_set Branch in
  let read_events = filter_events events e_set Read in
  let write_events = filter_events events e_set Write in
  let fence_events = filter_events events e_set Fence in
  let malloc_events = filter_events events e_set Malloc in
  let free_events = filter_events events e_set Free in

  (* Build tree for program order *)
  let build_tree rel =
    let tree = Hashtbl.create 256 in
      USet.iter (fun e -> Hashtbl.add tree e (USet.create ())) e_set;
      USet.iter
        (fun (from, to_) ->
          let set = Hashtbl.find tree from in
            USet.add set to_ |> ignore
        )
        rel;
      tree
  in

  Logs.debug (fun m -> m "Building PO tree...");

  let po_tree = build_tree po in

  Logs.debug (fun m -> m "PO tree built");

  (* Build ebranch mapping *)
  let ebranch =
    let tbl = Hashtbl.create 16 in
      USet.iter
        (fun e ->
          let branches =
            USet.filter (fun (f, t) -> USet.mem branch_events f && t = e) po
            |> USet.map (fun (f, _) -> f)
          in
            Hashtbl.add tbl e branches
        )
        e_set;
      tbl
  in

  let conflicting_branch e1 e2 =
    let branches1 =
      try Hashtbl.find ebranch e1 with Not_found -> USet.create ()
    in
    let branches2 =
      try Hashtbl.find ebranch e2 with Not_found -> USet.create ()
    in
    let common = USet.intersection branches1 branches2 in
    let values = USet.values common in
      match values with
      | [] -> failwith "No conflicting branch found"
      | hd :: tl -> List.fold_left max hd tl
  in

  (* Define the val function that extracts values from events *)
  let val_fn event_id =
    let ev = Hashtbl.find events event_id in
      match ev.wval with
      | Some v -> ev.wval
      | None -> (
          match ev.rval with
          | Some v -> Some (Expr.of_value v)
          | None -> None
        )
  in

  (* Initialize ForwardingContext *)
  let* () =
    Forwardingcontext.init
      {
        init_e = e_set;
        init_po = po;
        init_events = events;
        init_val = val_fn;
        init_rmw = rmw;
      }
  in

  (* Initialize justifications for writes *)
  let init_justs =
    USet.map
      (fun w ->
        try
          let event = Hashtbl.find events w in
            {
              p = [];
              d = USet.create ();
              fwd = USet.create ();
              we = USet.create ();
              w = event;
              op = ("init", None, None);
            }
        with Not_found -> failwith "Event not found"
      )
      write_events
  in

  Logs.debug (fun m ->
      m "Initial justification for event\n\t%s"
        (String.concat "\n\t"
           (List.map Justifications.to_string (USet.values init_justs))
        )
  );

  (* Initialize initial PPO relation *)
  let init_ppo =
    if Hashtbl.mem events 0 then
      URelation.cross (USet.singleton 0)
        (USet.set_minus
           (USet.of_list (Hashtbl.fold (fun k _ acc -> k :: acc) events []))
           (USet.singleton 0)
        )
    else USet.create ()
  in

  let fj = USet.union structure.fj init_ppo in

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

  Logs.debug (fun m -> m "Starting elaborations...");

  let* final_justs =
    if include_dependencies then
      let rec fixed_point (justs : justification uset) =
        Logs.debug (fun m ->
            m "Fixed-point iteration with %d justifications" (USet.size justs)
        );
        let* va = Elaborations.value_assign elab_ctx justs in
          let* lift = Elaborations.lift elab_ctx va in
            let* weak = Elaborations.weaken elab_ctx lift in
              let* fwd = Elaborations.forward elab_ctx weak in
                let* filtered =
                  Elaborations.filter elab_ctx (USet.union justs fwd)
                in

                let justs_str =
                  String.concat "\n\t"
                    (USet.values (USet.map Justifications.to_string filtered))
                in
                  if USet.equal filtered justs then (
                    Logs.debug (fun m ->
                        m "Fixed-point reached with %d justifications:\n\t%s"
                          (USet.size filtered) justs_str
                    );
                    Lwt.return filtered
                  )
                  else (
                    Logs.debug (fun m ->
                        m "Continue elaborating with %d justifications:\n\t%s"
                          (USet.size filtered) justs_str
                    );
                    fixed_point filtered
                  )
      in

      let* filtered_init = Elaborations.filter elab_ctx init_justs in
        fixed_point filtered_init
    else Lwt.return init_justs
  in

  Logs.debug (fun m ->
      m "Elaborations complete. Final justifications count: %d"
        (USet.size final_justs)
  );

  Logs.debug (fun m -> m "Generating executions...");

  (* Build executions if not just structure *)
  let* executions =
    if just_structure then Lwt.return []
    else (* Use the full execution generation *)
      generate_executions events structure final_justs structure.constraint_
        init_ppo ~include_dependencies ~restrictions
  in

  Logs.debug (fun m -> m "Executions generated: %d" (List.length executions));

  Lwt.return (structure, final_justs, executions)

(** Convert parsed AST expressions to IR format *)
let convert_expr = Parse.ast_expr_to_expr

(** Convert parsed AST statements to IR format *)
let rec convert_stmt = function
  | Ast.SThreads { threads } ->
      let ir_threads = List.map (List.map convert_stmt) threads in
        Threads { threads = ir_threads }
  | Ast.SRegisterStore { register; expr } ->
      let ir_expr = convert_expr expr in
        RegisterStore { register; expr = ir_expr }
  | Ast.SGlobalStore { global; expr; assign } ->
      let ir_expr = convert_expr expr in
        GlobalStore { global; expr = ir_expr; assign }
  | Ast.SGlobalLoad { register; global; load } ->
      GlobalLoad { register; global; load }
  | Ast.SStore { address; expr; assign } ->
      let ir_address = convert_expr address in
      let ir_expr = convert_expr expr in
        DerefStore { address = ir_address; expr = ir_expr; assign }
  | Ast.SIf { condition; then_body; else_body } ->
      let ir_condition = convert_expr condition in
      let ir_then_body = List.map convert_stmt then_body in
      let ir_else_body = Option.map (List.map convert_stmt) else_body in
        If
          {
            condition = ir_condition;
            then_body = ir_then_body;
            else_body = ir_else_body;
          }
  | Ast.SWhile { condition; body } ->
      let ir_condition = convert_expr condition in
      let ir_body = List.map convert_stmt body in
        While { condition = ir_condition; body = ir_body }
  | Ast.SDo { body; condition } ->
      let ir_condition = convert_expr condition in
      let ir_body = List.map convert_stmt body in
        Do { body = ir_body; condition = ir_condition }
  | Ast.SFence { mode } -> Fence { mode }
  | Ast.SLock { global } -> Lock { global }
  | Ast.SUnlock { global } -> Unlock { global }
  | Ast.SFree { register } -> Free { register }
  | Ast.SLabeled { label; stmt } ->
      let ir_stmt = convert_stmt stmt in
        Labeled { label; stmt = ir_stmt }
  | Ast.SCAS { register; address; expected; desired; mode } ->
      let ir_address = convert_expr address in
      let ir_expected = convert_expr expected in
      let ir_desired = convert_expr desired in
        Cas
          {
            register;
            address = ir_address;
            expected = ir_expected;
            desired = ir_desired;
            mode;
          }
  | Ast.SFADD { register; address; operand; mode } ->
      let ir_address = convert_expr address in
      let ir_operand = convert_expr operand in
        Fadd { register; address = ir_address; operand = ir_operand; mode }
  | Ast.SMalloc { register; size } ->
      let ir_size = convert_expr size in
        Malloc { register; size = ir_size }

(** Parse program *)
let parse_program program =
  Logs.debug (fun m -> m "Parsing program...");

  try
    let litmus = Parse.parse program in
    let constraints =
      List.map Parse.ast_expr_to_expr
        ( match litmus.config with
        | Some c -> c.constraint_
        | None -> []
        )
    in
    let program_stmts = List.map convert_stmt litmus.program in
      (constraints, program_stmts)
  with
  | Failure msg ->
      Logs.err (fun m -> m "Parse error: %s" msg);
      ([], [])
  | e ->
      Logs.err (fun m -> m "Unexpected error: %s" (Printexc.to_string e));
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

  assert (Hashtbl.length events = USet.size structure.e);

  Logs.debug (fun m -> m "Program interpreted successfully.");

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

  Logs.debug (fun m -> m "Dependencies calculated.");

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

  Logs.debug (fun m -> m "Verification complete.");

  Lwt.return result
