open Assertion
open Ast
open Context
open Ir
open Lwt.Syntax
open Types

type ir_stmt = unit Ir.ir_stmt
type ir_node = unit Ir.ir_node
type ir_assertion = unit Ir.ir_assertion
type ir_litmus = unit Ir.ir_litmus

(** Parse a litmus test from a string *)

let parse prsr src =
  let lexbuf = Lexing.from_string src in
    try prsr Lexer.token lexbuf with
    | Lexer.Lexer_error msg -> failwith (Printf.sprintf "Lexer error: %s" msg)
    | Parser.Error ->
        let pos = lexbuf.lex_curr_p in
        let msg =
          Printf.sprintf "Parse error at line %d, column %d" pos.pos_lnum
            (pos.pos_cnum - pos.pos_bol)
        in
          failwith msg

let parse_litmus = parse Parser.litmus
let parse_expr = parse Parser.expr_only

(** Conversion functions to Types module *)

(** Convert ast_expr to Types.expr *)
let rec ast_expr_to_expr : ast_expr -> Types.expr = function
  | EInt n -> Types.ENum n
  | ERegister r -> Types.EVar r
  | EGlobal g -> Types.EVar g
  | EAtLoc l -> Types.EVar l
  | EASet s -> Types.EVar ("." ^ s)
  | EBinOp (l, op, r) ->
      Types.EBinOp (ast_expr_to_expr l, op, ast_expr_to_expr r)
  | EUnOp (op, e) -> Types.EUnOp (op, ast_expr_to_expr e)
  | ETuple (e1, e2) ->
      (* Represent tuple as a special binop *)
      Types.EBinOp (ast_expr_to_expr e1, ",", ast_expr_to_expr e2)

(** Convert ast_mode to Types.mode *)
let ast_mode_to_mode : mode -> Types.mode = function
  | Nonatomic -> Types.Nonatomic
  | Relaxed -> Types.Relaxed
  | Release -> Types.Release
  | ReleaseAcquire -> Types.ReleaseAcquire
  | Acquire -> Types.Acquire
  | SC -> Types.SC
  | Normal -> Types.Normal
  | Strong -> Types.Strong

(** Helper to convert expression lists *)
let convert_expr_list exprs = List.map ast_expr_to_expr exprs

(** Convert parsed AST statements to IR format *)

let make_ir_node stmt = { stmt; annotations = () }

(* TODO rec to handle label case; use ctx annotation instead *)
let rec convert_stmt_open ~recurse = function
  | Ast.SThreads { threads } ->
      let ir_threads = List.map (List.map recurse) threads in
        Threads { threads = ir_threads }
  | Ast.SRegisterStore { register; expr } ->
      let ir_expr = ast_expr_to_expr expr in
        RegisterStore { register; expr = ir_expr }
  | Ast.SRegisterRefAssign { register; global } ->
      RegisterRefAssign { register; global }
  | Ast.SGlobalStore { global; expr; assign } ->
      let ir_expr = ast_expr_to_expr expr in
        GlobalStore { global; expr = ir_expr; assign }
  | Ast.SGlobalLoad { register; global; load } ->
      GlobalLoad { register; global; load }
  | Ast.SStore { address; expr; assign } ->
      let ir_address = ast_expr_to_expr address in
      let ir_expr = ast_expr_to_expr expr in
        DerefStore { address = ir_address; expr = ir_expr; assign }
  | Ast.SLoad { register; address; load } ->
      let ir_address = ast_expr_to_expr address in
        DerefLoad { register; address = ir_address; load }
  | Ast.SIf { condition; then_body; else_body } ->
      let ir_condition = ast_expr_to_expr condition in
      let ir_then_body = List.map recurse then_body in
      let ir_else_body = Option.map (List.map recurse) else_body in
        If
          {
            condition = ir_condition;
            then_body = ir_then_body;
            else_body = ir_else_body;
          }
  | Ast.SWhile { condition; body } ->
      let ir_condition = ast_expr_to_expr condition in
      let ir_body = List.map recurse body in
        While { condition = ir_condition; body = ir_body }
  | Ast.SDo { body; condition } ->
      let ir_condition = ast_expr_to_expr condition in
      let ir_body = List.map recurse body in
        Do { body = ir_body; condition = ir_condition }
  | Ast.SFence { mode } -> Fence { mode }
  | Ast.SLock { global } -> Lock { global }
  | Ast.SUnlock { global } -> Unlock { global }
  | Ast.SFree { register } -> Free { register }
  | Ast.SLabeled { label; stmt } ->
      let ir_stmt = convert_stmt_open ~recurse stmt in
        Labeled { label; stmt = make_ir_node ir_stmt }
  | Ast.SCAS { register; address; expected; desired; load_mode; assign_mode } ->
      let ir_address = ast_expr_to_expr address in
      let ir_expected = ast_expr_to_expr expected in
      let ir_desired = ast_expr_to_expr desired in
        Cas
          {
            register;
            address = ir_address;
            expected = ir_expected;
            desired = ir_desired;
            load_mode;
            assign_mode;
          }
  | Ast.SFADD { register; address; operand; rmw_mode; load_mode; assign_mode }
    ->
      let ir_address = ast_expr_to_expr address in
      let ir_operand = ast_expr_to_expr operand in
        Fadd
          {
            register;
            address = ir_address;
            operand = ir_operand;
            rmw_mode;
            load_mode;
            assign_mode;
          }
  | Ast.SRegMalloc { register; size } ->
      let ir_size = ast_expr_to_expr size in
        RegMalloc { register; size = ir_size }
  | Ast.SGlobalMalloc { global; size } ->
      let ir_size = ast_expr_to_expr size in
        GlobalMalloc { global; size = ir_size }
  | Ast.SSkip -> Skip

let rec convert_stmt ast_node =
  convert_stmt_open ~recurse:convert_stmt ast_node.stmt |> make_ir_node

(** Convert parsed AST litmus test to IR format *)

let rec convert_assertion ast_assertion =
  match ast_assertion with
  | AOutcome { outcome; condition; model } ->
      (* Check if condition is the special "ub" marker *)
      let ir_condition =
        match condition with
        | EGlobal "ub" -> Ir.CondUB
        | _ -> Ir.CondExpr (ast_expr_to_expr condition)
      in
      let ir_outcome = outcome_of_string outcome in
        Outcome { outcome = ir_outcome; condition = ir_condition; model }
  | AModel { model } -> Model { model }
  | AChained { model; outcome; rest } ->
      Chained
        {
          model;
          outcome = outcome_of_string outcome;
          rest = convert_litmus rest;
        }

and convert_litmus ast_litmus =
  let name =
    Option.map (fun (c : ast_config) -> c.name) ast_litmus.config |> Option.join
  in
  let model =
    Option.map (fun (c : ast_config) -> c.model) ast_litmus.config
    |> Option.join
  in
  let values =
    match ast_litmus.config with
    | Some config -> config.values
    | None -> []
  in
  let defacto =
    match ast_litmus.config with
    | Some config -> convert_expr_list config.defacto
    | None -> []
  in
  let constraints =
    match ast_litmus.config with
    | Some config -> convert_expr_list config.constraints
    | None -> []
  in
  let config = { name; model; values; defacto; constraints } in
  let assertions =
    match ast_litmus.assertion with
    | Some assertion -> [ convert_assertion assertion ]
    | None -> []
  in
  let program = List.map convert_stmt ast_litmus.program in
    { config; assertions; program }

(** Parse litmus to AST and convert from AST to IR *)

let parse_and_convert_litmus ~validate_ast src =
  Logs.debug (fun m -> m "Parsing program...");

  try
    let litmus_ast = parse_litmus src in
      validate_ast litmus_ast;
      convert_litmus litmus_ast
  with
  | Failure msg ->
      Logs.err (fun m -> m "Parse error: %s" msg);
      failwith ("Parse error: " ^ msg)
  | e ->
      Logs.err (fun m -> m "Unexpected error: %s" (Printexc.to_string e));
      failwith ("Unexpected error: " ^ Printexc.to_string e)

(** Post-parse validation on ASTs *)

(* Validate that there are no thread spawns inside loops *)
let rec validate_no_threads_under_loop (ast : ast_node list) : bool =
  let rec traverse handle_threads handle_loop nodes =
    List.for_all
      (fun (node : Ast.ast_node) ->
        match node.stmt with
        | Ast.SThreads { threads } -> handle_threads threads
        | Ast.SWhile { condition; body } | Ast.SDo { body; condition } ->
            handle_loop body
        | Ast.SIf { condition; then_body; else_body } ->
            traverse handle_threads handle_loop then_body
            && Option.value
                 (Option.map (traverse handle_threads handle_loop) else_body)
                 ~default:true
        | _ -> true
      )
      nodes
  in
  (* no_threads: forbid threads everywhere *)
  let rec no_threads nodes =
    traverse
      (fun _ -> false) (* threads not allowed *)
      no_threads (* recurse into loop bodies *)
      nodes
  in
    (* Main validation: allow threads at top level, but check loop bodies *)
    traverse
      (* validate thread bodies *)
      (fun threads -> List.for_all validate_no_threads_under_loop threads
      )
      no_threads (* inside loops, use no_threads checker *)
      ast

(** Pipeline step for parsing litmus tests *)

let step_parse_litmus (ctx_lwt : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let validate_ast (litmus_ast : ast_litmus) : unit =
    if not (validate_no_threads_under_loop (litmus_ast : ast_litmus).program)
    then
      failwith "Validation error: Thread spawns inside loops are not allowed."
    else ()
  in
    let* ctx = ctx_lwt in
      match ctx.litmus with
      | Some program ->
          let litmus_ir = parse_and_convert_litmus ~validate_ast program in
          let { config; assertions; program } = litmus_ir in
            Option.iter
              (fun model ->
                ctx.options.model <- model;
                apply_model_options ctx model
              )
              config.model;
            Option.iter (fun name -> ctx.litmus_name <- name) config.name;
            ctx.litmus_constraints <- Some config.constraints;
            ctx.program_stmts <- Some program;
            ctx.assertions <-
              ( match assertions with
              | [] -> None
              | [ a ] -> (
                  match a with
                  | Ir.Outcome { model = Some model; _ } | Ir.Model { model } ->
                      apply_model_options ctx model;
                      Logs.info (fun m -> m "Applied model options for %s" model);
                      Some a
                  | _ -> Some a
                )
              | _ -> failwith "Multiple assertions are not supported."
              );
            Lwt.return ctx
      | None ->
          Logs.err (fun m -> m "No program provided for parsing.");
          Lwt.return ctx
