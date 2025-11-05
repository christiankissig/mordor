open Ast
open Context
open Ir
open Lwt.Syntax
open Types

(** Parse a litmus test from a string *)
let parse src =
  let lexbuf = Lexing.from_string src in
    try Parser.litmus Lexer.token lexbuf with
    | Lexer.Lexer_error msg -> failwith (Printf.sprintf "Lexer error: %s" msg)
    | Parser.Error ->
        let pos = lexbuf.lex_curr_p in
        let msg =
          Printf.sprintf "Parse error at line %d, column %d" pos.pos_lnum
            (pos.pos_cnum - pos.pos_bol)
        in
          failwith msg

(** Parse an expression from a string *)
let parse_expr src =
  let lexbuf = Lexing.from_string src in
    try Parser.expr_only Lexer.token lexbuf with
    | Lexer.Lexer_error msg -> failwith (Printf.sprintf "Lexer error: %s" msg)
    | Parser.Error ->
        let pos = lexbuf.Lexing.lex_curr_p in
          failwith
            (Printf.sprintf "Parse error at line %d, column %d"
               pos.Lexing.pos_lnum
               (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
            )

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
  | Acquire -> Types.Acquire
  | SC -> Types.SC
  | Normal -> Types.Normal
  | Strong -> Types.Strong

(** Helper to convert expression lists *)
let convert_expr_list exprs = List.map ast_expr_to_expr exprs

(** Convert parsed AST statements to IR format *)
let rec convert_stmt = function
  | Ast.SThreads { threads } ->
      let ir_threads = List.map (List.map convert_stmt) threads in
        Threads { threads = ir_threads }
  | Ast.SRegisterStore { register; expr } ->
      let ir_expr = ast_expr_to_expr expr in
        RegisterStore { register; expr = ir_expr }
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
      let ir_then_body = List.map convert_stmt then_body in
      let ir_else_body = Option.map (List.map convert_stmt) else_body in
        If
          {
            condition = ir_condition;
            then_body = ir_then_body;
            else_body = ir_else_body;
          }
  | Ast.SWhile { condition; body } ->
      let ir_condition = ast_expr_to_expr condition in
      let ir_body = List.map convert_stmt body in
        While { condition = ir_condition; body = ir_body }
  | Ast.SDo { body; condition } ->
      let ir_condition = ast_expr_to_expr condition in
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
      let ir_address = ast_expr_to_expr address in
      let ir_expected = ast_expr_to_expr expected in
      let ir_desired = ast_expr_to_expr desired in
        Cas
          {
            register;
            address = ir_address;
            expected = ir_expected;
            desired = ir_desired;
            mode;
          }
  | Ast.SFADD { register; address; operand; mode } ->
      let ir_address = ast_expr_to_expr address in
      let ir_operand = ast_expr_to_expr operand in
        Fadd { register; address = ir_address; operand = ir_operand; mode }
  | Ast.SMalloc { register; size } ->
      let ir_size = ast_expr_to_expr size in
        Malloc { register; size = ir_size }

(** Parse program *)
let parse_program program =
  Logs.debug (fun m -> m "Parsing program...");

  try
    let litmus = parse program in
    let constraints =
      List.map ast_expr_to_expr
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

let step_parse_program (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in
    match ctx.litmus with
    | Some program ->
        let constraints, statements = parse_program program in
          ctx.litmus_constraints <- Some constraints;
          ctx.program_stmts <- Some statements;
          Lwt.return ctx
    | None ->
        Logs.err (fun m -> m "No program provided for parsing.");
        Lwt.return ctx
