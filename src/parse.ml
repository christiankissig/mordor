open Assertion
open Ast
open Context
open Ir
open Parser_state
open Lwt.Syntax

(** Parse a litmus test from a string *)

(* A parse error names the line and the 1-based column where the token it
   failed on starts, and the token. It used to give the column where the token
   ended, which points past it, and not say what the token was.

   The column is counted in [src] from the token's offset rather than read off
   the lexer's positions: the lexer winds [pos_cnum] back over the whitespace it
   skips, so those positions do not count the whitespace before a token. *)
let parse prsr src =
  reset_parser_state ();
  let lexbuf = Lexing.from_string src in
  let error_at detail =
    let offset = lexbuf.lex_abs_pos + lexbuf.lex_start_pos in
    let line_start =
      if offset = 0 then 0
      else
        match String.rindex_from_opt src (offset - 1) '\n' with
        | Some i -> i + 1
        | None -> 0
    in
      failwith
        (Printf.sprintf "Parse error at line %d, column %d: %s"
           lexbuf.lex_start_p.pos_lnum
           (offset - line_start + 1)
           detail
        )
  in
    try prsr Lexer.token lexbuf with
    | Lexer.Lexer_error msg -> error_at msg
    | Parser.Error -> (
        match Lexing.lexeme lexbuf with
        | "" -> error_at "unexpected end of input"
        | token -> error_at (Printf.sprintf "unexpected %S" token)
      )

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

(** Helper to convert expression lists *)
let convert_expr_list exprs = List.map ast_expr_to_expr exprs

(** Convert parsed AST statements to IR format *)

let make_ir_node ~source_span ~thread_ctx ~loop_ctx stmt =
  { stmt; annotations = { source_span; thread_ctx; loop_ctx } }

let rec add_loop loop_id ir_node =
  let stmt, ann = (ir_node.stmt, ir_node.annotations) in
  let new_loop_ctx =
    match ann.loop_ctx with
    | Some ctx -> Some { ctx with loops = loop_id :: ctx.loops }
    | None -> Some { lid = loop_id; loops = [ loop_id ] }
  in
    match stmt with
    | While { condition; body } ->
        let new_body = List.map (fun n -> add_loop loop_id n) body in
          {
            stmt = While { condition; body = new_body };
            annotations = { ann with loop_ctx = new_loop_ctx };
          }
    | Do { body; condition } ->
        let new_body = List.map (fun n -> add_loop loop_id n) body in
          {
            stmt = Do { body = new_body; condition };
            annotations = { ann with loop_ctx = new_loop_ctx };
          }
    | If { condition; then_body; else_body } ->
        let new_then_body = List.map (fun n -> add_loop loop_id n) then_body in
        let new_else_body =
          Option.map
            (fun body -> List.map (fun n -> add_loop loop_id n) body)
            else_body
        in
          {
            stmt =
              If
                {
                  condition;
                  then_body = new_then_body;
                  else_body = new_else_body;
                };
            annotations = { ann with loop_ctx = new_loop_ctx };
          }
    | Threads { threads } ->
        let new_threads =
          List.map (List.map (fun n -> add_loop loop_id n)) threads
        in
          {
            stmt = Threads { threads = new_threads };
            annotations = { ann with loop_ctx = new_loop_ctx };
          }
    | _ -> { stmt; annotations = { ann with loop_ctx = new_loop_ctx } }

let rec convert_stmt_open ~recurse ~source_span ~thread_ctx ~loop_ctx = function
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
      let ir_body =
        List.map
          (fun ir_node ->
            match loop_ctx with
            | None -> ir_node
            | Some loop_ctx -> add_loop loop_ctx.lid ir_node
          )
          ir_body
      in
        While { condition = ir_condition; body = ir_body }
  | Ast.SDo { body; condition } ->
      let ir_condition = ast_expr_to_expr condition in
      let ir_body = List.map recurse body in
      let ir_body =
        List.map
          (fun ir_node ->
            match loop_ctx with
            | None -> ir_node
            | Some loop_ctx -> add_loop loop_ctx.lid ir_node
          )
          ir_body
      in
        Do { body = ir_body; condition = ir_condition }
  | Ast.SFence { mode } -> Fence { mode }
  | Ast.SLock { global } -> Lock { global }
  | Ast.SUnlock { global } -> Unlock { global }
  | Ast.SFree { pointer = ERegister register } -> Free { register }
  | Ast.SFree { pointer } ->
      (* [validate_program] has already refused this. *)
      invalid_arg ("free of a non-register: " ^ Ast.expr_to_string pointer)
  | Ast.SLabeled { label; stmt } ->
      let ir_stmt =
        convert_stmt_open ~recurse ~source_span ~thread_ctx ~loop_ctx stmt
      in
        Labeled
          {
            label;
            stmt = make_ir_node ~source_span ~thread_ctx ~loop_ctx ir_stmt;
          }
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

let rec convert_stmt (ast_node : ast_node) =
  let source_span = ast_node.source_span in
  let thread_ctx = ast_node.thread_ctx in
  let loop_ctx = ast_node.loop_ctx in
  let ir_node =
    convert_stmt_open ~recurse:convert_stmt ~source_span ~thread_ctx ~loop_ctx
      ast_node.stmt
    |> make_ir_node ~source_span ~thread_ctx ~loop_ctx
  in
    ir_node

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
  (* TODO TBC program wide guarantees *)
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

(** {1 Expressions range over registers}

    A program touches a global only through a load or a store statement, each
    its own event, and takes a global's address only by [r := &x]. Everywhere
    else an expression is over registers and constants. A pointer held in a
    global is loaded into a register before it is used.

    The grammar has one expression language for programs and assertions, and an
    assertion does name globals, so it cannot refuse them there. Accepted in a
    program, a global stood for its own address rather than its value:
    [r := x + 1] added one to where [x] lives, [if (x = 1)] compared that, and
    [*p := v] wrote to [p] itself. [&x] reached the solver, which has no such
    operator. *)

(** [program_expression_error e] is what is wrong with [e] as an expression in a
    program, if anything. *)
let rec program_expression_error : ast_expr -> string option = function
  | EInt _ | ERegister _ -> None
  | EGlobal g ->
      Some
        (Printf.sprintf
           "global variable %s in an expression; load it into a register first \
            (r := %s)"
           g g
        )
  | EAtLoc l ->
      Some
        (Printf.sprintf
           "location @%s in an expression; a program's expressions range over \
            registers"
           l
        )
  | EASet s ->
      Some (Printf.sprintf "set .%s in an expression; sets are for assertions" s)
  | EUnOp ("&", _) ->
      Some
        "address-of in an expression; take the address into a register first \
         (r := &x)"
  | EUnOp (_, e) -> program_expression_error e
  | EBinOp (l, _, r) | ETuple (l, r) -> (
      match program_expression_error l with
      | None -> program_expression_error r
      | error -> error
    )

(** [statement_error stmt] is what is wrong with the expressions [stmt] carries
    itself, not counting the statements nested in it. *)
let rec statement_error : ast_stmt -> string option = function
  | SFree { pointer = EGlobal g } ->
      Some
        (Printf.sprintf
           "free of global variable %s; load the pointer into a register first \
            (r := %s; free(r))"
           g g
        )
  | SLabeled { stmt; _ } -> statement_error stmt
  | stmt ->
      let exprs =
        match stmt with
        | SRegisterStore { expr; _ } | SGlobalStore { expr; _ } -> [ expr ]
        | SLoad { address; _ } -> [ address ]
        | SStore { address; expr; _ } -> [ address; expr ]
        | SCAS { address; expected; desired; _ } ->
            [ address; expected; desired ]
        | SFADD { address; operand; _ } -> [ address; operand ]
        | SIf { condition; _ } | SWhile { condition; _ } | SDo { condition; _ }
          -> [ condition ]
        | SRegMalloc { size; _ } | SGlobalMalloc { size; _ } -> [ size ]
        | SFree { pointer } -> [ pointer ]
        | SThreads _
        | SRegisterRefAssign _
        | SGlobalLoad _
        | SFence _
        | SLock _
        | SUnlock _
        | SLabeled _
        | SSkip -> []
      in
        List.find_map program_expression_error exprs

let rec nested_statements : ast_stmt -> ast_node list = function
  | SThreads { threads } -> List.concat threads
  | SIf { then_body; else_body; _ } ->
      then_body @ Option.value else_body ~default:[]
  | SWhile { body; _ } | SDo { body; _ } -> body
  | SLabeled { stmt; _ } -> nested_statements stmt
  | _ -> []

(** The 1-based column a statement starts at in [src].

    A span's [start_col] is not that. The lexer winds [pos_cnum] back over the
    blanks before a token, so a statement's span starts where the previous token
    on its line ended, or at 0 when it is the first on its line. The statement
    itself is the first non-blank character from there. *)
let span_column src (span : Types.source_span) =
  match List.nth_opt (String.split_on_char '\n' src) (span.start_line - 1) with
  | None -> span.start_col + 1
  | Some line ->
      let rec skip_blanks i =
        if i < String.length line && String.contains " \t\r" line.[i] then
          skip_blanks (i + 1)
        else i
      in
        skip_blanks span.start_col + 1

(** [validate_program src litmus] fails with a parse error naming the first
    statement, in this program or a chained one, whose expressions are not over
    registers. *)
let rec validate_program src (litmus : ast_litmus) =
  let rec check (node : ast_node) =
    ( match statement_error node.stmt with
    | None -> ()
    | Some detail -> (
        match node.source_span with
        | Some span ->
            failwith
              (Printf.sprintf "Parse error at line %d, column %d: %s"
                 span.start_line (span_column src span) detail
              )
        | None -> failwith ("Parse error: " ^ detail)
      )
    );
    List.iter check (nested_statements node.stmt)
  in
    List.iter check litmus.program;
    match litmus.assertion with
    | Some (AChained { rest; _ }) -> validate_program src rest
    | _ -> ()

(** Parse litmus to AST and convert from AST to IR *)

let parse_and_convert_litmus ~validate_ast src =
  Logs_safe.debug (fun m -> m "Parsing program...");

  try
    let litmus_ast = parse_litmus src in
      validate_program src litmus_ast;
      validate_ast litmus_ast;
      convert_litmus litmus_ast
  with
  | Failure msg ->
      (* Errors from [parse] already say they are parse errors. *)
      let msg =
        if String.starts_with ~prefix:"Parse error" msg then msg
        else "Parse error: " ^ msg
      in
        Logs_safe.err (fun m -> m "%s" msg);
        failwith msg
  | e ->
      Logs_safe.err (fun m -> m "Unexpected error: %s" (Printexc.to_string e));
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
            ctx.litmus_defacto <- Some config.defacto;
            ctx.litmus_constraints <- Some config.constraints;
            ctx.program_stmts <- Some program;
            ctx.assertions <-
              ( match assertions with
              | [] -> None
              | [ a ] -> (
                  match a with
                  | Ir.Outcome { model = Some model; _ } | Ir.Model { model } ->
                      apply_model_options ctx model;
                      Logs_safe.info (fun m ->
                          m "Applied model options for %s" model
                      );
                      Some a
                  | _ -> Some a
                )
              | _ -> failwith "Multiple assertions are not supported."
              );
            Lwt.return ctx
      | None ->
          Logs_safe.err (fun m -> m "No program provided for parsing.");
          Lwt.return ctx
