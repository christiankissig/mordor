(** Parser for sMRD litmus tests using Menhir and ocamllex *)

(** This module provides parsing for sMRD litmus tests.

    It defines AST types for the parsing phase, and provides conversion
    functions to convert to Types module representations when needed.

    Usage: let litmus = Parse.parse source_string let expr = Parse.parse_expr
    "r1 + 42" *)

open Ast
open Types

(** Parse a litmus test from a string *)
let parse src =
  let lexbuf = Lexing.from_string src in
    try Parser.litmus Lexer.token lexbuf with
    | Lexer.Lexer_error msg -> failwith (Printf.sprintf "Lexer error: %s" msg)
    | Parser.Error ->
        let pos = lexbuf.Lexing.lex_curr_p in
          failwith
            (Printf.sprintf "Parse error at line %d, column %d"
               pos.Lexing.pos_lnum
               (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
            )

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
  | EMalloc e -> Types.EUnOp ("malloc", Types.VExpression (ast_expr_to_expr e))
  | EBinOp (l, op, r) ->
      Types.EBinOp
        ( Types.VExpression (ast_expr_to_expr l),
          op,
          Types.VExpression (ast_expr_to_expr r)
        )
  | EUnOp (op, e) -> Types.EUnOp (op, Types.VExpression (ast_expr_to_expr e))
  | ETuple (e1, e2) ->
      (* Represent tuple as a special binop *)
      Types.EBinOp
        ( Types.VExpression (ast_expr_to_expr e1),
          ",",
          Types.VExpression (ast_expr_to_expr e2)
        )
  | ELoad { address; load } ->
      (* Represent load as a special unary operation *)
      Types.EUnOp ("load", Types.VExpression (ast_expr_to_expr address))

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
