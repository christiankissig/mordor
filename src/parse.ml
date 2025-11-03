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

(** Convert ast_expr to expr *)
let rec ast_expr_to_expr : ast_expr -> expr = function
  | EInt n -> ENum n
  | ERegister r -> EVar r
  | EGlobal g -> EVar g
  | EAtLoc l -> EVar l
  | EASet s -> EVar ("." ^ s)
  | EBinOp (l, op, r) -> EBinOp (ast_expr_to_expr l, op, ast_expr_to_expr r)
  | EUnOp (op, e) -> EUnOp (op, ast_expr_to_expr e)
  | ETuple (e1, e2) ->
      (* Represent tuple as a special binop *)
      EBinOp (ast_expr_to_expr e1, ",", ast_expr_to_expr e2)
  | ELoad { address; load } ->
      (* Represent load as a special unary operation *)
      EUnOp ("load", ast_expr_to_expr address)

(** Convert ast_mode to mode *)
let ast_mode_to_mode : mode -> mode = function
  | Nonatomic -> Nonatomic
  | Relaxed -> Relaxed
  | Release -> Release
  | Acquire -> Acquire
  | SC -> SC
  | Normal -> Normal
  | Strong -> Strong

(** Helper to convert expression lists *)
let convert_expr_list exprs = List.map ast_expr_to_expr exprs
