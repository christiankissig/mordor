(** Public interface for sMRD parser *)

open Ast
open Context
open Types

type ir_stmt = unit Ir.ir_stmt
type ir_assertion = unit Ir.ir_assertion
type ir_node = unit Ir.ir_node

(** Parse a complete litmus test from a string *)
val parse : string -> ast_litmus

(** Parse a single expression from a string *)
val parse_expr : string -> ast_expr

(** Parse a program (list of statements) from a string *)
val parse_program : string -> expr list * ir_node list * ir_assertion list

(** Convert parser AST expression to Types.expr *)
val ast_expr_to_expr : ast_expr -> Types.expr

(** Convert parser mode to Types.mode *)
val ast_mode_to_mode : mode -> Types.mode

(** Convert a list of parser expressions to Types.expr list *)
val convert_expr_list : ast_expr list -> Types.expr list

(** Pipeline step for parser *)
val step_parse_program : mordor_ctx Lwt.t -> mordor_ctx Lwt.t
