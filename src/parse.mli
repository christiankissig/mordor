(** Public interface for sMRD parser *)

open Ast
open Types

(** Parse a complete litmus test from a string *)
val parse : string -> ast_litmus

(** Parse a single expression from a string *)
val parse_expr : string -> ast_expr

(** Convert parser AST expression to Types.expr *)
val ast_expr_to_expr : ast_expr -> Types.expr

(** Convert parser mode to Types.mode *)
val ast_mode_to_mode : mode -> Types.mode

(** Convert a list of parser expressions to Types.expr list *)
val convert_expr_list : ast_expr list -> Types.expr list
