(** Public interface for sMRD parser *)

open Ast
open Context

(** Parse a complete litmus test from a string *)
val parse_litmus : string -> ast_litmus

(** Parse a single expression from a string *)
val parse_expr : string -> ast_expr

(** Parse a litmus test from a string, check it, and convert it to IR.

    Besides [validate_ast], every program in the test, chained ones included, is
    checked to use only registers and constants in its expressions: a global in
    an expression, [@x], address-of outside [r := &x], and [free] of a global
    fail with ["Parse error at line L, column C: ..."]. *)
val parse_and_convert_litmus :
  validate_ast:(ast_litmus -> unit) -> string -> ir_litmus

(** Convert parser AST expression to Types.expr *)
val ast_expr_to_expr : ast_expr -> Types.expr

(** Convert a list of parser expressions to Types.expr list *)
val convert_expr_list : ast_expr list -> Types.expr list

(** Pipeline step for parser *)
val step_parse_litmus : mordor_ctx Lwt.t -> mordor_ctx Lwt.t

(** Validate that there are no thread spawns inside loops *)
val validate_no_threads_under_loop : ast_node list -> bool
