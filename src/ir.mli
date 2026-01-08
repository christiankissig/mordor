open Ast
open Types

type ir_assertion_outcome = Allow | Forbid
type ir_assertion_check = { model : string; condition : ir_assertion_outcome }

(* Assertion condition can be either a regular expression or the special UB marker *)
type assertion_condition = CondExpr of expr | CondUB

type 'a ir_litmus = {
  config : ir_config;
  program : 'a ir_node list;
  assertions : 'a ir_assertion list;
}

and ir_config = {
  name : string option;
  model : string option;
  values : Z.t list;
  defacto : expr list;
  constraints : expr list;
}

and 'a ir_stmt =
  | Threads of { threads : 'a ir_node list list }
  | RegisterStore of { register : string; expr : expr }
  | RegisterRefAssign of { register : string; global : string }
  | GlobalStore of { global : string; expr : expr; assign : assign_info }
  | GlobalLoad of { register : string; global : string; load : assign_info }
  | DerefStore of { address : expr; expr : expr; assign : assign_info }
  | DerefLoad of { register : string; address : expr; load : assign_info }
  | If of {
      condition : expr;
      then_body : 'a ir_node list;
      else_body : 'a ir_node list option;
    }
  | While of { condition : expr; body : 'a ir_node list }
  | Do of { body : 'a ir_node list; condition : expr }
  | Fence of { mode : mode }
  | Lock of { global : string option }
  | Unlock of { global : string option }
  | Free of { register : string }
  | Cas of {
      register : string;
      address : expr;
      expected : expr;
      desired : expr;
      load_mode : mode;
      assign_mode : mode;
    }
  | Fadd of {
      register : string;
      address : expr;
      operand : expr;
      rmw_mode : string;
      load_mode : mode;
      assign_mode : mode;
    }
  | RegMalloc of { register : string; size : expr }
  | GlobalMalloc of { global : string; size : expr }
  | Labeled of { label : string list; stmt : 'a ir_node }
  | Skip

(* annotated ir node wrapping ir statements with annotations *)
and 'a ir_node = { stmt : 'a ir_stmt; annotations : 'a }

and 'a ir_assertion =
  | Outcome of {
      outcome : ir_assertion_outcome;
      condition : assertion_condition;
      model : string option;
    }
  | Model of { model : string }
  | Chained of {
      model : string;
      outcome : ir_assertion_outcome;
      rest : 'a ir_litmus;
    }

val get_stmt : 'a ir_node -> 'a ir_stmt

val extract_conditions_from_stmt : 'a ir_stmt -> expr list

val to_string : ann_to_string:('a -> string) -> 'a ir_node -> string

