open Ast
open Types

type ir_stmt =
  | Threads of { threads : ir_stmt list list }
  | RegisterStore of { register : string; expr : expr }
  | GlobalStore of { global : string; expr : expr; assign : assign_info }
  | GlobalLoad of { register : string; global : string; load : assign_info }
  | DerefStore of { address : expr; expr : expr; assign : assign_info }
  | If of {
      condition : expr;
      then_body : ir_stmt list;
      else_body : ir_stmt list option;
    }
  | While of { condition : expr; body : ir_stmt list }
  | Do of { body : ir_stmt list; condition : expr }
  | Fence of { mode : mode }
  | Lock of { global : string option }
  | Unlock of { global : string option }
  | Free of { register : string }
  | Cas of {
      register : string;
      address : expr;
      expected : expr;
      desired : expr;
      mode : mode;
    }
  | Fadd of { register : string; address : expr; operand : expr; mode : mode }
  | Malloc of { register : string; size : expr }
  | Labeled of { label : string list; stmt : ir_stmt }
