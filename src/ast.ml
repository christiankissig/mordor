open Types

(** AST types for sMRD parser *)

type assign_info = { mode : mode; volatile : bool }

type ast_expr =
  | EInt of Z.t
  | ERegister of string
  | EGlobal of string
  | EAtLoc of string
  | EASet of string
  | EBinOp of ast_expr * string * ast_expr
  | EUnOp of string * ast_expr
  | ETuple of ast_expr * ast_expr
  | ELoad of { address : ast_expr; load : assign_info }

type ast_stmt =
  | SThreads of { threads : ast_stmt list list }
  | SRegisterStore of { register : string; expr : ast_expr }
  | SGlobalStore of { global : string; expr : ast_expr; assign : assign_info }
  | SGlobalLoad of { register : string; global : string; load : assign_info }
  | SStore of { address : ast_expr; expr : ast_expr; assign : assign_info }
  | SCAS of {
      register : string;
      address : ast_expr;
      expected : ast_expr;
      desired : ast_expr;
      mode : mode;
    }
  | SFADD of {
      register : string;
      address : ast_expr;
      operand : ast_expr;
      mode : mode;
    }
  | SIf of {
      condition : ast_expr;
      then_body : ast_stmt list;
      else_body : ast_stmt list option;
    }
  | SWhile of { condition : ast_expr; body : ast_stmt list }
  | SDo of { body : ast_stmt list; condition : ast_expr }
  | SQDo of { body : ast_stmt list; condition : ast_expr }
  | SFence of { mode : mode }
  | SLock of { global : string option }
  | SUnlock of { global : string option }
  | SMalloc of {
      register : string;
      size : ast_expr;
      pc : int;
      label : string list;
    }
  | SFree of { register : string }
  | SLabeled of { label : string list; stmt : ast_stmt }
  | SSkip

type ast_config = {
  name : string;
  values : Z.t list;
  defacto : ast_expr list;
  constraint_ : ast_expr list;
}

type ast_thread = ast_stmt list

type ast_assertion =
  | AOutcome of {
      outcome : string;
      condition : ast_expr;
      model : string option;
    }
  | AModel of { model : string }
  | AChained of { model : string; outcome : string; rest : ast_litmus }

and ast_litmus = {
  config : ast_config option;
  program : ast_stmt list; (* List of parallel threads *)
  assertion : ast_assertion option;
}

let expr_to_string (expr : ast_expr) : string =
  match expr with
  | EInt _ -> "EInt"
  | ERegister _ -> "ERegister"
  | EGlobal _ -> "EGlobal"
  | EAtLoc _ -> "EAtLoc"
  | EASet _ -> "EASet"
  | EBinOp _ -> "EBinOp"
  | EUnOp _ -> "EUnOp"
  | ETuple _ -> "ETuple"
  | ELoad _ -> "ELoad"

let to_string (stmt : ast_stmt) : string =
  match stmt with
  | SThreads _ -> "SThreads"
  | SRegisterStore _ -> "SRegisterStore"
  | SGlobalStore _ -> "SGlobalStore"
  | SGlobalLoad _ -> "SGlobalLoad"
  | SStore _ -> "SStore"
  | SCAS _ -> "SCAS"
  | SFADD _ -> "SFADD"
  | SIf _ -> "SIf"
  | SWhile _ -> "SWhile"
  | SDo _ -> "SDo"
  | SQDo _ -> "SQDo"
  | SFence _ -> "SFence"
  | SLock _ -> "SLock"
  | SUnlock _ -> "SUnlock"
  | SMalloc _ -> "SMalloc"
  | SFree _ -> "SFree"
  | SLabeled _ -> "SLabeled"
  | SSkip -> "SSkip"
