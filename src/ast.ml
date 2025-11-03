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
  | SFence of { mode : mode }
  | SLock of { global : string option }
  | SUnlock of { global : string option }
  | SMalloc of { register : string; size : ast_expr }
  | SFree of { register : string }
  | SLabeled of { label : string list; stmt : ast_stmt }

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

(** String representation functions for AST expressions *)
let rec expr_to_string (expr : ast_expr) : string =
  match expr with
  | EInt z -> Printf.sprintf "EInt %s" (Z.to_string z)
  | ERegister r -> Printf.sprintf "ERegister %s" r
  | EGlobal g -> Printf.sprintf "EGlobal %s" g
  | EAtLoc l -> Printf.sprintf "EAtLoc %s" l
  | EASet s -> Printf.sprintf "EASet %s" s
  | EBinOp (lhs, op, rhs) ->
      Printf.sprintf "EBinOp %s %s %s" (expr_to_string lhs) op
        (expr_to_string rhs)
  | EUnOp (op, rhs) -> Printf.sprintf "EUnOp %s %s" op (expr_to_string rhs)
  | ETuple (lhs, rhs) ->
      Printf.sprintf "ETuple %s , %s" (expr_to_string lhs) (expr_to_string rhs)
  | ELoad { address; load } -> (
      match load with
      | { mode; volatile } ->
          Printf.sprintf "ELoad %s with mode %s and volatile %b"
            (expr_to_string address)
            (Types.mode_to_string mode)
            volatile
    )

(** String representation functions for AST statements *)
let rec to_string (stmt : ast_stmt) : string =
  match stmt with
  | SThreads { threads } ->
      Printf.sprintf "SThreads %s"
        (String.concat " | "
           (List.map
              (fun thread ->
                "[" ^ String.concat ", " (List.map to_string thread) ^ "]"
              )
              threads
           )
        )
  | SRegisterStore { register; expr } ->
      Printf.sprintf "SRegisterStore %s := %s" register (expr_to_string expr)
  | SGlobalStore { global; expr; assign } ->
      Printf.sprintf "SGlobalStore %s := %s with mode %s and volatile %b" global
        (expr_to_string expr)
        (Types.mode_to_string assign.mode)
        assign.volatile
  | SGlobalLoad { register; global; load } ->
      Printf.sprintf "SGlobalLoad %s := load %s with mode %s and volatile %b"
        register global
        (Types.mode_to_string load.mode)
        load.volatile
  | SStore { address; expr; assign } ->
      Printf.sprintf "SStore *%s := %s with mode %s and volatile %b"
        (expr_to_string address) (expr_to_string expr)
        (Types.mode_to_string assign.mode)
        assign.volatile
  | SCAS { register; address; expected; desired; mode } ->
      Printf.sprintf "SCAS %s, %s, %s, %s with mode %s" register
        (expr_to_string address) (expr_to_string expected)
        (expr_to_string desired)
        (Types.mode_to_string mode)
  | SFADD { register; address; operand; mode } ->
      Printf.sprintf "SFADD %s, %s, %s with mode %s" register
        (expr_to_string address) (expr_to_string operand)
        (Types.mode_to_string mode)
  | SIf { condition; then_body; else_body } -> (
      "SIf "
      ^ expr_to_string condition
      ^ " then: "
      ^ String.concat ", " (List.map to_string then_body)
      ^
      match else_body with
      | Some else_stmts ->
          " else: " ^ String.concat ", " (List.map to_string else_stmts)
      | None -> ""
    )
  | SWhile { condition; body } ->
      Printf.sprintf "SWhile %s do %s" (expr_to_string condition)
        (String.concat "; " (List.map to_string body))
  | SDo { body; condition } ->
      Printf.sprintf "SDo do %s while %s"
        (String.concat "; " (List.map to_string body))
        (expr_to_string condition)
  | SFence { mode } ->
      Printf.sprintf "SFence with mode %s" (Types.mode_to_string mode)
  | SLock { global } ->
      Printf.sprintf "SLock with global %s"
        ( match global with
        | Some g -> g
        | None -> "none"
        )
  | SUnlock { global } ->
      Printf.sprintf "SUnlock with global %s"
        ( match global with
        | Some g -> g
        | None -> "none"
        )
  | SMalloc { register; size } ->
      Printf.sprintf "SMalloc %s := malloc %s" register (expr_to_string size)
  | SFree { register } -> Printf.sprintf "SFree %s" register
  | SLabeled { label; stmt } ->
      Printf.sprintf "SLabeled [%s]: %s" (String.concat "; " label)
        (to_string stmt)

(** String representation for entire litmus test *)
let ast_litmus_to_string (litmus : ast_litmus) : string =
  let program_str = String.concat "\n" (List.map to_string litmus.program) in
  let assertion_str =
    match litmus.assertion with
    | Some _ -> "With assertion"
    | None -> "No assertion"
  in
    "Program:\n" ^ program_str ^ "\n" ^ assertion_str ^ "\n"
