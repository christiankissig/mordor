open Types

(* The thread context tracks the IDs of thread blocks in the AST. For example,
   in the following code:

   threads {
     // Thread 0
     ...
     threads {
       // Thread 0.0
       ...
     }
     // Thread 0.1
     ...
   }

   The thread context for statements in the outer thread block would be
   { tid = 0; path = [0] }, while the thread context for statements in the
   inner thread block would be { tid = 0; path = [0; 0] } for Thread 0.0 and
   { tid = 1; path = [0; 1] } for Thread 0.1.
*)
type thread_ctx = { tid : int; path : int list }

(* The source context tracks the program counter (PC) of statements in the AST.
   *)
type src_ctx = { pc : int }

(* The loop context tracks the loop ID and the iteration counts of loops
   surrounding a statement in the AST. For example, in the following code:

   while (cond1) {
     // Loop 0, iteration i1
     ...
     while (cond2) {
       // Loop 1, iteration i2
       ...
     }
   }

   The loop context for statements in the outer loop would be
   { lid = 0; loops = [i1] }, while the loop context for statements in the
   inner loop would be { lid = 1; loops = [i1; i2] }.
   *)
type loop_ctx = { lid : int; loops : int list }

(* Information about memory assignments (loads/stores) : memory mode and volatile
   flag *)
type assign_info = { mode : mode; volatile : bool }

(* AST for expressions and statements *)
type ast_expr =
  | EInt of Z.t
  | ERegister of string
  | EGlobal of string
  | EAtLoc of string
  | EASet of string
  | EBinOp of ast_expr * string * ast_expr
  | EUnOp of string * ast_expr
  | ETuple of ast_expr * ast_expr

(* AST for statements and nodes *)
type ast_stmt =
  | SThreads of { threads : ast_node list list }
  | SRegisterStore of { register : string; expr : ast_expr }
  | SRegisterRefAssign of { register : string; global : string }
  | SGlobalStore of { global : string; expr : ast_expr; assign : assign_info }
  | SGlobalLoad of { register : string; global : string; load : assign_info }
  | SLoad of { register : string; address : ast_expr; load : assign_info }
  | SStore of { address : ast_expr; expr : ast_expr; assign : assign_info }
  | SCAS of {
      register : string;
      address : ast_expr;
      expected : ast_expr;
      desired : ast_expr;
      load_mode : mode;
      assign_mode : mode;
    }
  | SFADD of {
      register : string;
      address : ast_expr;
      operand : ast_expr;
      rmw_mode : string;
      load_mode : mode;
      assign_mode : mode;
    }
  | SIf of {
      condition : ast_expr;
      then_body : ast_node list;
      else_body : ast_node list option;
    }
  | SWhile of { condition : ast_expr; body : ast_node list }
  | SDo of { body : ast_node list; condition : ast_expr }
  | SFence of { mode : mode }
  | SLock of { global : string option }
  | SUnlock of { global : string option }
  | SRegMalloc of { register : string; size : ast_expr }
  | SGlobalMalloc of { global : string; size : ast_expr }
  | SFree of { register : string }
  | SLabeled of { label : string list; stmt : ast_stmt }
  | SSkip

and ast_node = {
  stmt : ast_stmt;
  thread_ctx : thread_ctx option;
  src_ctx : src_ctx option;
  loop_ctx : loop_ctx option;
}

(* Threads are lists of nodes wrapping statements *)
type ast_thread = ast_node list

(** Accessor functions for AST nodes *)
let get_ast_stmt (node : ast_node) : ast_stmt = node.stmt

let make_ast_node ?(thread_ctx = None) ?(src_ctx = None) ?(loop_ctx = None) stmt
    =
  { stmt; thread_ctx; src_ctx; loop_ctx }

(* AST for litmust test config *)
type ast_config = {
  name : string option;
  model : string option;
  values : Z.t list;
  defacto : ast_expr list;
  constraints : ast_expr list;
}

(* AST for litmus test assertions and litmus tests *)
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
  program : ast_node list; (* List of parallel threads *)
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

(** String representation functions for AST statements *)

let rec stmt_to_string stmt =
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
  | SRegisterRefAssign { register; global } ->
      Printf.sprintf "SRegisterRefAssign %s := &%s" register global
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
  | SLoad { register; address; load } ->
      Printf.sprintf "SLoad %s from address %s with mode %s and volatile %b"
        register (expr_to_string address)
        (Types.mode_to_string load.mode)
        load.volatile
  | SStore { address; expr; assign } ->
      Printf.sprintf "SStore *%s := %s with mode %s and volatile %b"
        (expr_to_string address) (expr_to_string expr)
        (Types.mode_to_string assign.mode)
        assign.volatile
  | SCAS { register; address; expected; desired; load_mode; assign_mode } ->
      Printf.sprintf "SCAS %s, %s, %s, %s with load mode %s and assign mode %s"
        register (expr_to_string address) (expr_to_string expected)
        (expr_to_string desired)
        (Types.mode_to_string load_mode)
        (Types.mode_to_string assign_mode)
  | SFADD { register; address; operand; rmw_mode; load_mode; assign_mode } ->
      Printf.sprintf
        "SFADD %s, %s, %s with rmw_mode %s and load mode %s and assign mode %s"
        register (expr_to_string address) (expr_to_string operand) rmw_mode
        (Types.mode_to_string load_mode)
        (Types.mode_to_string assign_mode)
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
  | SRegMalloc { register; size } ->
      Printf.sprintf "SRegMalloc %s := malloc %s" register (expr_to_string size)
  | SGlobalMalloc { global; size } ->
      Printf.sprintf "SGlobalMalloc %s := malloc %s" global (expr_to_string size)
  | SFree { register } -> Printf.sprintf "SFree %s" register
  | SLabeled { label; stmt } ->
      Printf.sprintf "SLabeled [%s]: %s" (String.concat "; " label)
        (stmt_to_string stmt)
  | SSkip -> "SSkip"

and to_string (node : ast_node) : string =
  let stmt = node.stmt in
    stmt_to_string stmt

(** String representation for entire litmus test *)
let ast_litmus_to_string (litmus : ast_litmus) : string =
  let program_str = String.concat "\n" (List.map to_string litmus.program) in
  let assertion_str =
    match litmus.assertion with
    | Some _ -> "With assertion"
    | None -> "No assertion"
  in
    "Program:\n" ^ program_str ^ "\n" ^ assertion_str ^ "\n"
