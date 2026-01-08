open Expr
open Types

(** {1 Types for IR Syntax Trees} *)

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
  | GlobalStore of { global : string; expr : expr; assign : Ast.assign_info }
  | GlobalLoad of { register : string; global : string; load : Ast.assign_info }
  | DerefStore of { address : expr; expr : expr; assign : Ast.assign_info }
  | DerefLoad of { register : string; address : expr; load : Ast.assign_info }
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

(** {1 Accessor Functions} *)

let get_stmt node = node.stmt

(** {1 Utility Functions} *)

let extract_written_registers_from_stmt (stmt : 'a ir_stmt) : string list =
  match stmt with
  | RegisterStore { register; _ } -> [ register ]
  | GlobalLoad { register; _ } -> [ register ]
  | DerefLoad { register; _ } -> [ register ]
  | Cas { register; _ } -> [ register ]
  | Fadd { register; _ } -> [ register ]
  | RegMalloc { register; _ } -> [ register ]
  | _ -> []

let extract_read_registers_from_stmt (stmt : 'a ir_stmt) : string list =
  match stmt with
  | RegisterStore { expr; _ } -> Expr.extract_registers expr
  | GlobalStore { expr; _ } -> Expr.extract_registers expr
  | DerefStore { address; expr; _ } ->
      Expr.extract_registers address @ Expr.extract_registers expr
  | If { condition; _ } -> Expr.extract_registers condition
  | While { condition; _ } -> Expr.extract_registers condition
  | Do { condition; _ } -> Expr.extract_registers condition
  | Cas { address; expected; desired; _ } ->
      Expr.extract_registers address
      @ Expr.extract_registers expected
      @ Expr.extract_registers desired
  | Fadd { address; operand; _ } ->
      Expr.extract_registers address @ Expr.extract_registers operand
  | RegMalloc { size; _ } -> Expr.extract_registers size
  | GlobalMalloc { size; _ } -> Expr.extract_registers size
  | _ -> []

(** Extract conditions from IR statements *)
let rec extract_conditions_from_stmt (stmt : 'a ir_stmt) : expr list =
  match stmt with
  | If { condition; then_body; else_body; _ } ->
      let nested_then =
        List.concat_map (fun n -> extract_conditions_from_stmt n.stmt) then_body
      in
      let nested_else =
        match else_body with
        | Some body ->
            List.concat_map (fun n -> extract_conditions_from_stmt n.stmt) body
        | None -> []
      in
        condition :: (nested_then @ nested_else)
  | While { condition; body } ->
      let nested =
        List.concat_map (fun n -> extract_conditions_from_stmt n.stmt) body
      in
        condition :: nested
  | Do { body; condition } ->
      let nested =
        List.concat_map (fun n -> extract_conditions_from_stmt n.stmt) body
      in
        condition :: nested
  | Threads { threads } ->
      List.concat_map
        (fun thread ->
          List.concat_map (fun n -> extract_conditions_from_stmt n.stmt) thread
        )
        threads
  | Labeled { stmt; _ } -> extract_conditions_from_stmt stmt.stmt
  | _ -> []

(** {1 Pretty-printing IR} *)

let rec to_string ~ann_to_string (node : 'a ir_node) : string =
  let to_string = to_string ~ann_to_string in
  let stmt = get_stmt node in
    match stmt with
    | Threads { threads } ->
        let thread_strs =
          List.map
            (fun thread ->
              Printf.sprintf "[%s]"
                (String.concat "; " (List.map to_string thread))
            )
            threads
        in
          Printf.sprintf "Threads [%s]" (String.concat "; " thread_strs)
    | RegisterStore { register; expr } ->
        Printf.sprintf "Reg Store %s := %s" register (Expr.to_string expr)
    | RegisterRefAssign { register; global } ->
        Printf.sprintf "Reg Ref Assign %s := &%s" register global
    | GlobalStore { global; expr; assign } ->
        Printf.sprintf "Store %s := %s with mode %s" global (Expr.to_string expr)
          (Types.mode_to_string assign.mode)
    | GlobalLoad { register; global; load } ->
        Printf.sprintf "%s := Load %s with mode %s" register global
          (Types.mode_to_string load.mode)
    | DerefStore { address; expr; assign } ->
        Printf.sprintf "Store *%s := %s with mode %s" (Expr.to_string address)
          (Expr.to_string expr)
          (Types.mode_to_string assign.mode)
    | DerefLoad { register; address; load } ->
        Printf.sprintf "%s := Load *%s with mode %s" register
          (Expr.to_string address)
          (Types.mode_to_string load.mode)
    | If { condition; then_body; else_body } ->
        let then_str = String.concat "; " (List.map to_string then_body) in
        let else_str =
          match else_body with
          | Some body ->
              Printf.sprintf " else { %s }"
                (String.concat "; " (List.map to_string body))
          | None -> ""
        in
          Printf.sprintf "If (%s) { %s }%s" (Expr.to_string condition) then_str
            else_str
    | While { condition; body } ->
        let body_str = String.concat "; " (List.map to_string body) in
          Printf.sprintf "While (%s) { %s }" (Expr.to_string condition) body_str
    | Do { body; condition } ->
        let body_str = String.concat "; " (List.map to_string body) in
          Printf.sprintf "Do { %s } While (%s)" body_str
            (Expr.to_string condition)
    | Fence { mode } -> Printf.sprintf "Fence(%s)" (Types.mode_to_string mode)
    | Lock { global } -> (
        match global with
        | Some g -> Printf.sprintf "Lock(%s)" g
        | None -> "Lock"
      )
    | Unlock { global } -> (
        match global with
        | Some g -> Printf.sprintf "Unlock(%s)" g
        | None -> "Unlock"
      )
    | Free { register } -> Printf.sprintf "Free(%s)" register
    | Cas { register; address; expected; desired; load_mode; assign_mode } ->
        Printf.sprintf
          "%s := CAS(%s, %s, %s) with load mode %s and assign mode\n        %s"
          register (Expr.to_string address) (Expr.to_string expected)
          (Expr.to_string desired)
          (Types.mode_to_string load_mode)
          (Types.mode_to_string assign_mode)
    | Fadd { register; address; operand; rmw_mode; load_mode; assign_mode } ->
        Printf.sprintf
          "%s := FADD(%s, %s) with rmw mode %s and load mode %s and assign \
           mode %s"
          register (Expr.to_string address) (Expr.to_string operand) rmw_mode
          (Types.mode_to_string load_mode)
          (Types.mode_to_string assign_mode)
    | RegMalloc { register; size } ->
        Printf.sprintf "%s := MALLOC(%s)" register (Expr.to_string size)
    | GlobalMalloc { global; size } ->
        Printf.sprintf "%s := MALLOC(%s)" global (Expr.to_string size)
    | Labeled { label; stmt } ->
        Printf.sprintf "Labeled [%s]: %s" (String.concat "; " label)
          (to_string stmt)
    | Skip -> "Skip"
