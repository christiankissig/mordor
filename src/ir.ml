open Ast
open Expr
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

let rec to_string (stmt : ir_stmt) : string =
  match stmt with
  | Threads { threads } ->
      let thread_strs =
        List.map
          (fun t ->
            Printf.sprintf "[%s]" (String.concat "; " (List.map to_string t))
          )
          threads
      in
        Printf.sprintf "Threads [%s]" (String.concat "; " thread_strs)
  | RegisterStore { register; expr } ->
      Printf.sprintf "Reg Store %s := %s" register (Expr.to_string expr)
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
        Printf.sprintf "Do { %s } While (%s)" body_str (Expr.to_string condition)
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
  | Cas { register; address; expected; desired; mode } ->
      Printf.sprintf "%s := CAS(%s, %s, %s) with mode %s" register
        (Expr.to_string address) (Expr.to_string expected)
        (Expr.to_string desired)
        (Types.mode_to_string mode)
  | Fadd { register; address; operand; mode } ->
      Printf.sprintf "%s := FADD(%s, %s) with mode %s" register
        (Expr.to_string address) (Expr.to_string operand)
        (Types.mode_to_string mode)
  | Malloc { register; size } ->
      Printf.sprintf "%s := MALLOC(%s)" register (Expr.to_string size)
  | Labeled { label; stmt } ->
      Printf.sprintf "Labeled [%s]: %s" (String.concat "; " label)
        (to_string stmt)
