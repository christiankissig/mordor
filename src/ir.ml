open Ast
open Expr
open Types

type ir_assertion_outcome = Allow | Forbid
type ir_assertion_check = { model : string; condition : ir_assertion_outcome }

type 'a ir_litmus = {
  name : string;
  program : 'a ir_node list;
  assertions : 'a ir_assertion list;
}

and 'a ir_stmt =
  | Threads of { threads : 'a ir_node list list }
  | RegisterStore of { register : string; expr : expr }
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
      mode : mode;
    }
  | Fadd of { register : string; address : expr; operand : expr; mode : mode }
  | Malloc of { register : string; size : expr }
  | Labeled of { label : string list; stmt : 'a ir_node }

(* annotated ir node wrapping ir statements with annotations *)
and 'a ir_node = { stmt : 'a ir_stmt; annotations : 'a }

and 'a ir_assertion =
  | Outcome of {
      outcome : ir_assertion_outcome;
      condition : expr;
      model : string option;
    }
  | Model of { model : string }
  | Chained of {
      model : string;
      outcome : ir_assertion_outcome;
      rest : 'a ir_litmus;
    }

let get_stmt node = node.stmt

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
