open Types
open Expr
open Uset
open Events

let to_string (just : justification) : string =
  Printf.sprintf "{%s}, {%s} |-({%s},{%s}) %s"
    (String.concat "," (List.map Expr.to_string just.p))
    (String.concat "," (USet.values just.d))
    (String.concat ","
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values just.fwd)
       )
    )
    (String.concat ","
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values just.we)
       )
    )
    (Event.to_string just.w)
