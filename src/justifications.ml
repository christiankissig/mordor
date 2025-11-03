open Types
open Expr

let to_string (just : justification) : string =
  Printf.sprintf "{%s}, {%s} |-({%s},{%s}) %s"
    (String.concat "," (List.map Expr.to_string just.p))
    (String.concat "," (Uset.values just.d))
    (String.concat ","
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (Uset.values just.fwd)
       )
    )
    (String.concat ","
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (Uset.values just.we)
       )
    )
    (Events.event_to_string just.w)
