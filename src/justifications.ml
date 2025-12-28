open Types
open Expr
open Uset
open Events

module Justification = struct
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

  let equal j1 j2 =
    j1.w = j2.w
    && USet.equal j1.fwd j2.fwd
    && USet.equal j1.we j2.we
    && USet.equal j1.d j2.d
    && List.equal Expr.equal j1.p j2.p
end
