open Types
open Uset

let exec_to_string (exec : symbolic_execution) : string =
  Printf.sprintf "{\n\tex_e=%s,\n\trf=%s\n\tdp=%s\n\tppo=%s\n}"
    (String.concat ", " (List.map (Printf.sprintf "%d") (USet.values exec.ex_e)))
    (String.concat ", "
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values exec.rf)
       )
    )
    (String.concat ", "
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values exec.dp)
       )
    )
    (String.concat ", "
       (List.map
          (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
          (USet.values exec.ppo)
       )
    )
