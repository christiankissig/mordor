(** The native {!Smt_backend}: Z3, through {!Z3_translate}, with W1's query dump
    ({!Smt_dump}). *)

open Types
open Z3_translate

type solver = context

let create = create_context

let push solver =
  Smt_dump.call "push";
  Z3.Solver.push solver.solver

let pop solver = Z3.Solver.pop solver.solver 1

let add solver exprs =
  let z3_exprs = List.map (expr_to_z3 solver) exprs in
    Z3.Solver.add solver.solver z3_exprs

let check solver =
  let started = if Smt_dump.enabled then Unix.gettimeofday () else 0. in
  let status = Z3.Solver.check solver.solver [] in
    if Smt_dump.enabled then
      Smt_dump.query solver.ctx solver.solver status
        (Unix.gettimeofday () -. started);
    match status with
    | Z3.Solver.SATISFIABLE -> Some true
    | Z3.Solver.UNSATISFIABLE -> Some false
    | Z3.Solver.UNKNOWN -> None

let model solver =
  Smt_dump.call "model";
  match Z3.Solver.get_model solver.solver with
  | Some m ->
      let bindings = Hashtbl.create 16 in
        Hashtbl.iter
          (fun name var ->
            match Z3.Model.eval m var true with
            | Some value -> (
                let str = Z3.Expr.to_string value in
                  try
                    let n = Z.of_string str in
                      Hashtbl.add bindings name (VNumber n)
                  with _ -> Hashtbl.add bindings name (VVar str)
              )
            | None -> ()
          )
          solver.vars;
        Some bindings
  | None -> None

let statistics solver =
  Z3.Statistics.to_string (Z3.Solver.get_statistics solver.solver)
