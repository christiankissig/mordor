(** The browser's {!Smt_backend}, until W4 (#180) brings a solver. A solver can
    be made, so that [Solver]'s per-domain one can be, but asking it anything
    fails, and says why. *)

type solver = unit

let no_solver () =
  failwith
    "This build of MoRDor has no SMT solver yet (W4, #180). It parses any \
     program, and interprets those whose conditions are decided without one."

let create () = ()
let push () = ()
let pop () = ()
let add () _ = no_solver ()
let check () = no_solver ()
let model () = no_solver ()
let statistics () = "no SMT solver"
