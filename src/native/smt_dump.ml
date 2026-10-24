(** W1 (#175): with [MORDOR_SMT_DUMP] set to a directory, every query that
    reaches Z3 is written there in SMT-LIB 2, so that other solvers can be
    measured on the queries MoRDor actually asks. A query is its solver's
    assertions, across every pushed scope, as asserted, printed as a standalone
    benchmark with their declarations and [(check-sat)]: one file per distinct
    query, named by its digest. Not [Z3.Solver.to_string], which on a solver
    checked before prints its preprocessed assertions and the model converter's
    state ([model-add], [model-del]), which is not SMT-LIB. [index.tsv] has a
    line per query asked -- digest, caller, Z3's answer and seconds -- and
    [calls.tsv], written at exit, counts the scope pushes and model reads by
    caller. A model read counts whether or not Z3 was asked: [Solver.solve]
    reads one off a query [Solver.trivially] answered too. *)

let dir = Sys.getenv_opt "MORDOR_SMT_DUMP"
let enabled = Option.is_some dir
let mutex = Mutex.create ()
let calls = Hashtbl.create 16

let index =
  Option.map
    (fun dir ->
      if not (Sys.file_exists dir) then Sys.mkdir dir 0o755;
      let oc =
        open_out_gen
          [ Open_append; Open_creat; Open_text ]
          0o644
          (Filename.concat dir "index.tsv")
      in
        at_exit (fun () ->
            close_out oc;
            Out_channel.with_open_gen [ Open_append; Open_creat; Open_text ]
              0o644 (Filename.concat dir "calls.tsv") (fun oc ->
                Hashtbl.iter
                  (fun (what, site) n ->
                    Printf.fprintf oc "%s\t%s\t%d\n" what site n
                  )
                  calls
            )
        );
        (* A run cut short by [timeout] still writes what it asked. *)
        Sys.set_signal Sys.sigterm (Sys.Signal_handle (fun _ -> exit 143));
        oc
    )
    dir

(** Counts a scope push or a model evaluation, by its caller. *)
let call what =
  if enabled then
    let key = (what, Call_site.caller ()) in
      Mutex.protect mutex (fun () ->
          Hashtbl.replace calls key
            (1 + Option.value ~default:0 (Hashtbl.find_opt calls key))
      )

let query ctx solver status seconds =
  Option.iter
    (fun dir ->
      let text =
        Z3.SMT.benchmark_to_smtstring ctx "mordor" "" "unknown" ""
          (Z3.Solver.get_assertions solver)
          (Z3.Boolean.mk_true ctx)
      in
      let digest = Digest.to_hex (Digest.string text) in
      let answer =
        match status with
        | Z3.Solver.SATISFIABLE -> "sat"
        | Z3.Solver.UNSATISFIABLE -> "unsat"
        | Z3.Solver.UNKNOWN -> "unknown"
      in
      let site = Call_site.caller () in
        Mutex.protect mutex (fun () ->
            let path = Filename.concat dir (digest ^ ".smt2") in
              if not (Sys.file_exists path) then
                Out_channel.with_open_text path (fun oc -> output_string oc text);
              Option.iter
                (fun oc ->
                  Printf.fprintf oc "%s\t%s\t%s\t%.6f\n%!" digest site answer
                    seconds
                )
                index
        )
    )
    dir
