(** V1 (#97) — equivalence harness for the bounded pipeline.

    Every bounded path of phase 2 builds different intermediate objects from the
    enumeration it replaces -- one witness per future instead of every execution
    (R13, [futures_by_witness]), one execution per question instead of all of
    them (R16, [by_query]) -- and none of them may change what MoRDor reports.
    This runs each program under the baseline, the enumeration, and under each
    bounded path, and diffs what is reported:

    - futures: the future set of the witness path against the enumeration's, as
      sets of [dp ∪ ppo ∪ id] projections;
    - assertions: the verdict asked by query against the enumeration's -- valid,
      and undefined behaviour where the query asks about it -- and the witness
      the query reports, which must be one of the enumeration's executions;
    - executions: every execution a bounded path returns must be one the
      enumeration returns.

    Executions are compared in {!Canonicalize}'s canonical form, first without
    predicates. Two with the same relations whose predicates differ as text are
    asked of the solver -- does each list entail the other -- and the match is
    counted as syntactic, semantic or divergent (risk R2 of S9): a divergent
    pair is a difference.

    With [--flags-off] the bounded runs are replaced by a second baseline run,
    and the harness must find nothing: that is the check that it is sound
    itself, the quotient of execution sets being the identity.

    Usage: equivalence [--flags-off] [--timeout SECS] [DIR|FILE ...]

    Each program runs in a child process, killed after [--timeout] seconds
    (default 300) and reported as timed out rather than compared. Exits non-zero
    on any difference or error. *)

open Types

let default_dirs = [ "litmus-tests"; "litmus-tests-jmm"; "programs" ]

let rec lit_files path =
  if not (Sys.file_exists path) then []
  else if not (Sys.is_directory path) then
    if Filename.check_suffix path ".lit" then [ path ] else []
  else
    Sys.readdir path
    |> Array.to_list
    |> List.sort compare
    |> List.concat_map (fun name -> lit_files (Filename.concat path name))

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
    close_in ic;
    s

(** {1 One run} *)

type run = {
  structure : symbolic_event_structure;
  executions : symbolic_execution list;
  futures : (int * int) list list;
  valid : bool option;
  ub : bool option;
  report : Context.query_report option;
}

let run ~witnesses ~by_query program =
  let options =
    {
      Context.default_options with
      dependencies = true;
      allow_unknown_model = true;
      futures_by_witness = witnesses;
      by_query;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "equivalence";
    ctx.litmus <- Some program;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx
        |> Parse.step_parse_litmus
        |> Interpret.step_interpret
        |> Semantics.step_calculate_executions
        |> Assertion.step_check_assertions
        )
    in
    let structure = Option.get ctx.structure in
    let executions =
      Option.fold ~none:[] ~some:Uset.USet.values ctx.executions
    in
    let futures =
      Futures.calculate_future_set (Uset.USet.of_list executions)
      |> Uset.USet.values
      |> List.map (fun f -> Uset.USet.values f |> List.sort compare)
      |> List.sort_uniq compare
    in
      {
        structure;
        executions;
        futures;
        valid = ctx.valid;
        ub = ctx.undefined_behaviour;
        report = ctx.query_report;
      }

(** {1 Matching executions} *)

type matched = Syntactic | Semantic | Divergent

(* Every model of [ps] satisfies [qs]. *)
let entails ps qs =
  List.for_all
    (fun q ->
      List.exists (Expr.Expr.equal q) ps
      || not (Solver.is_sat (Expr.Expr.inverse q :: ps))
    )
    qs

let relations (c : Canonicalize.t) =
  Canonicalize.signature { c with predicates = [] }

(** [index run] is [run]'s executions by their canonical relations, each with
    its predicates as text and as expressions. *)
let index (r : run) =
  let tbl = Hashtbl.create 64 in
    List.iter
      (fun (x : symbolic_execution) ->
        let c = Canonicalize.canonicalize r.structure x in
        let k = relations c in
          Hashtbl.replace tbl k
            ((c.predicates, x.ex_p)
            :: (Hashtbl.find_opt tbl k |> Option.value ~default:[])
            )
      )
      r.executions;
    tbl

(** [find tbl r x] is how execution [x] of run [r] matches one in [tbl]. *)
let find tbl (r : run) (x : symbolic_execution) =
  let c = Canonicalize.canonicalize r.structure x in
    match Hashtbl.find_opt tbl (relations c) with
    | None -> Divergent
    | Some candidates ->
        if List.exists (fun (text, _) -> text = c.predicates) candidates then
          Syntactic
        else if
          List.exists
            (fun (_, ps) -> entails ps x.ex_p && entails x.ex_p ps)
            candidates
        then Semantic
        else Divergent

(** {1 One program} *)

type result = {
  differences : string list;
  syntactic : int;
  semantic : int;
  divergent : int;
  asked : bool;  (** The query answered the assertion. *)
}

let compare_program ~flags_off program =
  let differences = ref [] in
  let differ fmt =
    Printf.ksprintf (fun s -> differences := s :: !differences) fmt
  in
  let syntactic = ref 0 and semantic = ref 0 and divergent = ref 0 in
  let count = function
    | Syntactic -> incr syntactic
    | Semantic -> incr semantic
    | Divergent -> incr divergent
  in
  (* Every execution of [bounded] is one of [baseline]'s. *)
  let contained what baseline (bounded : run) =
    let tbl = index baseline in
      List.iter
        (fun x ->
          let m = find tbl bounded x in
            count m;
            if m = Divergent then
              differ "%s: execution %d is not one the enumeration returns" what
                x.id
        )
        bounded.executions
  in
  let show = function
    | Some b -> string_of_bool b
    | None -> "none"
  in
  let baseline = run ~witnesses:false ~by_query:false program in
  let asked = ref false in
    if flags_off then begin
      let again = run ~witnesses:false ~by_query:false program in
        if baseline.futures <> again.futures then differ "futures";
        if baseline.valid <> again.valid || baseline.ub <> again.ub then
          differ "verdict: %s/%s then %s/%s" (show baseline.valid)
            (show baseline.ub) (show again.valid) (show again.ub);
        if List.length baseline.executions <> List.length again.executions then
          differ "executions: %d then %d"
            (List.length baseline.executions)
            (List.length again.executions);
        contained "executions" baseline again;
        contained "executions (reverse)" again baseline
    end
    else begin
      let witness = run ~witnesses:true ~by_query:false program in
        if baseline.futures <> witness.futures then
          differ "futures: %d by enumeration, %d from witnesses"
            (List.length baseline.futures)
            (List.length witness.futures);
        contained "futures' witness" baseline witness;
        let query = run ~witnesses:false ~by_query:true program in
          match query.report with
          | None -> ()
          | Some _ ->
              asked := true;
              let same a b = a = None || b = None || a = b in
                if query.valid = None && query.ub = None then
                  differ "query undecided"
                else if
                  not
                    (same baseline.valid query.valid
                    && same baseline.ub query.ub
                    )
                then
                  differ "verdict: %s/%s by enumeration, %s/%s by query"
                    (show baseline.valid) (show baseline.ub) (show query.valid)
                    (show query.ub);
                contained "query's witness" baseline query
    end;
    {
      differences = List.rev !differences;
      syntactic = !syntactic;
      semantic = !semantic;
      divergent = !divergent;
      asked = !asked;
    }

(** {1 Driver} *)

type outcome = Done of result | Failed of string | Timed_out

(* [isolated ~timeout f] runs [f] in a child process, killed by SIGALRM after
   [timeout] seconds, and reads its result back through a pipe. *)
let isolated ~timeout f =
  let rd, wr = Unix.pipe () in
    match Unix.fork () with
    | 0 ->
        Unix.close rd;
        ignore (Unix.alarm timeout);
        let outcome =
          try Done (f ()) with e -> Failed (Printexc.to_string e)
        in
        let oc = Unix.out_channel_of_descr wr in
          Marshal.to_channel oc outcome [];
          close_out oc;
          Unix._exit 0
    | pid ->
        Unix.close wr;
        let ic = Unix.in_channel_of_descr rd in
        let outcome =
          try (Marshal.from_channel ic : outcome)
          with End_of_file -> Timed_out
        in
          close_in ic;
          ignore (Unix.waitpid [] pid);
          outcome

let () =
  let flags_off = ref false and timeout = ref 300 and paths = ref [] in
  let spec =
    [
      ("--flags-off", Arg.Set flags_off, " Compare the baseline with itself");
      ("--timeout", Arg.Set_int timeout, "SECS Per-program time limit (300)");
    ]
  in
    Arg.parse spec
      (fun p -> paths := p :: !paths)
      "equivalence [--flags-off] [--timeout SECS] [DIR|FILE ...]";
    Logs.set_level (Some Logs.Error);
    let files =
      List.concat_map lit_files
        (if !paths = [] then default_dirs else List.rev !paths)
    in
      Printf.printf "equivalence%s: %d programs\n%!"
        (if !flags_off then " (flags off)" else "")
        (List.length files);
      let agree = ref 0
      and different = ref []
      and timed_out = ref []
      and errors = ref []
      and asked = ref 0
      and syntactic = ref 0
      and semantic = ref 0
      and divergent = ref 0 in
        List.iter
          (fun file ->
            let t0 = Unix.gettimeofday () in
            let outcome =
              isolated ~timeout:!timeout (fun () ->
                  compare_program ~flags_off:!flags_off (read_file file)
              )
            in
            let secs = Unix.gettimeofday () -. t0 in
              match outcome with
              | Timed_out ->
                  Printf.printf "%-70s timed out after %.0fs\n%!" file secs;
                  timed_out := file :: !timed_out
              | Failed m ->
                  Printf.printf "%-70s error: %s\n%!" file m;
                  errors := (file, m) :: !errors
              | Done r ->
                  syntactic := !syntactic + r.syntactic;
                  semantic := !semantic + r.semantic;
                  divergent := !divergent + r.divergent;
                  if r.asked then incr asked;
                  if r.differences = [] then incr agree
                  else begin
                    different := (file, r.differences) :: !different;
                    Printf.printf "%-70s DIFFERS\n%!" file;
                    List.iter (Printf.printf "    %s\n%!") r.differences
                  end
          )
          files;
        Printf.printf "\n===== equivalence%s =====\n"
          (if !flags_off then " (flags off)" else "");
        Printf.printf "agree        : %d\n" !agree;
        Printf.printf "DIFFER       : %d\n" (List.length !different);
        Printf.printf "timed out    : %d\n" (List.length !timed_out);
        Printf.printf "errors       : %d\n" (List.length !errors);
        if not !flags_off then
          Printf.printf "asked by query: %d of %d\n" !asked
            (List.length files - List.length !timed_out - List.length !errors);
        Printf.printf
          "execution matches: %d syntactic, %d semantic, %d divergent\n"
          !syntactic !semantic !divergent;
        List.iter
          (fun f -> Printf.printf "  timed out %s\n" f)
          (List.rev !timed_out);
        List.iter
          (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
          (List.rev !errors);
        if !different <> [] || !errors <> [] then exit 1
