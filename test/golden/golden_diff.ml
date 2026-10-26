(** R1 — golden-diff check target ("--pipeline-diff").

    For every litmus test, runs the classic pipeline through assertion checking
    and renders a canonical, order- and id-independent summary of the result:
    the assertion verdict + the canonicalized execution set ({!Canonicalize}).
    That summary is compared against a committed golden; any divergence is a
    regression in the pipeline (or an intended change to be re-blessed).

    This is the CI gate the bottom-up migration is built on (plan Phase 0): no
    construction refactor lands without the golden diff staying green.

    Usage: golden_diff check [DIR ...] compare against committed goldens
    (default) golden_diff update [DIR ...] (re)generate goldens golden_diff
    verify [DIR ...] run each test twice, assert determinism golden_diff
    check-order [DIR ...] render each test with sets iterated both ways, assert
    the pipeline does not depend on the order golden_diff check-query [DIR ...]
    decide each test's assertion by enumeration and by query (R16), assert the
    verdicts agree golden_diff check-regions [DIR ...] render each test with
    allocations kept apart by their bases and by their regions (R17), list every
    test whose verdict or executions differ

    DIR defaults to the litmus corpora in [default_dirs]. Goldens live under
    [test/goldens/<litmus-path>.golden]. `check` exits non-zero on any mismatch
    or missing golden. *)

(* mordor_lib is (wrapped false): Context, Parse, Interpret, Elaborations,
   Executions, Assertion, Canonicalize, Types, Uset are all top-level. *)

let default_dirs =
  [
    "litmus-tests";
    (* litmus-tests-refinement/ is gone: with refinement chains decided (#85,
       #87) all six of its files are in litmus-tests/. litmus-tests-review/
       is gone too: its last parked test returned with #63. *)
  ]

let goldens_root = "test/goldens"

let rec lit_files dir =
  if not (Sys.file_exists dir) then []
  else if not (Sys.is_directory dir) then
    if Filename.check_suffix dir ".lit" then [ dir ] else []
  else
    Sys.readdir dir
    |> Array.to_list
    |> List.sort compare
    |> List.concat_map (fun name -> lit_files (Filename.concat dir name))

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
    close_in ic;
    s

let write_file path contents =
  let dir = Filename.dirname path in
  let rec mkdirs d =
    if not (Sys.file_exists d) then begin
      mkdirs (Filename.dirname d);
      try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
    end
  in
    mkdirs dir;
    let oc = open_out_bin path in
      output_string oc contents;
      close_out oc

let golden_path lit_file = Filename.concat goldens_root (lit_file ^ ".golden")

(* Run the pipeline through assertion checking and render the canonical
   summary: verdict + canonicalized execution set. A fresh context per call
   (the steps mutate it). *)
let render ?(regions = Context.default_options.disjoint_regions)
    (program : string) : string =
  (* A test may name a model MoRDor does not implement. Since #86 that is fatal
     unless the caller opts in; a golden is a record of what the pipeline does
     today, so opt in and let the fallback verdict be recorded as before. *)
  let options =
    {
      Context.default_options with
      dependencies = true;
      allow_unknown_model = true;
      disjoint_regions = regions;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "golden";
    ctx.litmus <- Some program;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx
        |> Parse.step_parse_litmus
        |> Interpret.step_interpret
        |> Elaborations.step_generate_justifications
        |> Executions.step_calculate_dependencies
        |> Assertion.step_check_assertions
        )
    in
    let verdict =
      match ctx.valid with
      | Some true -> "valid"
      | Some false -> "invalid"
      | None -> "none"
    in
    let structure, execs =
      match (ctx.structure, ctx.executions) with
      | Some s, Some e -> (s, Uset.USet.values e)
      | _ -> failwith "pipeline produced no structure/executions"
    in
    let canon = Canonicalize.canonicalize_set structure execs in
    (* A conjunction's assertions each have a verdict of their own; the
       executions are the first assertion's model's. *)
    let verdicts =
      String.concat ""
        (List.map
           (fun (assertion, holds) ->
             Printf.sprintf "  %s %s\n"
               (if holds then "holds" else "fails")
               assertion
           )
           ctx.assertion_verdicts
        )
    in
      Printf.sprintf "verdict: %s\n%sexecutions: %d\n%s\n" verdict verdicts
        (List.length execs)
        (Canonicalize.set_signature ~with_predicates:true canon)

(* The verdict of [program]'s assertions -- valid, and undefined behaviour --
   by enumeration, or asked by query (R16), with how the query was answered and
   the seconds it took. *)
let verdict ~by_query (program : string) =
  let options =
    {
      Context.default_options with
      dependencies = true;
      allow_unknown_model = true;
      by_query;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "golden";
    ctx.litmus <- Some program;
    let t0 = Unix.gettimeofday () in
    let ctx =
      Lwt_main.run
        (Lwt.return ctx
        |> Parse.step_parse_litmus
        |> Interpret.step_interpret
        |> Semantics.step_calculate_executions
        |> Assertion.step_check_assertions
        )
    in
    let show = function
      | Some b -> string_of_bool b
      | None -> "undecided"
    in
      ( Printf.sprintf "valid=%s ub=%s" (show ctx.valid)
          (show ctx.undefined_behaviour),
        ctx.query_report,
        ctx.valid,
        ctx.undefined_behaviour,
        Unix.gettimeofday () -. t0
      )

(* Query gate (R16, V1): every test's verdict asked by query is the verdict
   enumeration gives. Undefined behaviour is compared where the query asks
   about it -- a [ub] assertion, or none -- and the condition's verdict where
   there is a condition. An undecided query is reported, not counted as a
   difference: it gives no verdict to disagree with. A test the query cannot
   ask about falls back to enumeration and is counted apart. *)
let run_check_query files =
  let agree = ref 0
  and differ = ref []
  and undecided = ref []
  and enumerated = ref 0
  and errs = ref []
  and t_enum = ref 0.
  and t_query = ref 0. in
    List.iter
      (fun lit ->
        match
          let program = read_file lit in
          let enum, _, ev, eub, te = verdict ~by_query:false program in
          let query, report, qv, qub, tq = verdict ~by_query:true program in
            t_enum := !t_enum +. te;
            t_query := !t_query +. tq;
            (lit, enum, ev, eub, query, report, qv, qub, te, tq)
        with
        | _, _, _, _, _, None, _, _, _, _ -> incr enumerated
        | lit, enum, ev, eub, query, Some r, qv, qub, te, tq ->
            Printf.printf "%-70s %6.2fs %6.2fs %s\n%!" lit te tq
              (Context.show_query_report r);
            let same a b = a = None || b = None || a = b in
              if qv = None && qub = None then undecided := lit :: !undecided
              else if same ev qv && same eub qub then incr agree
              else
                differ :=
                  Printf.sprintf "%s: enumeration %s, query %s" lit enum query
                  :: !differ
        | exception e -> errs := (lit, Printexc.to_string e) :: !errs
      )
      files;
    Printf.printf "\n===== query check =====\n";
    Printf.printf "agree       : %d\n" !agree;
    Printf.printf "DIFFER      : %d\n" (List.length !differ);
    Printf.printf "undecided   : %d\n" (List.length !undecided);
    Printf.printf "enumerated  : %d (not a question for a query)\n" !enumerated;
    Printf.printf "errors      : %d\n" (List.length !errs);
    Printf.printf "time        : enumeration %.1fs, query %.1fs\n" !t_enum
      !t_query;
    List.iter (fun d -> Printf.printf "  differs %s\n" d) (List.rev !differ);
    List.iter (fun f -> Printf.printf "  undecided %s\n" f) (List.rev !undecided);
    List.iter
      (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
      (List.rev !errs);
    if !differ <> [] || !errs <> [] then exit 1

(* Region gate (R17): what stating that allocations occupy disjoint regions
   changes. A verdict that changes is a difference in what the tool says the
   program means, and is listed apart from a change in the executions alone.
   Reports; fails only on errors. *)
let run_check_regions files =
  let same = ref 0
  and verdicts = ref []
  and executions = ref []
  and errs = ref [] in
  let verdict_lines r =
    String.split_on_char '\n' r
    |> List.filter (fun l ->
        String.starts_with ~prefix:"verdict:" l
        || String.starts_with ~prefix:"  holds" l
        || String.starts_with ~prefix:"  fails" l
    )
  in
  let count r =
    List.find_map
      (fun l ->
        if String.starts_with ~prefix:"executions: " l then
          Some (String.sub l 12 (String.length l - 12))
        else None
      )
      (String.split_on_char '\n' r)
    |> Option.value ~default:"?"
  in
    List.iter
      (fun lit ->
        match
          let program = read_file lit in
            (render ~regions:false program, render ~regions:true program)
        with
        | bases, regions ->
            if String.equal bases regions then incr same
            else if verdict_lines bases <> verdict_lines regions then
              verdicts :=
                Printf.sprintf "%s: %s -> %s" lit
                  (String.concat "; " (verdict_lines bases))
                  (String.concat "; " (verdict_lines regions))
                :: !verdicts
            else
              (* The first line that differs, to say what did. *)
              let rec first = function
                | a :: x, b :: y -> if a = b then first (x, y) else (a, b)
                | a :: _, [] -> (a, "")
                | [], b :: _ -> ("", b)
                | [], [] -> ("", "")
              in
              let a, b =
                first
                  ( String.split_on_char '\n' bases,
                    String.split_on_char '\n' regions
                  )
              in
                executions :=
                  Printf.sprintf
                    "%s: %s -> %s executions\n      - %s\n      + %s" lit
                    (count bases) (count regions) a b
                  :: !executions
        | exception e -> errs := (lit, Printexc.to_string e) :: !errs
      )
      files;
    Printf.printf "\n===== region check =====\n";
    Printf.printf "unchanged          : %d\n" !same;
    Printf.printf "VERDICT CHANGED    : %d\n" (List.length !verdicts);
    Printf.printf "executions changed : %d\n" (List.length !executions);
    Printf.printf "errors             : %d\n" (List.length !errs);
    List.iter (fun d -> Printf.printf "  verdict %s\n" d) (List.rev !verdicts);
    List.iter
      (fun d -> Printf.printf "  executions %s\n" d)
      (List.rev !executions);
    List.iter
      (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
      (List.rev !errs);
    if !errs <> [] then exit 1

let run_check files =
  let pass = ref 0
  and mismatch = ref []
  and missing = ref []
  and errs = ref [] in
    List.iter
      (fun lit ->
        let gp = golden_path lit in
          match
            try `Ok (render (read_file lit))
            with e -> `Err (Printexc.to_string e)
          with
          | `Err m -> errs := (lit, m) :: !errs
          | `Ok actual ->
              if not (Sys.file_exists gp) then missing := lit :: !missing
              else if String.equal (read_file gp) actual then incr pass
              else mismatch := lit :: !mismatch
      )
      files;
    Printf.printf "\n===== golden check =====\n";
    Printf.printf "pass      : %d\n" !pass;
    Printf.printf "MISMATCH  : %d\n" (List.length !mismatch);
    Printf.printf "MISSING   : %d\n" (List.length !missing);
    Printf.printf "errors    : %d\n" (List.length !errs);
    let dump label xs =
      if xs <> [] then begin
        Printf.printf "\n-- %s --\n" label;
        List.iter (fun x -> Printf.printf "  %s\n" x) (List.rev xs)
      end
    in
      dump "mismatches" !mismatch;
      dump "missing goldens" !missing;
      List.iter
        (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
        (List.rev !errs);
      if !mismatch <> [] || !missing <> [] || !errs <> [] then exit 1

let run_update files =
  let written = ref 0 and errs = ref [] in
    List.iter
      (fun lit ->
        match
          try `Ok (render (read_file lit))
          with e -> `Err (Printexc.to_string e)
        with
        | `Ok actual ->
            write_file (golden_path lit) actual;
            incr written
        | `Err m -> errs := (lit, m) :: !errs
      )
      files;
    Printf.printf "\n===== golden update =====\nwrote %d goldens, %d errors\n"
      !written (List.length !errs);
    List.iter
      (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
      (List.rev !errs)

(* Determinism gate: render each test twice and require byte-identical output.
   A committed golden is only trustworthy if the pipeline is deterministic. *)
let run_verify files =
  let ok = ref 0 and flaky = ref [] and errs = ref [] in
    List.iter
      (fun lit ->
        match
          try
            let a = render (read_file lit) in
            let b = render (read_file lit) in
              `Ok (String.equal a b)
          with e -> `Err (Printexc.to_string e)
        with
        | `Ok true -> incr ok
        | `Ok false -> flaky := lit :: !flaky
        | `Err m -> errs := (lit, m) :: !errs
      )
      files;
    Printf.printf "\n===== determinism verify =====\n";
    Printf.printf "deterministic : %d\n" !ok;
    Printf.printf "NON-DETERMIN. : %d\n" (List.length !flaky);
    Printf.printf "errors        : %d\n" (List.length !errs);
    List.iter (fun f -> Printf.printf "  flaky %s\n" f) (List.rev !flaky);
    if !flaky <> [] then exit 1

(* Order gate: render each test with sets iterated in their usual order and
   in its reverse, and require byte-identical output. What the pipeline
   computes must be a function of the program, not of the order a hash set
   happens to hold its members in. *)
let run_check_order files =
  let ok = ref 0 and differ = ref [] and errs = ref [] in
    List.iter
      (fun lit ->
        match
          let program = read_file lit in
          let forward = render program in
            Uset.USet.reversed_iteration := true;
            let reversed =
              Fun.protect
                ~finally:(fun () -> Uset.USet.reversed_iteration := false)
                (fun () -> render program)
            in
              String.equal forward reversed
        with
        | true -> incr ok
        | false -> differ := lit :: !differ
        | exception e -> errs := (lit, Printexc.to_string e) :: !errs
      )
      files;
    Printf.printf "\n===== iteration-order check =====\n";
    Printf.printf "order-independent : %d\n" !ok;
    Printf.printf "ORDER-DEPENDENT   : %d\n" (List.length !differ);
    Printf.printf "errors            : %d\n" (List.length !errs);
    List.iter (fun f -> Printf.printf "  differs %s\n" f) (List.rev !differ);
    List.iter
      (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
      (List.rev !errs);
    if !differ <> [] || !errs <> [] then exit 1

let () =
  let argv = Array.to_list Sys.argv in
  let mode, dirs =
    match argv with
    | _ :: mode :: rest -> (mode, if rest = [] then default_dirs else rest)
    | _ -> ("check", default_dirs)
  in
  let files = List.concat_map lit_files dirs in
    Printf.printf "golden %s: %d litmus files\n%!" mode (List.length files);
    (* Run from elsewhere than the repo root, the corpus is not found; that must
       not pass as a check of nothing. *)
    if files = [] then begin
      Printf.eprintf
        "golden_diff: no .lit files under %s (working directory %s)\n"
        (String.concat ", " dirs) (Sys.getcwd ());
      exit 2
    end;
    match mode with
    | "check" -> run_check files
    | "update" -> run_update files
    | "verify" -> run_verify files
    | "check-order" -> run_check_order files
    | "check-query" -> run_check_query files
    | "check-regions" -> run_check_regions files
    | m ->
        Printf.eprintf
          "unknown mode %S (use \
           check|update|verify|check-order|check-query|check-regions)\n"
          m;
        exit 2
