(** R1 — golden-diff check target ("--pipeline-diff").

    For every litmus test, runs the classic pipeline through assertion checking
    and renders a canonical, order- and id-independent summary of the result:
    the assertion verdict + the canonicalized execution set ({!Canonicalize}).
    That summary is compared against a committed golden; any divergence is a
    regression in the pipeline (or an intended change to be re-blessed).

    This is the CI gate the bottom-up migration is built on (plan Phase 0): no
    construction refactor lands without the golden diff staying green.

    Usage:
      golden_diff check  [DIR ...]   compare against committed goldens (default)
      golden_diff update [DIR ...]   (re)generate goldens
      golden_diff verify [DIR ...]   run each test twice, assert determinism

    DIR defaults to the four litmus corpora. Goldens live under
    [test/goldens/<litmus-path>.golden]. `check` exits non-zero on any
    mismatch or missing golden. *)

(* mordor_lib is (wrapped false): Context, Parse, Interpret, Elaborations,
   Executions, Assertion, Canonicalize, Types, Uset are all top-level. *)

let default_dirs =
  [
    "litmus-tests";
    "litmus-tests-promising";
    "litmus-tests-refinement";
    "litmus-tests-review";
  ]

let goldens_root = "test/goldens"

let rec lit_files dir =
  if not (Sys.file_exists dir) then []
  else if not (Sys.is_directory dir) then
    if Filename.check_suffix dir ".lit" then [ dir ] else []
  else
    Sys.readdir dir |> Array.to_list |> List.sort compare
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
      (try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ())
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
let render (program : string) : string =
  let options = { Context.default_options with dependencies = true } in
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
        |> Assertion.step_check_assertions)
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
      Printf.sprintf "verdict: %s\nexecutions: %d\n%s\n" verdict
        (List.length execs)
        (Canonicalize.set_signature ~with_predicates:true canon)

let run_check files =
  let pass = ref 0 and mismatch = ref [] and missing = ref [] and errs = ref [] in
    List.iter
      (fun lit ->
        let gp = golden_path lit in
          match
            try `Ok (render (read_file lit)) with e -> `Err (Printexc.to_string e)
          with
          | `Err m -> errs := (lit, m) :: !errs
          | `Ok actual ->
              if not (Sys.file_exists gp) then missing := lit :: !missing
              else if String.equal (read_file gp) actual then incr pass
              else mismatch := lit :: !mismatch)
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
      List.iter (fun (f, m) -> Printf.printf "  error %s: %s\n" f m)
        (List.rev !errs);
      if !mismatch <> [] || !missing <> [] || !errs <> [] then exit 1

let run_update files =
  let written = ref 0 and errs = ref [] in
    List.iter
      (fun lit ->
        match try `Ok (render (read_file lit)) with e -> `Err (Printexc.to_string e) with
        | `Ok actual ->
            write_file (golden_path lit) actual;
            incr written
        | `Err m -> errs := (lit, m) :: !errs)
      files;
    Printf.printf "\n===== golden update =====\nwrote %d goldens, %d errors\n"
      !written (List.length !errs);
    List.iter (fun (f, m) -> Printf.printf "  error %s: %s\n" f m) (List.rev !errs)

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
        | `Err m -> errs := (lit, m) :: !errs)
      files;
    Printf.printf "\n===== determinism verify =====\n";
    Printf.printf "deterministic : %d\n" !ok;
    Printf.printf "NON-DETERMIN. : %d\n" (List.length !flaky);
    Printf.printf "errors        : %d\n" (List.length !errs);
    List.iter (fun f -> Printf.printf "  flaky %s\n" f) (List.rev !flaky);
    if !flaky <> [] then exit 1

let () =
  let argv = Array.to_list Sys.argv in
  let mode, dirs =
    match argv with
    | _ :: mode :: rest -> (mode, if rest = [] then default_dirs else rest)
    | _ -> ("check", default_dirs)
  in
  let files = List.concat_map lit_files dirs in
    Printf.printf "golden %s: %d litmus files\n%!" mode (List.length files);
    match mode with
    | "check" -> run_check files
    | "update" -> run_update files
    | "verify" -> run_verify files
    | m ->
        Printf.eprintf "unknown mode %S (use check|update|verify)\n" m;
        exit 2
