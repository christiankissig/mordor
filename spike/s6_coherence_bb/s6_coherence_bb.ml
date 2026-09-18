(* S6 (#18): branch and bound over coherence orders, against the exhaustive
   search it prunes.

   For one litmus file: run the pipeline to its executions once, then ask
   every registered model about every execution three times -- exhaustive,
   pruned, exhaustive again -- and compare the pruned answers, verdict and
   admitting coherence order both, with the exhaustive ones. Timing compares
   the pruned pass with the second exhaustive pass, when the solver's caches
   are as warm for one as for the other.

   Prints one line per model:
     <model> <executions> <differing> <t_full> <t_pruned> <leaves_full>
     <leaves_pruned> <partial_checks> <pruned> *)

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s

let answer s e m =
  match Coherence.check_for_coherence s e { coherent = m } with
  | None -> "none"
  | Some co ->
      Uset.USet.values co
      |> List.sort compare
      |> List.map (fun (a, b) -> Printf.sprintf "%d-%d" a b)
      |> String.concat " "
  | exception ex -> "EXN " ^ Printexc.to_string ex

let pass ~prune s execs m =
  Coherence.S6.prune := prune;
  Coherence.S6.reset ();
  let t0 = Unix.gettimeofday () in
  let answers = List.map (fun e -> answer s e m) execs in
  let t = Unix.gettimeofday () -. t0 in
    ( answers,
      t,
      !Coherence.S6.leaf_checks,
      !Coherence.S6.partial_checks,
      !Coherence.S6.pruned
    )

let () =
  let file = Sys.argv.(1) in
  let options =
    {
      Context.default_options with
      dependencies = true;
      allow_unknown_model = true;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "s6";
    ctx.litmus <- Some (read_file file);
    match
      Lwt_main.run
        (Lwt.return ctx
        |> Parse.step_parse_litmus
        |> Interpret.step_interpret
        |> Elaborations.step_generate_justifications
        |> Executions.step_calculate_dependencies
        )
    with
    | exception e -> Printf.printf "PIPELINE %s\n" (Printexc.to_string e)
    | ctx -> (
        match (ctx.structure, ctx.executions) with
        | Some s, Some es ->
            let execs = Uset.USet.values es in
              List.iter
                (fun m ->
                  let full, _, _, _, _ = pass ~prune:false s execs m in
                  let pruned, t_pruned, leaves_pruned, partial, cut =
                    pass ~prune:true s execs m
                  in
                  let full', t_full, leaves_full, _, _ =
                    pass ~prune:false s execs m
                  in
                  let differing =
                    List.fold_left2
                      (fun n a b -> if a = b then n else n + 1)
                      0 full pruned
                    + if full = full' then 0 else 1000000
                  in
                    Printf.printf "%s %d %d %.6f %.6f %d %d %d %d\n" m
                      (List.length execs) differing t_full t_pruned leaves_full
                      leaves_pruned partial cut
                )
                (List.sort compare (Coherence.ModelRegistry.names ()))
        | _ -> print_endline "NO EXECUTIONS"
      )
