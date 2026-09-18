(* S8 (#20): po_iter as each loop occurrence produces it from its own body,
   against po_iter as symbolic loop semantics rebuilds it at the end from
   loop_indices (Interpret.S8).

   For each program: the two relations, and every pair they disagree on,
   classified by whether its events conflict in the structure and whether they
   are the same event of the program in two copies -- the same source span. *)

open Types
open Uset

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s

let interpret ~compositional program =
  Interpret.S8.compositional_po_iter := compositional;
  let options =
    {
      Context.default_options with
      allow_unknown_model = true;
      loop_semantics = Context.Symbolic;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "s8";
    ctx.litmus <- Some program;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx |> Parse.step_parse_litmus |> Interpret.step_interpret)
    in
      (Option.get ctx.structure, Option.get ctx.source_spans)

let () =
  List.iter
    (fun file ->
      let program = read_file file in
      let classic, spans = interpret ~compositional:false program in
      let local, _ = interpret ~compositional:true program in
      let missing = USet.set_minus classic.po_iter local.po_iter in
      let extra = USet.set_minus local.po_iter classic.po_iter in
      let conflicting =
        USet.filter (fun p -> USet.mem classic.conflict p) missing
      in
      let copies =
        USet.filter
          (fun (a, b) ->
            match (Hashtbl.find_opt spans a, Hashtbl.find_opt spans b) with
            | Some sa, Some sb -> sa = sb
            | _ -> false
          )
          missing
      in
        Printf.printf
          "%-60s po_iter %5d  compositional %5d  missing %5d (in conflict %5d, \
           copies of one event %4d)  extra %d\n"
          file
          (USet.size classic.po_iter)
          (USet.size local.po_iter) (USet.size missing) (USet.size conflicting)
          (USet.size copies) (USet.size extra)
    )
    (List.tl (Array.to_list Sys.argv))
