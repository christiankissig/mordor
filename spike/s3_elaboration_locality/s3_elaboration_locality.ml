(* S3 (#16): is the elaboration fixpoint the same run per thread as run on the
   whole program?

   For a program with a parallel block: justifications are generated for the
   whole structure, as the pipeline does, and for each thread on the structure
   restricted to that thread's events and the events outside every thread
   (Init, the code before the block, the code after it). The per-thread sets
   are unioned and compared with the whole-program set, justification by
   justification, on a rendering that does not depend on hash-table order.
   A justification in one set only is reported with the elaboration that
   produced it.

   One line per program:
     <file> threads <n> whole <n> per-thread <n> missing <n> extra <n> [ops] *)

open Types
open Uset
open Expr

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s

let options = { Context.default_options with allow_unknown_model = true }

let interpret program =
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "s3";
    ctx.litmus <- Some program;
    Lwt_main.run
      (Lwt.return ctx |> Parse.step_parse_litmus |> Interpret.step_interpret)

(* [structure] with only the events [keep] says. *)
let restrict (s : symbolic_event_structure) keep : symbolic_event_structure =
  let ev = USet.filter keep in
  let rel = USet.filter (fun (a, b) -> keep a && keep b) in
  let tbl t =
    let t' = Hashtbl.copy t in
      Hashtbl.filter_map_inplace (fun k v -> if keep k then Some v else None) t';
      t'
  in
    {
      s with
      e = ev s.e;
      events = tbl s.events;
      po = rel s.po;
      po_iter = rel s.po_iter;
      rmw = USet.filter (fun (a, _, b) -> keep a && keep b) s.rmw;
      lo = rel s.lo;
      restrict = tbl s.restrict;
      defacto = tbl s.defacto;
      fj = rel s.fj;
      p = tbl s.p;
      conflict = rel s.conflict;
      origin =
        (let t = Hashtbl.copy s.origin in
           Hashtbl.filter_map_inplace
             (fun _ l -> if keep l then Some l else None)
             t;
           t
        );
      loop_indices = tbl s.loop_indices;
      thread_index = tbl s.thread_index;
      write_events = ev s.write_events;
      read_events = ev s.read_events;
      rlx_write_events = ev s.rlx_write_events;
      rlx_read_events = ev s.rlx_read_events;
      fence_events = ev s.fence_events;
      branch_events = ev s.branch_events;
      malloc_events = ev s.malloc_events;
      free_events = ev s.free_events;
      terminal_events = ev s.terminal_events;
    }

let justify structure =
  let ctx' = Context.make_context_with_model options () in
    ctx'.structure <- Some structure;
    let ctx' =
      Lwt_main.run (Lwt.return ctx' |> Elaborations.step_generate_justifications)
    in
      ( Option.get ctx'.justifications,
        Option.value ctx'.justification_derivations ~default:[]
      )

(* The rest of the pipeline from [justs]: the verdict and the canonical
   execution set, as the golden gate renders them. *)
let finish program justs =
  let ctx = interpret program in
  let ctx =
    Lwt_main.run (Lwt.return ctx |> Elaborations.step_generate_justifications)
  in
    ctx.justifications <- Some justs;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx
        |> Executions.step_calculate_dependencies
        |> Assertion.step_check_assertions
        )
    in
    let s = Option.get ctx.structure in
    let execs = Option.get ctx.executions |> USet.values in
      ( ctx.valid,
        Canonicalize.set_signature ~with_predicates:true
          (Canonicalize.canonicalize_set s execs)
      )

let render (j : justification) =
  let sorted l = List.sort_uniq compare l in
  let pairs r =
    USet.values r
    |> List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
    |> sorted
    |> String.concat ","
  in
    Printf.sprintf "%s | p %s | d %s | fwd %s | we %s" (show_event j.w)
      (List.map Expr.to_string j.p |> sorted |> String.concat " && ")
      (USet.values j.d |> sorted |> String.concat ",")
      (pairs j.fwd) (pairs j.we)

let op_of derivations (j : justification) =
  let r = Justifications.Justification.to_string j in
    List.assoc_opt r derivations |> Option.value ~default:"?" |> fun op ->
    List.hd (String.split_on_char ' ' op)

let () =
  List.iter
    (fun file ->
      match interpret (read_file file) with
      | exception e -> Printf.printf "%s ERROR %s\n" file (Printexc.to_string e)
      | ctx ->
          let s = Option.get ctx.structure in
          let threads =
            Hashtbl.fold
              (fun _ t acc ->
                if t > 0 && not (List.mem t acc) then t :: acc else acc
              )
              s.thread_index []
            |> List.sort compare
          in
            if List.length threads < 2 then
              Printf.printf "%s single-threaded\n" file
            else
              let whole, whole_derivs = justify s in
              let thread_of l = Hashtbl.find_opt s.thread_index l in
              (* Thread [t'] is nested in thread [t] when an event of [t] is
                 po-before one of [t']: sibling threads are not po-related. *)
              let nested_in t t' =
                t <> t'
                && USet.exists
                     (fun (a, b) ->
                       thread_of a = Some t && thread_of b = Some t'
                     )
                     s.po
              in
              let top_level =
                List.filter
                  (fun t' -> not (List.exists (fun t -> nested_in t t') threads))
                  threads
              in
              let in_fragment t l =
                match thread_of l with
                | None | Some 0 -> true
                | Some t' -> t' = t || nested_in t t'
              in
              (* Join-aware: each top-level thread with the blocks nested in it
                 elaborated on its own, and what runs outside every thread --
                 before the block, and after the join -- with the whole. *)
              let join_aware =
                List.concat_map
                  (fun t ->
                    let js, _ = justify (restrict s (in_fragment t)) in
                      List.filter
                        (fun (j : justification) ->
                          match thread_of j.w.label with
                          | Some t' -> t' <> 0 && in_fragment t j.w.label
                          | None -> false
                        )
                        js
                  )
                  top_level
                @ List.filter
                    (fun (j : justification) ->
                      match thread_of j.w.label with
                      | None | Some 0 -> true
                      | Some _ -> false
                    )
                    whole
              in
              let per_thread =
                List.concat_map
                  (fun t ->
                    let keep l =
                      match Hashtbl.find_opt s.thread_index l with
                      | Some t' -> t' = t || t' = 0
                      | None -> true
                    in
                    let js, derivs = justify (restrict s keep) in
                      List.map (fun j -> (j, derivs)) js
                  )
                  threads
              in
              let index l f =
                let h = Hashtbl.create 64 in
                  List.iter (fun x -> Hashtbl.replace h (render (f x)) x) l;
                  h
              in
              let w = index whole Fun.id and p = index per_thread fst in
              let only a b =
                Hashtbl.fold
                  (fun k v acc -> if Hashtbl.mem b k then acc else v :: acc)
                  a []
              in
              let missing = only w p and extra = only p w in
              let ops =
                List.map (op_of whole_derivs) missing
                @ List.map (fun (j, d) -> "+" ^ op_of d j) extra
                |> List.sort compare
                |> List.fold_left
                     (fun acc op ->
                       match acc with
                       | (o, n) :: rest when o = op -> (o, n + 1) :: rest
                       | _ -> (op, 1) :: acc
                     )
                     []
                |> List.rev_map (fun (o, n) -> Printf.sprintf "%s:%d" o n)
                |> String.concat " "
              in
              let join_aware_same =
                List.map render join_aware
                |> List.sort_uniq compare
                = (List.map render whole |> List.sort_uniq compare)
              in
              let same_executions =
                if missing = [] && extra = [] then ""
                else
                  let program = read_file file in
                  let v1, e1 = finish program whole in
                  let v2, e2 = finish program (List.map fst per_thread) in
                  let verdict = function
                    | Some true -> "valid"
                    | Some false -> "invalid"
                    | None -> "none"
                  in
                  let count e =
                    List.length
                      (List.filter
                         (String.starts_with ~prefix:"--- execution")
                         (String.split_on_char '\n' e)
                      )
                  in
                  let ja =
                    List.map render join_aware |> List.sort_uniq compare
                  in
                  let wh = List.map render whole |> List.sort_uniq compare in
                  let v3, e3 = finish program join_aware in
                    Printf.sprintf
                      "executions: %s (%d whole, %d per-thread), verdict \
                       %s/%s; join-aware: justifications %s, executions %s, \
                       verdict %s"
                      (if e1 = e2 then "same" else "DIFFER")
                      (count e1) (count e2) (verdict v1) (verdict v2)
                      (if ja = wh then "same" else "DIFFER")
                      (if e1 = e3 then "same" else "DIFFER")
                      (verdict v3)
              in
                if Sys.getenv_opt "S3_SHOW" <> None then begin
                  List.iter
                    (fun j -> Printf.printf "  - %s\n" (render j))
                    missing;
                  List.iter
                    (fun (j, _) -> Printf.printf "  + %s\n" (render j))
                    extra
                end;
                Printf.printf
                  "%s threads %d whole %d per-thread %d missing %d extra %d %s \
                   join-aware %s %s\n\
                   %!"
                  file (List.length threads) (Hashtbl.length w)
                  (Hashtbl.length p) (List.length missing) (List.length extra)
                  ops
                  (if join_aware_same then "same" else "DIFFERS")
                  same_executions
    )
    (List.tl (Array.to_list Sys.argv))
