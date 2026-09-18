(** S8 (#20): characterization goldens for loops under symbolic loop semantics.

    {!Golden_diff} compares executions under the default loop semantics, which
    unrolls loops, and so says nothing of what symbolic loop semantics builds.
    This renders, for each program with a loop, the interpreted structure's
    [po], [po_iter], [conflict] and [restrict], and the loop tables
    [loop_indices] and [loop_conditions], each sorted, under
    [loop_semantics = Symbolic], and compares that with a committed golden. A
    set of more than 5000 elements is kept as its size and a digest.

    Usage (from the repo root):
    - [loop_goldens check] compares every committed golden with the program it
      is named after;
    - [loop_goldens update FILE ...] (re)writes the goldens of the given
      programs.

    Goldens live under [test/goldens-loops/<program path>.structure]. The set of
    committed goldens is the corpus: [check] walks it rather than the program
    directories, which hold local programs that are not in the repository. *)

open Types
open Uset
open Expr

let goldens_root = "test/goldens-loops"

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s

let rec mkdirs d =
  if not (Sys.file_exists d) then begin
    mkdirs (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let write_file path contents =
  mkdirs (Filename.dirname path);
  let oc = open_out_bin path in
    output_string oc contents;
    close_out oc

let interpret program =
  let options =
    {
      Context.default_options with
      allow_unknown_model = true;
      loop_semantics = Context.Symbolic;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "loop-golden";
    ctx.litmus <- Some program;
    let ctx =
      Lwt_main.run
        (Lwt.return ctx |> Parse.step_parse_litmus |> Interpret.step_interpret)
    in
      Option.get ctx.structure

let render (s : symbolic_event_structure) =
  let pair (a, b) = Printf.sprintf "(%d,%d)" a b in
  let exprs es = String.concat " && " (List.map Expr.to_string es) in
  (* A large set is kept as its size and a digest: rcu-3's conflict relation
     alone would be 7MB. A change still shows; what changed does not. *)
  let set name show u =
    let rendered =
      String.concat " " (USet.values u |> List.map show |> List.sort compare)
    in
      if USet.size u <= 5000 then name ^ ": " ^ rendered
      else
        Printf.sprintf "%s: %d elements, md5 %s" name (USet.size u)
          (Digest.to_hex (Digest.string rendered))
  in
  let table name show_v tbl =
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl []
    |> List.sort compare
    |> List.map (fun (k, v) -> Printf.sprintf "%s %d: %s" name k (show_v v))
    |> String.concat "\n"
  in
    String.concat "\n"
      [
        table "event" (fun (e : event) -> show_event_type e.typ) s.events;
        set "po" pair s.po;
        set "po_iter" pair s.po_iter;
        set "conflict" pair s.conflict;
        table "restrict" exprs s.restrict;
        table "loop_indices"
          (fun ls -> String.concat ";" (List.map string_of_int ls))
          s.loop_indices;
        table "loop_conditions" exprs s.loop_conditions;
      ]
    ^ "\n"

let golden_path program = Filename.concat goldens_root (program ^ ".structure")

let rec goldens dir =
  if Sys.is_directory dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.sort compare
    |> List.concat_map (fun name -> goldens (Filename.concat dir name))
  else if Filename.check_suffix dir ".structure" then [ dir ]
  else []

let program_of golden =
  let prefix = goldens_root ^ "/" in
  let n = String.length prefix in
    Filename.chop_suffix
      (String.sub golden n (String.length golden - n))
      ".structure"

let check () =
  let pass = ref 0 and failed = ref [] in
    List.iter
      (fun golden ->
        let program = program_of golden in
          match render (interpret (read_file program)) with
          | actual when String.equal actual (read_file golden) -> incr pass
          | _ -> failed := (program, "MISMATCH") :: !failed
          | exception e -> failed := (program, Printexc.to_string e) :: !failed
      )
      (goldens goldens_root);
    Printf.printf
      "===== loop goldens check =====\npass      : %d\nfailed    : %d\n" !pass
      (List.length !failed);
    List.iter
      (fun (p, why) -> Printf.printf "  %s: %s\n" p why)
      (List.rev !failed);
    if !failed <> [] then exit 1

let update programs =
  List.iter
    (fun program ->
      match render (interpret (read_file program)) with
      | rendered ->
          write_file (golden_path program) rendered;
          Printf.printf "wrote %s\n" (golden_path program)
      | exception e ->
          Printf.printf "error %s: %s\n" program (Printexc.to_string e)
    )
    programs

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] | [ "check" ] -> check ()
  | "update" :: programs -> update programs
  | _ ->
      prerr_endline "usage: loop_goldens check | loop_goldens update FILE ...";
      exit 2
