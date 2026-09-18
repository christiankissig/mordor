(** S1 (#14) -- relabeling feasibility and cost.

    Interprets a program's fragments separately -- the statements before its
    parallel block, each thread of the block, and the continuation after it --
    each with an [events_t], and so an allocator, of its own. Every fragment
    therefore numbers its events from 0 and names its symbols from α. The
    fragments are then relabelled by offset and composed with the ordinary
    combinators, and the result is compared, field by field and with no
    renumbering in between, against the classic interpretation of the whole
    program.

    Uses only the public interfaces of [mordor_lib]. *)

open Types
open Uset
module SES = Eventstructures.SymbolicEventStructure
module Alloc = Interpret.Allocator

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s

let rec lit_files path =
  if not (Sys.file_exists path) then []
  else if Sys.is_directory path then
    Sys.readdir path
    |> Array.to_list
    |> List.sort compare
    |> List.concat_map (fun n -> lit_files (Filename.concat path n))
  else if Filename.check_suffix path ".lit" then [ path ]
  else []

let now = Unix.gettimeofday

(** {1 Program shape} *)

(* A statement the prefix may hold: one event chain, no choice. A branching
   prefix duplicates its continuation once per branch, which is S2's question
   (sequencing with copies), not S1's. *)
let rec straight (node : Context.ir_node) =
  match Ir.get_stmt node with
  | Ir.Threads _ | If _ | While _ | Do _ | Cas _ -> false
  | Labeled { stmt; _ } -> straight stmt
  | _ -> true

let rec has_threads (nodes : Context.ir_node list) =
  List.exists
    (fun (n : Context.ir_node) ->
      match Ir.get_stmt n with
      | Ir.Threads _ -> true
      | If { then_body; else_body; _ } ->
          has_threads then_body
          || Option.fold ~none:false ~some:has_threads else_body
      | While { body; _ } | Do { body; _ } -> has_threads body
      | Labeled { stmt; _ } -> has_threads [ stmt ]
      | _ -> false
    )
    nodes

type shape = {
  prefix : Context.ir_node list;
  threads : Context.ir_node list list;
  rest : Context.ir_node list;
}

let shape_of (stmts : Context.ir_node list) : (shape, string) result =
  let rec split acc = function
    | [] -> Error "no parallel block"
    | (n : Context.ir_node) :: rest -> (
        match Ir.get_stmt n with
        | Ir.Threads { threads } -> Ok (List.rev acc, threads, rest)
        | _ when straight n -> split (n :: acc) rest
        | _ -> Error "branching prefix"
      )
  in
    match split [] stmts with
    | Error e -> Error e
    | Ok (prefix, threads, rest) ->
        if List.exists has_threads threads || has_threads rest then
          Error "nested or repeated parallel block"
        else Ok { prefix; threads; rest }

(** {1 Relabelling} *)

(* How many symbols an allocator has handed out. The interface has no way to
   ask, so ask for one more and find its place in a fresh allocator's run. *)
let handed_out next alloc =
  let probe = next alloc in
  let fresh = Alloc.create () in
  let rec go i = if String.equal (next fresh) probe then i else go (i + 1) in
    go 0

let names next n =
  let a = Alloc.create () in
    Array.init n (fun _ -> next a)

(* A symbol a fragment inherits through its initial register environment. It
   stands in for the inherited symbol while the fragment is interpreted, so that
   the fragment's own α cannot capture the enclosing program's. *)
let placeholder j = "α" ^ string_of_int (1_000_000 + j)

let symbols_of_env (env : (string, expr) Hashtbl.t) =
  Hashtbl.fold (fun _ e acc -> Expr.Expr.get_symbols e @ acc) env []
  |> List.sort_uniq String.compare

let map_tbl fk fv tbl =
  let t = Hashtbl.create (max 16 (Hashtbl.length tbl)) in
    Hashtbl.iter (fun k v -> Hashtbl.replace t (fk k) (fv v)) tbl;
    t

(** [relabel ~off ~relab ?thread s] is [s] with every event label shifted by
    [off], every symbol renamed by [relab], and, if [thread] is given, every
    indexed event moved to that thread. *)
let relabel ~off ~(relab : string -> string option) ?thread
    (s : symbolic_event_structure) : symbolic_event_structure =
  let l x = x + off in
  let pair (a, b) = (l a, l b) in
  let ex = Expr.Expr.relabel ~relab in
  let sym x = Option.value (relab x) ~default:x in
  (* A UB assumption is recorded in the environment under a key that spells out
     the symbol it is about (interpret.ml, ub_assume), so there is a symbol
     inside a string for the relabelling to find. *)
  let env_key k =
    let prefix = Interpret.ub_fact_prefix in
    let n = String.length prefix in
      if String.length k > n && String.sub k 0 n = prefix then
        prefix ^ sym (String.sub k n (String.length k - n))
      else k
  in
  let event (ev : event) =
    {
      (* Event.relabel covers loc, rval and wval. A branch event carries its
         guard in [cond], which it leaves alone. *)
      (Events.Event.relabel ~relab ev)
      with
      label = l ev.label;
      cond = Option.map ex ev.cond;
    }
  in
    {
      e = USet.map l s.e;
      events = map_tbl l event s.events;
      po = USet.map pair s.po;
      po_iter = USet.map pair s.po_iter;
      rmw = USet.map (fun (a, c, b) -> (l a, ex c, l b)) s.rmw;
      lo = USet.map pair s.lo;
      restrict = map_tbl l (List.map ex) s.restrict;
      defacto = map_tbl l (List.map ex) s.defacto;
      fj = USet.map pair s.fj;
      p = map_tbl l (map_tbl env_key ex) s.p;
      constraints = List.map ex s.constraints;
      conflict = USet.map pair s.conflict;
      origin = map_tbl sym l s.origin;
      loop_indices = map_tbl l Fun.id s.loop_indices;
      loop_conditions = s.loop_conditions;
      thread_index =
        map_tbl l (fun t -> Option.value thread ~default:t) s.thread_index;
      write_events = USet.map l s.write_events;
      read_events = USet.map l s.read_events;
      rlx_write_events = USet.map l s.rlx_write_events;
      rlx_read_events = USet.map l s.rlx_read_events;
      fence_events = USet.map l s.fence_events;
      branch_events = USet.map l s.branch_events;
      malloc_events = USet.map l s.malloc_events;
      free_events = USet.map l s.free_events;
      terminal_events = USet.map l s.terminal_events;
    }

(* Drop one event: the terminal a fragment interpreted on its own ends with,
   where in the whole program the next fragment follows instead. *)
let without (s : symbolic_event_structure) x : symbolic_event_structure =
  let keep l = l <> x in
  let keep2 (a, b) = a <> x && b <> x in
  let drop tbl =
    let t = Hashtbl.copy tbl in
      Hashtbl.remove t x;
      t
  in
    {
      s with
      e = USet.filter keep s.e;
      events = drop s.events;
      po = USet.filter keep2 s.po;
      restrict = drop s.restrict;
      defacto = drop s.defacto;
      p = drop s.p;
      conflict = USet.filter keep2 s.conflict;
      terminal_events = USet.filter keep s.terminal_events;
    }

(** {1 Fragments} *)

type fragment = {
  structure : symbolic_event_structure;  (** Relabelled. *)
  labels : int;  (** Labels the fragment's allocator handed out. *)
  greek : int;
  zh : int;
  globals : string list;
  t_interpret : float;
  t_relabel : float;
}

type cursor = { off : int; g : int; z : int }

(* Interpret [stmts] as a fragment of its own, in [env], and relabel it to sit
   at [cur]. [env]'s symbols belong to the enclosing program and already carry
   their final names. *)
let fragment ~ubopt ~defacto ?thread (cur : cursor) env stmts : fragment =
  let inherited = symbols_of_env env |> Array.of_list in
  let hide = Hashtbl.create 8 and show = Hashtbl.create 8 in
    Array.iteri
      (fun j s ->
        Hashtbl.replace hide s (placeholder j);
        Hashtbl.replace show (placeholder j) s
      )
      inherited;
    let env' =
      map_tbl Fun.id (Expr.Expr.relabel ~relab:(Hashtbl.find_opt hide)) env
    in
    let events = Interpret.create_events ~ubopt defacto in
    let t0 = now () in
    let s = Interpret.interpret_statements stmts env' [] events in
    let t1 = now () in
    let labels = Alloc.next_label events.alloc in
    let greek = handed_out Alloc.next_greek events.alloc in
    let zh = handed_out Alloc.next_zh events.alloc in
    let local_g = names Alloc.next_greek greek
    and local_z = names Alloc.next_zh zh
    and global_g = names Alloc.next_greek (cur.g + greek)
    and global_z = names Alloc.next_zh (cur.z + zh) in
    let relab_tbl = Hashtbl.copy show in
      Array.iteri
        (fun k n -> Hashtbl.replace relab_tbl n global_g.(cur.g + k))
        local_g;
      Array.iteri
        (fun k n -> Hashtbl.replace relab_tbl n global_z.(cur.z + k))
        local_z;
      let t2 = now () in
      let structure =
        relabel ~off:cur.off ~relab:(Hashtbl.find_opt relab_tbl) ?thread s
      in
      let t3 = now () in
        {
          structure;
          labels;
          greek;
          zh;
          globals = USet.values events.globals;
          t_interpret = t1 -. t0;
          t_relabel = t3 -. t2;
        }

let advance (cur : cursor) (f : fragment) =
  { off = cur.off + f.labels; g = cur.g + f.greek; z = cur.z + f.zh }

(** {1 Rendering, for comparison} *)

let sorted_set show u = USet.values u |> List.map show |> List.sort compare
let pair_s (a, b) = Printf.sprintf "(%d,%d)" a b
let exprs_s es = String.concat " && " (List.map Expr.Expr.to_string es)

let env_s env =
  Hashtbl.fold (fun k v acc -> (k ^ "->" ^ Expr.Expr.to_string v) :: acc) env []
  |> List.sort compare
  |> String.concat ","

let tbl_s show_k show_v tbl =
  Hashtbl.fold (fun k v acc -> (show_k k ^ ": " ^ show_v v) :: acc) tbl []
  |> List.sort compare

(* Every field but [constraints], one entry per field. *)
let render (s : symbolic_event_structure) : (string * string list) list =
  let ints = sorted_set string_of_int and pairs = sorted_set pair_s in
  let i = string_of_int in
    [
      ("e", ints s.e);
      ("events", tbl_s i show_event s.events);
      ("po", pairs s.po);
      ("po_iter", pairs s.po_iter);
      ( "rmw",
        sorted_set
          (fun (a, c, b) ->
            Printf.sprintf "(%d,%s,%d)" a (Expr.Expr.to_string c) b
          )
          s.rmw
      );
      ("lo", pairs s.lo);
      ("restrict", tbl_s i exprs_s s.restrict);
      ("defacto", tbl_s i exprs_s s.defacto);
      ("fj", pairs s.fj);
      ("p", tbl_s i env_s s.p);
      ("conflict", pairs s.conflict);
      ("origin", tbl_s Fun.id i s.origin);
      ( "loop_indices",
        tbl_s i (fun ls -> String.concat ";" (List.map i ls)) s.loop_indices
      );
      ("thread_index", tbl_s i i s.thread_index);
      ("write_events", ints s.write_events);
      ("read_events", ints s.read_events);
      ("rlx_write_events", ints s.rlx_write_events);
      ("rlx_read_events", ints s.rlx_read_events);
      ("fence_events", ints s.fence_events);
      ("branch_events", ints s.branch_events);
      ("malloc_events", ints s.malloc_events);
      ("free_events", ints s.free_events);
      ("terminal_events", ints s.terminal_events);
    ]

let constraint_set (s : symbolic_event_structure) =
  List.map Expr.Expr.to_string s.constraints |> List.sort_uniq compare

(* The constraints a terminal structure is given, from everything the whole
   program declares: globals pairwise distinct, allocations pairwise distinct
   and distinct from every global (interpret.ml, make_generic_terminal_structure).
*)
let program_constraints globals (s : symbolic_event_structure) =
  let globals = List.sort_uniq compare globals in
  let rec pairs = function
    | [] -> []
    | x :: rest -> List.map (fun y -> (x, y)) rest @ pairs rest
  in
  let locations =
    Hashtbl.fold
      (fun _ (ev : event) acc ->
        match (ev.typ, ev.loc) with
        | Malloc, Some loc -> loc :: acc
        | _ -> acc
      )
      s.events []
    |> List.sort_uniq Expr.Expr.compare
  in
    List.map
      (fun (a, b) -> Expr.Expr.binop (EVar a) "!=" (EVar b))
      (pairs globals)
    @ List.concat_map
        (fun loc ->
          List.map (fun g -> Expr.Expr.binop loc "!=" (EVar g)) globals
        )
        locations
    @ List.map (fun (a, b) -> Expr.Expr.binop a "!=" b) (pairs locations)
    |> List.map Expr.Expr.to_string
    |> List.sort_uniq compare

(** {1 One program} *)

type outcome = {
  file : string;
  events : int;
  fragments : int;
  differing : string list;  (** Fields that differ from classic. *)
  constraints_local : bool;  (** Union of fragments' constraints = classic's. *)
  constraints_global : bool;  (** Recomputed over the whole = classic's. *)
  t_classic : float;
  t_fragments : float;
  t_relabel : float;
  t_compose : float;
}

let run file : (outcome, string) result =
  let options =
    {
      Context.default_options with
      allow_unknown_model = true;
      loop_semantics = Generic;
    }
  in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "s1";
    ctx.litmus <- Some (read_file file);
    let ctx = Lwt_main.run (Lwt.return ctx |> Parse.step_parse_litmus) in
    let stmts = Option.get ctx.program_stmts in
    let defacto = Option.value ctx.litmus_defacto ~default:[] in
    let ubopt = ctx.options.ubopt in
      match shape_of stmts with
      | Error why -> Error why
      | Ok { prefix; threads; rest } ->
          (* Classic: the whole program, one events_t. *)
          let t0 = now () in
          let classic, _ =
            Interpret.interpret ~ubopt ~defacto:(Some defacto) stmts
          in
          let t_classic = now () -. t0 in
          (* Fragments. Label 0 is Init's. *)
          let env0 : (string, expr) Hashtbl.t = Hashtbl.create 8 in
          let cur = { off = 1; g = 0; z = 0 } in
          let pre = fragment ~ubopt ~defacto cur env0 prefix in
          (* The prefix is a chain ending in the terminal it was given for
             being interpreted alone; that terminal's label is the last one,
             and its environment is the one the block is entered with. *)
          let pre_terminal = cur.off + pre.labels - 1 in
          let env = Hashtbl.find pre.structure.p pre_terminal in
          let pre = { pre with labels = pre.labels - 1 } in
          let pre_structure = without pre.structure pre_terminal in
          let cur = advance cur pre in
          let cur, thread_fragments =
            List.fold_left
              (fun (cur, acc) body ->
                let thread = List.length acc + 1 in
                let f = fragment ~ubopt ~defacto ~thread cur env body in
                  (advance cur f, f :: acc)
              )
              (cur, []) threads
          in
          let thread_fragments = List.rev thread_fragments in
          let cont =
            if rest = [] then None
            else Some (fragment ~ubopt ~defacto cur env rest)
          in
          let t0 = now () in
          let block =
            List.fold_left
              (fun acc (f : fragment) -> SES.cross acc f.structure)
              (SES.create ()) thread_fragments
          in
          let block =
            match cont with
            | None -> block
            | Some f -> SES.seq block f.structure
          in
          (* A chain before [block]: what prefixing its events one by one with
             [dot] comes to. *)
          let body =
            let c = SES.cross pre_structure block in
              {
                c with
                po = USet.union c.po (URelation.cross pre_structure.e block.e);
              }
          in
          let init = { (Events.Event.create Init 4 ()) with label = 0 } in
          let composed =
            SES.dot ~env:(Hashtbl.create 0) init body []
              (List.map (Expr.Expr.evaluate ~env:(fun _ -> None)) defacto)
          in
          let t_compose = now () -. t0 in
          let all = (pre :: thread_fragments) @ Option.to_list cont in
          let differing =
            List.filter_map
              (fun ((name, a), (_, b)) -> if a = b then None else Some name)
              (List.combine (render classic) (render composed))
          in
            if Sys.getenv_opt "S1_SHOW" <> None then
              List.iter
                (fun ((name, x), (_, y)) ->
                  if x <> y then begin
                    List.iter
                      (fun l ->
                        if not (List.mem l y) then
                          Printf.printf "  classic  %s: %s\n" name l
                      )
                      x;
                    List.iter
                      (fun l ->
                        if not (List.mem l x) then
                          Printf.printf "  composed %s: %s\n" name l
                      )
                      y
                  end
                )
                (List.combine (render classic) (render composed));
            if Sys.getenv_opt "S1_SHOW" <> None then
              Printf.printf "  recomputed constraints: %s\n"
                (String.concat "; "
                   (program_constraints
                      (List.concat_map (fun (f : fragment) -> f.globals) all)
                      composed
                   )
                );
            if Sys.getenv_opt "S1_SHOW" <> None then begin
              Printf.printf "  classic  constraints: %s\n"
                (String.concat "; " (constraint_set classic));
              Printf.printf "  composed constraints: %s\n"
                (String.concat "; " (constraint_set composed))
            end;
            let globals =
              List.concat_map (fun (f : fragment) -> f.globals) all
            in
              Ok
                {
                  file;
                  events = USet.size classic.e;
                  fragments = List.length all;
                  differing;
                  constraints_local =
                    constraint_set composed = constraint_set classic;
                  constraints_global =
                    program_constraints globals composed
                    = constraint_set classic;
                  t_classic;
                  t_fragments =
                    List.fold_left
                      (fun a (f : fragment) -> a +. f.t_interpret)
                      0. all;
                  t_relabel =
                    List.fold_left
                      (fun a (f : fragment) -> a +. f.t_relabel)
                      0. all;
                  t_compose;
                }

(** {1 Cost at realistic sizes}

    The litmus tests are small, and with loops left uninterpreted so are the
    programs. For the cost of relabelling at the sizes MoRDor actually reaches,
    take the structure the pipeline builds for a program with its loops
    unrolled, and relabel all of it: every label shifted, every symbol renamed.
*)
let cost file =
  let options = { Context.default_options with allow_unknown_model = true } in
  let ctx = Context.make_context_with_model options () in
    ctx.litmus_name <- "s1";
    ctx.litmus <- Some (read_file file);
    let ctx = Lwt_main.run (Lwt.return ctx |> Parse.step_parse_litmus) in
    let t0 = now () in
    let ctx = Lwt_main.run (Lwt.return ctx |> Interpret.step_interpret) in
    let t_interpret = now () -. t0 in
    let s = Option.get ctx.structure in
    let renaming = Hashtbl.create 64 in
      Hashtbl.iter
        (fun sym _ -> Hashtbl.replace renaming sym (sym ^ "9"))
        s.origin;
      let t0 = now () in
      let runs = 20 in
        for _ = 1 to runs do
          ignore (relabel ~off:100_000 ~relab:(Hashtbl.find_opt renaming) s)
        done;
        if Sys.getenv_opt "S1_SHOW" <> None then
          Printf.printf "  mallocs %d; constraints: %s\n"
            (USet.size s.malloc_events)
            (String.concat "; " (constraint_set s));
        let t_relabel = (now () -. t0) /. float_of_int runs in
        (* How much of that is the environments: one table per event, one
           expression per register, each put through Expr.relabel. *)
        let t0 = now () in
        let ex = Expr.Expr.relabel ~relab:(Hashtbl.find_opt renaming) in
          for _ = 1 to runs do
            ignore (map_tbl Fun.id (map_tbl Fun.id ex) s.p)
          done;
          let t_envs = (now () -. t0) /. float_of_int runs in
          let time_pairs name rel =
            let t0 = now () in
              for _ = 1 to runs do
                ignore (USet.map (fun (a, b) -> (a + 100_000, b + 100_000)) rel)
              done;
              Printf.printf "    of which %-12s: %.4fs (%d pairs)\n" name
                ((now () -. t0) /. float_of_int runs)
                (USet.size rel)
          in
            time_pairs "po" s.po;
            time_pairs "conflict" s.conflict;
            Printf.printf "    of which environments: %.4fs (%d bindings)\n"
              t_envs
              (Hashtbl.fold (fun _ env n -> n + Hashtbl.length env) s.p 0);
            Printf.printf
              "  %-40s %5d events %4d symbols %6d po: interpret %.4fs, relabel \
               %.4fs (%.1f%%)\n"
              file (USet.size s.e) (Hashtbl.length s.origin) (USet.size s.po)
              t_interpret t_relabel
              (100. *. t_relabel /. t_interpret)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
    if List.mem "--cost" args then begin
      List.iter cost (List.filter (fun a -> a <> "--cost") args);
      exit 0
    end;
    let verbose = List.mem "-v" args in
    let roots = List.filter (fun a -> a <> "-v") args in
    let roots =
      if roots = [] then
        [ "litmus-tests"; "litmus-tests-promising"; "litmus-tests-review" ]
      else roots
    in
    let files = List.concat_map lit_files roots in
    let skipped = Hashtbl.create 8 and errors = ref [] and ran = ref [] in
      List.iter
        (fun file ->
          match
            try run file with e -> Error ("ERROR " ^ Printexc.to_string e)
          with
          | Ok o -> ran := o :: !ran
          | Error why when String.length why > 5 && String.sub why 0 5 = "ERROR"
            -> errors := (file, why) :: !errors
          | Error why ->
              Hashtbl.replace skipped why
                (1 + Option.value (Hashtbl.find_opt skipped why) ~default:0)
        )
        files;
      let ran = List.rev !ran in
      let identical = List.filter (fun o -> o.differing = []) ran in
        Printf.printf "files                         : %d\n" (List.length files);
        Hashtbl.iter (Printf.printf "  skipped, %-20s : %d\n") skipped;
        Printf.printf "  errors                      : %d\n"
          (List.length !errors);
        Printf.printf "compared                      : %d\n" (List.length ran);
        Printf.printf "  identical, labels and all   : %d\n"
          (List.length identical);
        Printf.printf "  constraints, fragment union : %d equal\n"
          (List.length (List.filter (fun o -> o.constraints_local) ran));
        Printf.printf "  constraints, recomputed     : %d equal\n"
          (List.length (List.filter (fun o -> o.constraints_global) ran));
        List.iter
          (fun o ->
            if o.differing <> [] then
              Printf.printf "DIFF %s: %s\n" o.file
                (String.concat ", " o.differing)
          )
          ran;
        List.iter (fun (f, why) -> Printf.printf "%s: %s\n" f why) !errors;
        let sum f = List.fold_left (fun a o -> a +. f o) 0. ran in
          Printf.printf
            "time, all compared: classic %.3fs, fragments %.3fs, relabel \
             %.3fs, compose %.3fs\n"
            (sum (fun o -> o.t_classic))
            (sum (fun o -> o.t_fragments))
            (sum (fun o -> o.t_relabel))
            (sum (fun o -> o.t_compose));
          Printf.printf "largest:\n";
          List.sort (fun a b -> compare b.events a.events) ran
          |> List.filteri (fun i _ -> i < 8)
          |> List.iter (fun o ->
              Printf.printf
                "  %-52s %5d events %d fragments: classic %.4fs, fragments \
                 %.4fs, relabel %.4fs, compose %.4fs\n"
                o.file o.events o.fragments o.t_classic o.t_fragments
                o.t_relabel o.t_compose
          );
          if verbose then
            List.iter
              (fun o ->
                Printf.printf "%s,%d,%d,%b,%b,%b,%.5f,%.5f,%.5f,%.5f\n" o.file
                  o.events o.fragments (o.differing = []) o.constraints_local
                  o.constraints_global o.t_classic o.t_fragments o.t_relabel
                  o.t_compose
              )
              ran
