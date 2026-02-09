open Events
open Expr
open Lwt.Syntax
open Types
open Uset

module SymbolicEventStructure = struct
  type t = symbolic_event_structure

  let create () : t =
    {
      e = USet.create ();
      events = Hashtbl.create 16;
      po = USet.create ();
      po_iter = USet.create ();
      rmw = USet.create ();
      lo = USet.create ();
      restrict = Hashtbl.create 16;
      defacto = Hashtbl.create 16;
      fj = USet.create ();
      p = Hashtbl.create 16;
      constraints = [];
      conflict = USet.create ();
      origin = Hashtbl.create 16;
      loop_indices = Hashtbl.create 16;
      thread_index = Hashtbl.create 16;
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
      terminal_events = USet.create ();
    }

  let dot (event : event) structure phi defacto : symbolic_event_structure =
    if List.exists (fun p -> p = EBoolean false) phi then
      Logs.warn (fun m ->
          m "Adding event %d under unsatisfiable path condition.\n" event.label
      );
    Hashtbl.replace structure.restrict event.label phi;
    Hashtbl.replace structure.defacto event.label defacto;
    {
      e = USet.union structure.e (USet.singleton event.label);
      events = structure.events;
      po =
        USet.union structure.po
          (USet.map (fun e -> (event.label, e)) structure.e);
      po_iter = USet.create ();
      rmw = structure.rmw;
      lo = structure.lo;
      restrict = structure.restrict;
      defacto = structure.defacto;
      fj = structure.fj;
      p = structure.p;
      constraints = structure.constraints;
      conflict = structure.conflict;
      origin = structure.origin;
      loop_indices = structure.loop_indices;
      thread_index = structure.thread_index;
      write_events =
        ( if event.typ = Write then
            USet.union structure.write_events (USet.singleton event.label)
          else structure.write_events
        );
      read_events =
        ( if event.typ = Read then
            USet.union structure.read_events (USet.singleton event.label)
          else structure.read_events
        );
      rlx_write_events =
        ( if event.typ = Write && event.wmod = Relaxed then
            USet.union structure.rlx_write_events (USet.singleton event.label)
          else structure.rlx_write_events
        );
      rlx_read_events =
        ( if event.typ = Read && event.rmod = Relaxed then
            USet.union structure.rlx_read_events (USet.singleton event.label)
          else structure.rlx_read_events
        );
      fence_events =
        ( if event.typ = Fence then
            USet.union structure.fence_events (USet.singleton event.label)
          else structure.fence_events
        );
      branch_events =
        ( if event.typ = Branch then
            USet.union structure.branch_events (USet.singleton event.label)
          else structure.branch_events
        );
      malloc_events =
        ( if event.typ = Malloc then
            USet.union structure.malloc_events (USet.singleton event.label)
          else structure.malloc_events
        );
      free_events =
        ( if event.typ = Free then
            USet.union structure.free_events (USet.singleton event.label)
          else structure.free_events
        );
      terminal_events =
        ( if event.typ = Terminal then
            USet.union structure.terminal_events (USet.singleton event.label)
          else structure.terminal_events
        );
    }

  let plus a b : t =
    let restrict = Hashtbl.copy a.restrict in
      Hashtbl.iter (fun k v -> Hashtbl.replace restrict k v) b.restrict;
      let defacto = Hashtbl.copy a.defacto in
        Hashtbl.iter (fun k v -> Hashtbl.replace defacto k v) b.defacto;
        {
          e = USet.union a.e b.e;
          events = a.events;
          (* a and b share the same events table *)
          po = USet.union a.po b.po;
          po_iter = USet.create ();
          rmw = USet.union a.rmw b.rmw;
          lo = USet.union a.lo b.lo;
          restrict;
          defacto;
          fj = USet.union a.fj b.fj;
          p = Hashtbl.create 0;
          (* TODO value not needed here *)
          constraints = a.constraints @ b.constraints;
          conflict =
            USet.union a.conflict b.conflict
            |> USet.inplace_union (URelation.cross a.e b.e)
            |> USet.inplace_union (URelation.cross b.e a.e);
          (* a and b share the same origin table *)
          origin = a.origin;
          loop_indices = a.loop_indices;
          thread_index = a.thread_index;
          write_events = USet.union a.write_events b.write_events;
          read_events = USet.union a.read_events b.read_events;
          rlx_write_events = USet.union a.rlx_write_events b.rlx_write_events;
          rlx_read_events = USet.union a.rlx_read_events b.rlx_read_events;
          fence_events = USet.union a.fence_events b.fence_events;
          branch_events = USet.union a.branch_events b.branch_events;
          malloc_events = USet.union a.malloc_events b.malloc_events;
          free_events = USet.union a.free_events b.free_events;
          terminal_events = USet.union a.terminal_events b.terminal_events;
        }

  let cross a b : t =
    let restrict = Hashtbl.copy a.restrict in
      Hashtbl.iter (fun k v -> Hashtbl.replace restrict k v) b.restrict;
      let defacto = Hashtbl.copy a.defacto in
        Hashtbl.iter (fun k v -> Hashtbl.replace defacto k v) b.defacto;
        {
          e = USet.union a.e b.e;
          events = a.events;
          (* a and b share the same events table *)
          po = USet.union a.po b.po;
          po_iter = USet.create ();
          rmw = USet.union a.rmw b.rmw;
          lo = USet.union a.lo b.lo;
          restrict;
          defacto;
          fj = USet.union a.fj b.fj;
          p = Hashtbl.create 0;
          (* TODO value not needed here *)
          constraints = a.constraints @ b.constraints;
          conflict = USet.union a.conflict b.conflict;
          (* a and b share the same origin table *)
          origin = a.origin;
          loop_indices = a.loop_indices;
          thread_index = a.thread_index;
          write_events = USet.union a.write_events b.write_events;
          read_events = USet.union a.read_events b.read_events;
          rlx_write_events = USet.union a.rlx_write_events b.rlx_write_events;
          rlx_read_events = USet.union a.rlx_read_events b.rlx_read_events;
          fence_events = USet.union a.fence_events b.fence_events;
          branch_events = USet.union a.branch_events b.branch_events;
          malloc_events = USet.union a.malloc_events b.malloc_events;
          free_events = USet.union a.free_events b.free_events;
          terminal_events = USet.union a.terminal_events b.terminal_events;
        }

  let events_in_loop structure loop_id =
    Hashtbl.fold
      (fun event loop_indices acc ->
        if List.mem loop_id loop_indices then USet.add acc event else acc
      )
      structure.loop_indices (USet.create ())

  let events_po_before structure event =
    USet.filter (fun (e1, e2) -> e2 = event) structure.po |> URelation.pi_1
end

(* Find the origin of a symbol in a symbolic event structure *)
let origin structure (s : string) = Hashtbl.find_opt structure.origin s

(** Path type *)
type path_info = {
  path : int uset;
  p : expr list; (* List of predicate lists, serves as conjunction *)
}

(** Generate all paths through the control flow structure *)
let rec cartesian = function
  | [] -> [ [] ]
  | hd :: tl ->
      List.concat_map (fun x -> List.map (List.cons x) (cartesian tl)) hd

(** Generate maximal conflict-free sets of events as paths through the symbolic
    event structure. *)
let generate_max_conflictfree_sets (structure : symbolic_event_structure) =
  let e = USet.set_minus structure.e structure.branch_events in
  let po = USet.intersection structure.po (URelation.cross e e) in
  let po_intransitive = URelation.transitive_reduction po in
  let po_tree = URelation.adjacency_map po_intransitive in

  (*Partition neighbours into groups where each group is mutually in conflict *)
  let partition_by_conflict neighbours conflict =
    let neighbours_list = USet.values neighbours in

    (* Helper: find all neighbours in the same conflict group as 'seed' *)
    let rec find_conflict_group seed remaining acc =
      match remaining with
      | [] -> (acc, [])
      | n :: rest ->
          (* Check if n conflicts with all members of acc (including seed) *)
          let conflicts_with_all =
            List.for_all
              (fun member ->
                USet.mem conflict (member, n)
                || USet.mem conflict (n, member)
                || member = n
              )
              (seed :: acc)
          in
            if conflicts_with_all then find_conflict_group seed rest (n :: acc)
            else
              let group, remaining' = find_conflict_group seed rest acc in
                (group, n :: remaining')
    in

    (* Partition all neighbours into conflict groups *)
    let rec partition remaining groups =
      match remaining with
      | [] -> groups
      | seed :: rest ->
          let group, remaining' = find_conflict_group seed rest [ seed ] in
            partition remaining' (group :: groups)
    in

    partition neighbours_list []
  in

  (* DFS search for all paths. Each path is a uset event IDs. Search produces
     list of paths such paths. *)
  let rec dfs current =
    let neighbours =
      Hashtbl.find_opt po_tree current |> Option.value ~default:(USet.create ())
    in
      if USet.size neighbours == 0 then
        (* leaf node *)
        [ USet.singleton current ]
      else if USet.size neighbours == 1 then
        (* one neighbour; continue down that path *)
        let next = USet.values neighbours |> List.hd in
          dfs next |> List.map (fun path -> USet.add path current)
      else if
        USet.subset
          (USet.set_minus
             (URelation.cross neighbours neighbours)
             (URelation.identity neighbours)
          )
          structure.conflict
      then
        (* neighbour branches are in conflict; disjoint union *)
        USet.values neighbours
        |> List.map dfs
        |> List.flatten
        |> List.map (fun path -> USet.add path current)
      else
        (* Multiple neighbours: partition by conflict *)
        let conflict_groups =
          partition_by_conflict neighbours structure.conflict
        in

        (* For each conflict group, choose one alternative (disjoint union) *)
        (* Across groups, take all combinations (cartesian product) *)
        conflict_groups
        |> List.map (fun group ->
            (* Within this conflict group, just flatten (disjoint union) *)
            List.map dfs group |> List.flatten
        )
        |> cartesian
        |> List.map (fun paths ->
            List.fold_left
              (fun acc path -> USet.union acc path)
              (USet.singleton current) paths
        )
  in

  (* Find root events (events with no predecessors in po) *)
  let roots =
    let all_events = structure.e in
    let has_predecessor = URelation.pi_2 structure.po in
      USet.set_minus all_events has_predecessor
  in

  Logs.debug (fun m ->
      m "Generating paths from roots: %s"
        (String.concat ", " (USet.values (USet.map (Printf.sprintf "%d") roots)))
  );

  (* Generate p from value restrictions along path and compose path_info. TODO
     need to filter paths by satisfiability? *)
  let paths =
    USet.values roots
    |> List.map dfs
    |> List.flatten
    |> List.map (fun path ->
        let p =
          USet.values path
          |> List.map (fun e ->
              Hashtbl.find_opt structure.restrict e |> Option.value ~default:[]
          )
          |> List.flatten
          |> USet.of_list
          |> USet.values
        in
          { path; p }
    )
  in
    Logs.debug (fun m ->
        m "Generated %d paths through the control flow" (List.length paths)
    );
    paths

(* Check if write w is downward-closed same-location write before read r. This
   prevents r reading from shadowed writes w.*)
(* TODO optimize *)
let dslwb structure w r =
  let landmark = Landmark.register "dslwb" in
    Landmark.enter landmark;
    let write_events = structure.write_events in
    let r_restrict =
      Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
    in
      let* result =
        USet.async_exists
          (fun (w2, r2) ->
            if
              r2 = r (* w2 po bfore r *)
              && w2 <> w (* w2 is not w *)
              && USet.mem write_events w2 (* w2 is a write *)
              && USet.mem structure.po (w, w2)
              (* w2 po after w, thus in between w and r *)
            then
              (* w2 potentially shadows w *)
              (* TODO use semantic equivalence relative to valres *)
              match (get_loc structure w, get_loc structure w2) with
              | Some loc, Some loc2 -> Solver.exeq ~state:r_restrict loc loc2
              | _ -> Lwt.return false
            else Lwt.return false
          )
          structure.po
      in
        Landmark.exit landmark;
        Lwt.return result

let init_ppo structure =
  let events = structure.events in
  let po = structure.po in
  let init_ppo =
    if Hashtbl.mem events 0 then USet.filter (fun (f, t) -> f <> t && f = 0) po
    else USet.create ()
  in
  let terminal_events =
    Hashtbl.fold
      (fun lbl ev acc -> if ev.typ = Terminal then USet.add acc lbl else acc)
      structure.events (USet.create ())
  in
  let terminal_ppo =
    USet.filter (fun (f, t) -> f <> t && USet.mem terminal_events t) po
  in
  (* TODO discern in subsequent computation *)
  let init_ppo = USet.union init_ppo terminal_ppo in
    init_ppo

(* TODO accomodate indexing po_iter by loop indices *)
let symbols_in_loop structure e =
  let e_loops =
    Hashtbl.find_opt structure.loop_indices e
    |> Option.value ~default:[]
    |> USet.of_list
  in
  let evt = Hashtbl.find structure.events e in
  let symbols =
    (Option.map Expr.get_symbols evt.loc |> Option.value ~default:[])
    @ (Option.map Value.get_symbols evt.rval |> Option.value ~default:[])
    @ (Option.map Expr.get_symbols evt.wval |> Option.value ~default:[])
    |> USet.of_list
    |> USet.filter (fun s ->
        let o_loops =
          Hashtbl.find structure.origin s
          |> Hashtbl.find_opt structure.loop_indices
          |> Option.value ~default:[]
          |> USet.of_list
        in
          USet.size (USet.intersection e_loops o_loops) > 0
    )
  in
    symbols
