open Events
open Types
open Uset

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
  let po_intransitive = URelation.transitive_reduction structure.po in
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
             (URelation.identity_relation neighbours)
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
  let write_events = structure.write_events in
  let r_restrict =
    Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
  in
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
