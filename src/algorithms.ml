(** Combination and permutation utilities for constraint solving.

    This module provides utilities for generating combinations from maps of
    alternatives, with support for incremental validation and early pruning.
    Used extensively in elaboration algorithms to explore valid combinations of
    symbol relabelings and event orderings. *)

open Lwt.Syntax
open Uset

(** {1 List-Based Combination Builder} *)

(** Combination builder for maps from keys to lists of alternatives.

    Given a hash table mapping keys to lists of values, generates all total
    combinations where each key is paired with one of its associated values.
    Supports incremental validation through partial and final checks to prune
    the search space early.

    Example: Given map
    {[
      {a: [1,2], b: [3,4
    ]}

    and keys

    {[
      [ (a, b) ]
    ]}

    produces

    {[
      [
        ( [ (a, 1); (b, 3) ],
          [ (a, 1); (b, 4) ],
          [ (a, 2); (b, 3) ],
          [ (a, 2); (b, 4) ]
        );
      ]
    ]} *)
module ListMapCombinationBuilder = struct
  (** [build_combinations listmap keys ?check_partial ?check_final ()] generates
      combinations.

      Produces all total combinations of key-value pairs from [listmap] for the
      given [keys]. The result is a list where each element is a complete
      assignment pairing each key with one of its associated values.

      The algorithm builds combinations incrementally, validating partial
      combinations as they are constructed to enable early pruning of invalid
      branches. This is significantly more efficient than generating all
      combinations and then filtering.

      @param listmap Hash table mapping keys to lists of alternative values.
      @param keys List of keys to build combinations for (determines order).
      @param check_partial
        Optional validator for partial combinations. Called as
        [check_partial combo ?alternatives (key, value)] where [combo] is the
        current partial assignment, [alternatives] is the full list of values
        for [key], and [(key, value)] is the binding being added. Returns [true]
        to accept this binding. Default: always accept.
      @param check_final
        Optional validator for complete combinations. Called as
        [check_final combo] where [combo] is a complete assignment. Returns
        [true] to include this combination in results. Default: always accept.
      @return Promise of list of all valid complete combinations.

      Optimizations:
      - Streaming processing: combinations built incrementally rather than all
        at once
      - Filter before extend: invalid partial combinations pruned immediately
      - Efficient list operations: uses cons and rev_append instead of append

      Example:
      {[
        let map = Hashtbl.create 2 in
        Hashtbl.add map "x" [1; 2];
        Hashtbl.add map "y" [3; 4];
        let* combos = ListMapCombinationBuilder.build_combinations
          map ["x"; "y"]
          ~check_partial:(fun combo ?alternatives (k, v) ->
            (* Prune if sum exceeds threshold *)
            let sum = List.fold_left (fun acc (_, n) -> acc + n) v combo in
            Lwt.return (sum <= 5)
          )
          ()
        in
        (* combos = [[("x",1);("y",3)]; [("x",1);("y",4)]; [("x",2);("y",3)]] *)
      ]} *)
  let build_combinations (type a) (type b) (listmap : (a, b list) Hashtbl.t)
      (keys : a list)
      ?(check_partial = fun _ ?alternatives:_ _ -> Lwt.return true)
      ?(check_final = fun _ -> Lwt.return true) () =
    let rec combine_and_check combinations keys =
      match keys with
      | [] -> Lwt_list.filter_s check_final combinations
      | key :: rest_keys ->
          let justs = try Hashtbl.find listmap key with Not_found -> [] in
            (* OPTIMIZATION 1: Process combinations in a streaming fashion *)
            (* Instead of collecting all new_combinations at once, process incrementally *)
            let* new_combinations =
              Lwt_list.fold_left_s
                (fun acc just ->
                  (* OPTIMIZATION 2: Filter first, then extend *)
                  let* filtered =
                    Lwt_list.filter_s
                      (fun combo ->
                        check_partial combo ?alternatives:(Some justs)
                          (key, just)
                      )
                      combinations
                  in
                  (* OPTIMIZATION 3: Use cons (::) instead of append (@) *)
                  (* Reverse the list once at the end instead of maintaining order *)
                  let extended =
                    List.map (fun combo -> (key, just) :: combo) filtered
                  in
                    (* OPTIMIZATION 4: Use rev_append for efficient concatenation *)
                    Lwt.return (List.rev_append extended acc)
                )
                [] justs
            in
              (* Note: Combinations are now in reverse order within each combo *)
              (* If order matters, reverse each combo at the end *)
              combine_and_check new_combinations rest_keys
    in
      let* result = combine_and_check [ [] ] keys in
        (* OPTIMIZATION 5: Reverse each combination to restore original order *)
        Lwt.return (List.map List.rev result)
end

(** {1 USet-Based Combination Builder} *)

(** Combination builder for maps from keys to USets of alternatives.

    Wrapper around {!ListMapCombinationBuilder} that handles conversion between
    USets and lists. Provides the same functionality but works with the USet
    type used throughout the symbolic execution engine. *)
module USetMapCombinationBuilder = struct
  (** [build_combinations usetmap keys ?check_partial ?check_final ()] generates
      combinations.

      Like {!ListMapCombinationBuilder.build_combinations} but operates on USets
      instead of lists. Converts the input map to lists, generates combinations,
      then converts results back to USets.

      @param usetmap Hash table mapping keys to USets of alternative values.
      @param keys List of keys to build combinations for.
      @param check_partial
        Optional validator for partial combinations. See
        {!ListMapCombinationBuilder.build_combinations} for details.
      @param check_final
        Optional validator for complete combinations. See
        {!ListMapCombinationBuilder.build_combinations} for details.
      @return
        Promise of USet of all valid complete combinations (each combo is also a
        USet).

      Example:
      {[
        (* Generate symbol relabelings for lifting *)
        let* relabelings = USetMapCombinationBuilder.build_combinations
          symbol_map
          (USet.values symbols_1)
          ~check_partial:(fun combo ?alternatives (from, to_) ->
            (* Ensure injectivity: no two symbols map to same target *)
            Lwt.return (List.for_all (fun (_, t') -> to_ <> t') combo)
          )
          ()
        in
        (* Each element of relabelings is a USet of (symbol, symbol) pairs *)
      ]} *)
  let build_combinations (type a) (type b) (usetmap : (a, b USet.t) Hashtbl.t)
      (keys : a list)
      ?(check_partial = fun _ ?alternatives:_ _ -> Lwt.return true)
      ?(check_final = fun _ -> Lwt.return true) () =
    let listmap = Hashtbl.create (Hashtbl.length usetmap) in
      Hashtbl.iter
        (fun k uset -> Hashtbl.add listmap k (USet.values uset))
        usetmap;
      ListMapCombinationBuilder.build_combinations listmap keys ~check_partial
        ~check_final ()
      |> Lwt.map USet.of_list
      |> Lwt.map (USet.map USet.of_list)
end

(** {1 Permutation Utilities} *)

(** [permutations lst] generates all permutations of a list.

    Produces all possible orderings of the input list elements. The number of
    permutations is [n!] where [n] is the length of the list, so this should
    only be used on small lists.

    Algorithm: Recursively generates permutations of the tail, then inserts the
    head at all possible positions in each permutation.

    @param lst The list to permute.
    @return List of all permutations, where each permutation is a list.

    Example:
    {[
      permutations [ 1; 2; 3 ]
        (* Returns: [[1;2;3]; [2;1;3]; [2;3;1]; [1;3;2]; [3;1;2]; [3;2;1]] *)
        permutations [] (* Returns: [[]] *)
        permutations [ 42 ]
      (* Returns: [[42]] *)
    ]}

    Complexity: O(n! × n) time, O(n! × n) space where n is list length. *)
let rec permutations = function
  | [] -> [ [] ]
  | x :: xs ->
      let perms = permutations xs in
        List.concat
          (List.map
             (fun perm ->
               let rec insert_at_all_positions acc = function
                 | [] -> [ List.rev (x :: acc) ]
                 | y :: ys as rest ->
                     (List.rev acc @ (x :: rest))
                     :: insert_at_all_positions (y :: acc) ys
               in
                 insert_at_all_positions [] perm
             )
             perms
          )

(** {1 Map Operations} *)

(** Computes the transitive closure of a mapping represented as a hash table.

    Given a hash table mapping keys to values, computes the transitive closure
    such that each key maps directly to its final target after following the
    chain of mappings. Detects cycles and raises an exception if found.

    @param map Hash table representing the initial mapping.
    @return New hash table representing the transitive closure of the mapping.

    Example:
    {[
      let map = Hashtbl.create 3 in
      Hashtbl.add map "a" "b";
      Hashtbl.add map "b" "c";
      Hashtbl.add map "c" "d";
      let closure = map_transitive_closure map;
      (* closure now maps:
         "a" -> "d"
         "b" -> "d"
         "c" -> "d"
      *)
    ]} *)
let map_transitive_closure (map : ('a, 'a) Hashtbl.t) : ('a, 'a) Hashtbl.t =
  let result = Hashtbl.create (Hashtbl.length map) in
  let rec find_root (k : 'a) (visited : 'a USet.t) =
    if USet.mem visited k then None (* Cycle detected *)
    else
      let _ = USet.add visited k in
        (* Mutate visited in-place *)
        match Hashtbl.find_opt map k with
        | None -> Some k (* No further mapping, k is root *)
        | Some v -> find_root v visited (* Pass same (now modified) visited *)
  in
    Hashtbl.iter
      (fun k _ ->
        match find_root k (USet.create ()) with
        | Some root -> Hashtbl.replace result k root
        | None -> failwith "Cycle detected in mapping"
      )
      map;
    result
