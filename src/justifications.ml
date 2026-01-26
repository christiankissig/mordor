(** Justification operations and caching.

    This module provides operations on justifications, which represent
    conditions under which write events can be executed in a symbolic event
    structure. A justification includes predicates (path conditions), symbols
    (data dependencies), forwarding edges, and write-exclusion edges that
    together justify why a write event can occur and what value it produces. *)

open Types
open Expr
open Uset
open Events

(** {1 Justification Operations} *)

(** Operations on justifications.

    Provides comparison, hashing, string conversion, and analysis operations
    needed for working with justifications throughout the elaboration process.
*)
module Justification : sig
  (** The justification type. *)
  type t = justification

  (** [to_string just] converts justification to human-readable string.

      Format: [{predicates}, {symbols} ⊢({fwd},{we}) event]

      @param just The justification to convert.
      @return String representation showing all components. *)
  val to_string : justification -> string

  (** [equal j1 j2] tests justification equality.

      Two justifications are equal if they have the same write event, forwarding
      edges, write-exclusion edges, symbols, and predicates.

      @param j1 First justification.
      @param j2 Second justification.
      @return [true] if justifications are equal. *)
  val equal : justification -> justification -> bool

  (** [hash j] computes hash value for justification.

      Hash is based on all justification components for use in hash tables.

      @param j The justification to hash.
      @return Hash value. *)
  val hash : justification -> int

  (** [get_symbols just] extracts all symbols used in justification.

      Collects symbols from predicates, the symbol set D, and the write event.

      @param just The justification.
      @return Set of all symbols appearing in the justification. *)
  val get_symbols : justification -> string uset

  (** [covers j_y ppo_y j_x ppo_x] tests if [j_y] covers [j_x].

      Justification [j_y] covers [j_x] if they justify the same write with the
      same forwarding context, but [j_y] has strictly fewer (more general)
      predicates. Covered justifications are redundant and can be filtered out.

      @param j_y Potentially covering justification.
      @param ppo_y PPO relation for [j_y].
      @param j_x Potentially covered justification.
      @param ppo_x PPO relation for [j_x].
      @return [true] if [j_y] covers [j_x]. *)
  val covers : justification -> justification -> bool

  (** [relabel ~relab just] relabels symbols in justification.

      Applies symbol substitution to predicates, symbol set, and write event.
      Used during lifting elaboration to match justifications from different
      paths.

      @param relab Function mapping symbols to their replacements.
      @param just The justification to relabel.
      @return New justification with relabeled symbols. *)
  val relabel :
    relab:(string -> string option) -> justification -> justification
end = struct
  type t = justification

  let to_string (just : justification) : string =
    Printf.sprintf "{%s}, {%s} ⊢({%s},{%s}) %s"
      (String.concat "," (List.map Expr.to_string just.p))
      (String.concat "," (USet.values just.d))
      (String.concat ","
         (List.map
            (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
            (USet.values just.fwd)
         )
      )
      (String.concat ","
         (List.map
            (fun (e1, e2) -> Printf.sprintf "(%d,%d)" e1 e2)
            (USet.values just.we)
         )
      )
      (Event.to_string just.w)

  let equal j1 j2 =
    let result =
      j1.w = j2.w
      && USet.equal j1.fwd j2.fwd
      && USet.equal j1.we j2.we
      && USet.equal j1.d j2.d
      && List.equal Expr.equal j1.p j2.p
    in
      result

  let hash j =
    let compare_pairs =
     fun (a1, b1) (a2, b2) ->
      let c = compare a1 a2 in
        if c <> 0 then c else compare b1 b2
    in
    let result =
      Hashtbl.hash
        ( j.w,
          USet.to_list j.fwd |> List.sort compare_pairs,
          USet.to_list j.we |> List.sort compare_pairs,
          USet.to_list j.d |> List.sort String.compare,
          List.map hash_expr j.p
        )
    in
      result

  let get_symbols (just : justification) : string uset =
    let symbols = USet.create () in
      USet.inplace_union symbols just.d |> ignore;
      List.map Expr.get_symbols just.p
      |> List.flatten
      |> USet.of_list
      |> USet.inplace_union symbols
      |> ignore;
      USet.inplace_union symbols (Event.get_symbols just.w) |> ignore;
      symbols

  let relabel ~(relab : string -> string option) (just : justification) :
      justification =
    {
      p = List.map (Expr.relabel ~relab) just.p;
      d =
        USet.map
          (fun s ->
            match relab s with
            | Some s' -> s'
            | None -> s
          )
          just.d;
      we = USet.clone just.we;
      fwd = USet.clone just.fwd;
      w = Event.relabel ~relab just.w;
    }

  let covers (just_y : justification) (just_x : justification) : bool =
    just_x.w.label = just_y.w.label
    && Option.equal Expr.equal just_x.w.loc just_y.w.loc
    && Option.equal Expr.equal just_x.w.wval just_y.w.wval
    && USet.equal just_x.fwd just_y.fwd
    && USet.equal just_x.we just_y.we
    && List.length just_y.p < List.length just_x.p
    (* TODO use that just.p are ordered *)
    && List.for_all
         (fun e -> List.exists (fun e' -> Expr.equal e e') just_x.p)
         just_y.p
  (* TODO too strict! ppo is a function of fwd, we, and p, which we
     test above. Less p seems to mean less ppo. Can this be removed altogether? *)
  (* && USet.equal ppo_x ppo_y *)
end

(** {1 Justification Caching} *)

(** Cache key type for single justifications.

    Implements equality and hashing for use in [Hashtbl.Make]. *)
module JustificationCacheKey = struct
  (** The key type is a justification. *)
  type t = justification

  (** Equality based on [Justification.equal]. *)
  let equal = Justification.equal

  (** Hash based on [Justification.hash]. *)
  let hash = Justification.hash
end

(** Hash table keyed by justifications.

    Used to cache operations on individual justifications, such as tracking
    which justifications have been processed during forwarding. *)
module JustificationCache = Hashtbl.Make (JustificationCacheKey)

(** [deduplicate_justification_list justs] removes duplicate justifications.

    Filters the list to keep only the first occurrence of each unique
    justification according to structural equality.

    @param justs List of justifications potentially containing duplicates.
    @return List with duplicates removed, preserving first occurrence order. *)
let deduplicate_justification_list (justs : justification list) :
    justification list =
  let seen = JustificationCache.create (List.length justs) in
    List.filter
      (fun j ->
        if JustificationCache.mem seen j then false
        else (
          JustificationCache.add seen j ();
          true
        )
      )
      justs

(** {1 Justification Pair Caching} *)

(** Cache key type for justification pairs.

    Used for caching operations on pairs of justifications, such as lifting
    elaboration results. *)
module JustificationPairCacheKey = struct
  (** The key type is a pair of justifications. *)
  type t = justification * justification

  (** [equal (j1a, j1b) (j2a, j2b)] tests pair equality.

      Two pairs are equal if both components are equal according to
      [Justification.equal].

      @param j1a First component of first pair.
      @param j1b Second component of first pair.
      @param j2a First component of second pair.
      @param j2b Second component of second pair.
      @return [true] if pairs are equal. *)
  let equal (j1a, j1b) (j2a, j2b) =
    Justification.equal j1a j2a && Justification.equal j1b j2b

  (** [hash (j1, j2)] computes hash for justification pair.

      Combines hashes of both justifications.

      @param j1 First justification.
      @param j2 Second justification.
      @return Hash value for the pair. *)
  let hash (j1, j2) = Hashtbl.hash (Justification.hash j1, Justification.hash j2)
end

(** Hash table keyed by justification pairs.

    Used to cache operations on pairs of justifications, such as lifting
    elaboration which processes all pairs in the cross product. *)
module JustificationPairCache = Hashtbl.Make (JustificationPairCacheKey)
