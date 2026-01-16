open Types
open Expr
open Uset
open Events

module Justification = struct
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
    j1.w = j2.w
    && USet.equal j1.fwd j2.fwd
    && USet.equal j1.we j2.we
    && USet.equal j1.d j2.d
    && List.equal Expr.equal j1.p j2.p

  let hash j =
    let compare_pairs =
     fun (a1, b1) (a2, b2) ->
      let c = compare a1 a2 in
        if c <> 0 then c else compare b1 b2
    in
      Hashtbl.hash
        ( j.w,
          USet.to_list j.fwd |> List.sort compare_pairs,
          USet.to_list j.we |> List.sort compare_pairs,
          USet.to_list j.d |> List.sort String.compare,
          List.map hash_expr j.p
        )
end

module JustificationCacheKey = struct
  type t = justification

  let equal = Justification.equal
  let hash = Justification.hash
end

module JustificationCache = Hashtbl.Make (JustificationCacheKey)

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
