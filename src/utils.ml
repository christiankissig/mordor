(** Relation utilities *)

open Uset

(** Project first elements from relation *)
let pi_1 rel = USet.map (fun (x, _) -> x) rel

(** Project second elements from relation *)
let pi_2 rel = USet.map (fun (_, y) -> y) rel
