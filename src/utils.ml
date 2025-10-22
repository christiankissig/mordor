(** Relation utilities *)

(** Project first elements from relation *)
let pi_1 rel = Uset.map (fun (x, _) -> x) rel

(** Project second elements from relation *)
let pi_2 rel = Uset.map (fun (_, y) -> y) rel
