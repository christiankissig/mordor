(** Unordered Set using Core's Hash_set.Poly *)

open Core
open Lwt.Syntax

(** Generic set type using Core's polymorphic Hash_set *)
type 'a t = 'a Hash_set.Poly.t

(** Equality function for values *)
let value_equality a b =
  match (a, b) with
  | x, y when phys_equal x y -> true
  | x, y when Poly.(x = y) -> true
  | _ -> false

(** Create empty set *)
let create () : 'a t = Hash_set.Poly.create ()

(** Create singleton set *)
let singleton x =
  let s = Hash_set.Poly.create () in
    Hash_set.add s x;
    s

(** Create from list *)
let of_list lst = Hash_set.Poly.of_list lst

(** Check membership *)
let mem s x = Hash_set.mem s x

(** Add element (mutates and returns set for chaining) *)
let add s x =
  Hash_set.add s x;
  s

(** Remove element (mutates and returns set for chaining) *)
let remove s x =
  Hash_set.remove s x;
  s

(** Get all values *)
let values s = Hash_set.to_list s

(** Size *)
let size s = Hash_set.length s

(** Clear set (mutates and returns set for chaining) *)
let clear s =
  Hash_set.clear s;
  s

(** Clone set *)
let clone s = Hash_set.copy s

(** Union - creates new set *)
let union s1 s2 = Hash_set.union s1 s2

(** In-place union (mutates s1 and returns it) *)
let inplace_union s1 s2 =
  Hash_set.iter s2 ~f:(fun x -> Hash_set.add s1 x);
  s1

(** Intersection - creates new set *)
let intersection s1 s2 = Hash_set.inter s1 s2

(** Set minus - creates new set *)
let set_minus s1 s2 = Hash_set.diff s1 s2

(** In-place set minus (mutates s1 and returns it) *)
let inplace_set_minus s1 s2 =
  Hash_set.iter s2 ~f:(fun x -> Hash_set.remove s1 x);
  s1

(** Difference (symmetric difference) - creates new set *)
let difference s1 s2 =
  let a = Hash_set.copy s1 in
  let b = Hash_set.copy s2 in
    Hash_set.iter s1 ~f:(fun x -> Hash_set.remove b x);
    Hash_set.iter s2 ~f:(fun x -> Hash_set.remove a x);
    Hash_set.iter b ~f:(fun x -> Hash_set.add a x);
    a

(** Map - creates new set with mapped values *)
let map f s =
  let result = Hash_set.Poly.create () in
    Hash_set.iter s ~f:(fun v -> Hash_set.add result (f v));
    result

(** In-place map (mutates s and returns it) *)
let imap f s =
  let pairs = Hash_set.to_list s in
    Hash_set.clear s;
    List.iter pairs ~f:(fun v -> Hash_set.add s (f v));
    s

(** Filter - creates new set with filtered values *)
let filter f s = Hash_set.filter s ~f

(** In-place filter (mutates s and returns it) *)
let ifilter f s =
  Hash_set.filter_inplace s ~f;
  s

(** Async map *)
let async_map f s =
  let+ results = Lwt_list.map_p f (Hash_set.to_list s) in
    Hash_set.Poly.of_list results

(** Async filter *)
let async_filter f s =
  let* vals = Lwt_list.filter_p f (Hash_set.to_list s) in
    Lwt.return (Hash_set.Poly.of_list vals)

(** Iter *)
let iter f s = Hash_set.iter s ~f

(** Fold *)
let fold f s init = Hash_set.fold s ~init ~f:(fun acc v -> f acc v)

(** For all *)
let for_all f s = Hash_set.for_all s ~f

(** Exists *)
let exists f s = Hash_set.exists s ~f

(** Find - returns first element satisfying predicate *)
let find f s = Hash_set.find s ~f

(** Async for all *)
let async_for_all f s =
  let vals = Hash_set.to_list s in
  let rec check = function
    | [] -> Lwt.return_true
    | v :: rest ->
        let* result = f v in
          if result then check rest else Lwt.return_false
  in
    check vals

(** Async exists *)
let async_exists f s =
  let vals = Hash_set.to_list s in
  let rec check = function
    | [] -> Lwt.return_false
    | v :: rest ->
        let* result = f v in
          if result then Lwt.return_true else check rest
  in
    check vals

(** Cartesian product *)
let cross s1 s2 =
  let result = Hash_set.Poly.create () in
    Hash_set.iter s1 ~f:(fun v1 ->
        Hash_set.iter s2 ~f:(fun v2 -> Hash_set.add result (v1, v2))
    );
    result

(** Identity relation *)
let identity_relation s = map (fun x -> (x, x)) s

(** Inverse relation *)
let inverse_relation s = map (fun (a, b) -> (b, a)) s

(** Transitive closure (for relations) *)
let transitive_closure s =
  let result = Hash_set.copy s in
  let changed = ref true in
    while !changed do
      changed := false;
      let vals = Hash_set.to_list result in
        List.iter vals ~f:(fun (a, b) ->
            List.iter vals ~f:(fun (c, d) ->
                if Poly.(b = c) && not (Hash_set.mem result (a, d)) then (
                  Hash_set.add result (a, d);
                  changed := true
                )
            )
        )
    done;
    result

(** Reflexive closure *)
let reflexive_closure domain s = union (identity_relation domain) s

(** Check if acyclic *)
let acyclic s =
  let s_tc = transitive_closure s in
    Hash_set.for_all s_tc ~f:(fun (a, b) -> not Poly.(a = b))

(** Check if irreflexive *)
let is_irreflexive s = for_all (fun (a, b) -> not Poly.(a = b)) s

(** Equality *)
let equal s1 s2 = Hash_set.equal s1 s2

(** Subset *)
let subset s1 s2 = Hash_set.for_all s1 ~f:(fun v -> Hash_set.mem s2 v)

(** To string - requires a string conversion function *)
let to_string string_of_val s =
  let vals = Hash_set.to_list s |> List.map ~f:string_of_val in
    if List.is_empty vals then "∅"
    else Printf.sprintf "{%s}" (String.concat ~sep:"," vals)
