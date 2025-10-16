(** Unordered Set with structural equality *)

open Lwt.Syntax

(** Equality function for values *)
let value_equality a b =
  match (a, b) with
  | x, y when x == y -> true
  | x, y when Stdlib.(x = y) -> true
  | _ -> false

(** Generic set type using hash table *)
type 'a t = ('a, 'a) Hashtbl.t

(** Create empty set *)
let create () : 'a t = Hashtbl.create 16

(** Create singleton set *)
let singleton x =
  let s = create () in
    Hashtbl.add s x x;
    s

(** Create from list *)
let of_list lst =
  let s = create () in
    List.iter (fun x -> Hashtbl.add s x x) lst;
    s

(** Check membership *)
let mem s x = Hashtbl.mem s x

(** Add element *)
let add s x =
  Hashtbl.replace s x x;
  s

(** Remove element *)
let remove s x =
  Hashtbl.remove s x;
  s

(** Get all values *)
let values s = Hashtbl.fold (fun _ v acc -> v :: acc) s []

(** Size *)
let size s = Hashtbl.length s

(** Clear set *)
let clear s =
  Hashtbl.clear s;
  s

(** Clone set *)
let clone s =
  let ns = create () in
    Hashtbl.iter (fun k v -> Hashtbl.add ns k v) s;
    ns

(** Union *)
let union s1 s2 =
  let result = clone s1 in
    Hashtbl.iter (fun k v -> Hashtbl.add result k v) s2;
    result

(** In-place union *)
let inplace_union s1 s2 =
  Hashtbl.iter (fun k v -> Hashtbl.add s1 k v) s2;
  s1

(** Intersection *)
let intersection s1 s2 =
  let result = create () in
    Hashtbl.iter (fun k v -> if Hashtbl.mem s2 k then Hashtbl.add result k v) s1;
    result

(** Set minus *)
let set_minus s1 s2 =
  let result = clone s1 in
    Hashtbl.iter (fun k _ -> Hashtbl.remove result k) s2;
    result

(** In-place set minus *)
let inplace_set_minus s1 s2 =
  Hashtbl.iter (fun k _ -> Hashtbl.remove s1 k) s2;
  s1

(** Difference (symmetric difference) *)
let difference s1 s2 =
  let a = clone s1 in
  let b = clone s2 in
  let _ = inplace_set_minus b s1 in
  let _ = inplace_set_minus a s2 in
    inplace_union a b

(** Map *)
let map f s =
  let result = create () in
    Hashtbl.iter
      (fun _ v ->
        let nv = f v in
          Hashtbl.add result nv nv
      )
      s;
    result

(** In-place map *)
let imap f s =
  let pairs = values s in
    clear s |> ignore;
    List.iter
      (fun v ->
        let nv = f v in
          Hashtbl.add s nv nv
      )
      pairs;
    s

(** Filter *)
let filter f s =
  let result = create () in
    Hashtbl.iter (fun _ v -> if f v then Hashtbl.add result v v) s;
    result

(** In-place filter *)
let ifilter f s =
  let to_remove = ref [] in
    Hashtbl.iter (fun k v -> if not (f v) then to_remove := k :: !to_remove) s;
    List.iter (Hashtbl.remove s) !to_remove;
    s

(** Async map *)
let async_map f s =
  let+ results = Lwt_list.map_p f (values s) in
    of_list results

(** Async filter *)
let async_filter f s =
  let* vals = Lwt_list.filter_p f (values s) in
    Lwt.return (of_list vals)

(** Iter *)
let iter f s = Hashtbl.iter (fun _ v -> f v) s

(** Fold *)
let fold f s init = Hashtbl.fold (fun _ v acc -> f acc v) s init

(** For all *)
let for_all f s = Hashtbl.fold (fun _ v acc -> acc && f v) s true

(** Exists *)
let exists f s = Hashtbl.fold (fun _ v acc -> acc || f v) s false

(** Find *)
let find f s =
  Hashtbl.fold
    (fun _ v acc ->
      match acc with
      | Some _ -> acc
      | None -> if f v then Some v else None
    )
    s None

(** Async for all *)
let async_for_all f s =
  let vals = values s in
  let rec check = function
    | [] -> Lwt.return_true
    | v :: rest ->
        let* result = f v in
          if result then check rest else Lwt.return_false
  in
    check vals

(** Async exists *)
let async_exists f s =
  let vals = values s in
  let rec check = function
    | [] -> Lwt.return_false
    | v :: rest ->
        let* result = f v in
          if result then Lwt.return_true else check rest
  in
    check vals

(** Cartesian product *)
let cross s1 s2 =
  let result = create () in
    Hashtbl.iter
      (fun _ v1 ->
        Hashtbl.iter
          (fun _ v2 ->
            let pair = (v1, v2) in
              Hashtbl.add result pair pair
          )
          s2
      )
      s1;
    result

(** Identity relation *)
let identity_relation s = map (fun x -> (x, x)) s

(** Inverse relation *)
let inverse_relation s = map (fun (a, b) -> (b, a)) s

(** Transitive closure (for relations) *)
let transitive_closure s =
  let result = clone s in
  let vals = values result in
  let changed = ref true in
    while !changed do
      changed := false;
      List.iter
        (fun (a, b) ->
          List.iter
            (fun (c, d) ->
              if b = c && not (mem result (a, d)) then (
                add result (a, d) |> ignore;
                changed := true
              )
            )
            vals
        )
        vals
    done;
    result

(** Reflexive closure *)
let reflexive_closure domain s = union (identity_relation domain) s

(** Check if acyclic *)
let acyclic s =
  let vals = values s in
  let left_keys = Hashtbl.create 16 in
  let right_map = Hashtbl.create 16 in

  (* Build maps *)
  List.iter
    (fun (a, b) ->
      Hashtbl.replace left_keys a true;
      let rights = try Hashtbl.find right_map b with Not_found -> [] in
        Hashtbl.replace right_map b (a :: rights)
    )
    vals;

  (* Remove nodes with no incoming edges *)
  let changed = ref true in
    while !changed do
      changed := false;
      let keys = Hashtbl.fold (fun k _ acc -> k :: acc) left_keys [] in
        List.iter
          (fun key ->
            if not (Hashtbl.mem right_map key) then (
              Hashtbl.remove left_keys key;
              changed := true
            )
          )
          keys
    done;

    Hashtbl.length left_keys = 0

(** Check if irreflexive *)
let is_irreflexive s = for_all (fun (a, b) -> a <> b) s

(** Equality *)
let equal s1 s2 = size s1 = size s2 && for_all (fun v -> mem s2 v) s1

(** Subset *)
let subset s1 s2 = for_all (fun v -> mem s2 v) s1

(** To string *)
let to_string s =
  let vals =
    values s |> List.map (fun v -> Printf.sprintf "%d" (Obj.magic v))
  in
    if List.length vals = 0 then "∅"
    else Printf.sprintf "{%s}" (String.concat "," vals)
