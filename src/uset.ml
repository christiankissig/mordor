(** Unordered Set using Core's Hash_set.Poly *)

module USet : sig
  type 'a t

  val value_equality : 'a -> 'a -> bool
  val equal : 'a t -> 'a t -> bool
  val create : unit -> 'a t
  val singleton : 'a -> 'a t
  val of_list : 'a list -> 'a t
  val to_list : 'a t -> 'a list
  val mem : 'a t -> 'a -> bool
  val add : 'a t -> 'a -> 'a t
  val remove : 'a t -> 'a -> 'a t
  val values : 'a t -> 'a list
  val size : 'a t -> int
  val clear : 'a t -> 'a t
  val clone : 'a t -> 'a t
  val union : 'a t -> 'a t -> 'a t
  val flatten : 'a t t -> 'a t
  val inplace_union : 'a t -> 'a t -> 'a t
  val intersection : 'a t -> 'a t -> 'a t
  val set_minus : 'a t -> 'a t -> 'a t
  val inplace_set_minus : 'a t -> 'a t -> 'a t
  val difference : 'a t -> 'a t -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val imap : ('a -> 'a) -> 'a t -> 'a t
  val filter : ('a -> bool) -> 'a t -> 'a t
  val ifilter : ('a -> bool) -> 'a t -> 'a t
  val async_map : ('a -> 'b Lwt.t) -> 'a t -> 'b t Lwt.t
  val async_filter : ('a -> bool Lwt.t) -> 'a t -> 'a t Lwt.t
  val iter : ('a -> unit) -> 'a t -> unit
  val fold : ('b -> 'a -> 'b) -> 'a t -> 'b -> 'b
  val for_all : ('a -> bool) -> 'a t -> bool
  val exists : ('a -> bool) -> 'a t -> bool
  val find : ('a -> bool) -> 'a t -> 'a option
  val async_for_all : ('a -> bool Lwt.t) -> 'a t -> bool Lwt.t
  val async_exists : ('a -> bool Lwt.t) -> 'a t -> bool Lwt.t
  val subset : 'a t -> 'a t -> bool
  val to_string : ('a -> string) -> 'a t -> string
end = struct
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

  (** Equality *)
  let equal s1 s2 = Hash_set.equal s1 s2

  (** Create empty set *)
  let create () : 'a t = Hash_set.Poly.create ()

  (** Create singleton set *)
  let singleton x =
    let s = Hash_set.Poly.create () in
      Hash_set.add s x;
      s

  (** Create from list *)
  let of_list lst = Hash_set.Poly.of_list lst

  let to_list s = Hash_set.to_list s

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

  (** Flatten a set of sets into a single set *)
  let flatten ss =
    let result = Hash_set.Poly.create () in
      Hash_set.iter ss ~f:(fun s ->
          Hash_set.iter s ~f:(fun x -> Hash_set.add result x)
      );
      result

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

  (** Subset *)
  let subset s1 s2 = for_all (fun v -> mem s2 v) s1

  (** To string - requires a string conversion function *)
  let to_string string_of_val s =
    let vals = values s |> fun s -> List.map s ~f:string_of_val in
      if List.is_empty vals then "∅"
      else Printf.sprintf "{%s}" (String.concat ~sep:"," vals)
end

module URelation : sig
  type 'a t = ('a * 'a) USet.t

  val cross : 'a USet.t -> 'a USet.t -> 'a t
  val identity_relation : 'a USet.t -> 'a t
  val inverse_relation : 'a t -> 'a t
  val reflexive_closure : 'a USet.t -> 'a t -> 'a t
  val transitive_closure : 'a t -> 'a t
  val transitive_reduction : 'a t -> 'a t
  val exhaustive_closure : 'a t -> 'a t
  val acyclic : 'a t -> bool
  val is_irreflexive : 'a t -> bool
  val is_function : 'a t -> bool
  val pi_1 : 'a t -> 'a USet.t
  val pi_2 : 'a t -> 'a USet.t
  val adjacency_map : 'a t -> ('a, 'a USet.t) Hashtbl.t
end = struct
  type 'a t = ('a * 'a) USet.t

  (** Project first elements from relation *)
  let pi_1 rel = USet.map (fun (x, _) -> x) rel

  (** Project second elements from relation *)
  let pi_2 rel = USet.map (fun (_, y) -> y) rel

  (** Cartesian product *)
  let cross s1 s2 =
    let result = USet.create () in
      USet.iter
        (fun v1 -> USet.iter (fun v2 -> USet.add result (v1, v2) |> ignore) s2)
        s1;
      result

  (** Identity relation *)
  let identity_relation s = USet.map (fun x -> (x, x)) s

  (** Inverse relation *)
  let inverse_relation s = USet.map (fun (a, b) -> (b, a)) s

  (** Transitive closure (for relations) *)
  let transitive_closure s =
    let result = USet.clone s in
    let changed = ref true in
      while !changed do
        changed := false;
        let vals = USet.to_list result in
          List.iter
            (fun (a, b) ->
              List.iter
                (fun (c, d) ->
                  if b = c && not (USet.mem result (a, d)) then (
                    USet.add result (a, d) |> ignore;
                    changed := true;
                    ()
                  )
                )
                vals
            )
            vals
      done;
      result

  (* Compute transitive reduction: remove edges that can be derived through transitivity *)
  let transitive_reduction rel =
    USet.filter
      (fun (e1, e2) ->
        (* Keep (e1, e2) only if there's no intermediate e3 where (e1,e3) and (e3,e2) both in rel *)
        not
          (USet.exists
             (fun (f, t) -> f = e1 && t <> e2 && USet.mem rel (t, e2))
             rel
          )
      )
      rel

  (* Applies relation exhaustively on itself. *)
  let exhaustive_closure s =
    let result = USet.clone s in
    let changed = ref true in
      while !changed do
        changed := false;
        let vals = USet.to_list result in
          List.iter
            (fun (a, b) ->
              List.iter
                (fun (c, d) ->
                  if not (USet.mem result (a, d)) then
                    if b = c then USet.add result (a, d) |> ignore;
                  USet.remove result (a, b) |> ignore;
                  changed := true;
                  ()
                )
                vals
            )
            vals
      done;
      result

  (** Reflexive closure *)
  let reflexive_closure domain s = USet.union (identity_relation domain) s

  (** Check if acyclic *)
  let acyclic s =
    let s_tc = transitive_closure s in
      USet.for_all (fun (a, b) -> not (a = b)) s_tc

  (** Check if irreflexive *)
  let is_irreflexive s = USet.for_all (fun (a, b) -> not (a = b)) s

  (** Check if relation is a function, i.e. uniquely maps each element in domain
      to at most one element in codomain *)
  let is_function s =
    USet.for_all
      (fun a -> USet.size (USet.filter (fun (x, _) -> x = a) s) <= 1)
      (pi_1 s)

  (* Build tree for program order *)
  let adjacency_map rel =
    let tree = Hashtbl.create 256 in
      USet.iter (fun e -> Hashtbl.add tree e (USet.create ())) (pi_1 rel);
      USet.iter
        (fun (from, to_) ->
          let set = Hashtbl.find tree from in
            USet.add set to_ |> ignore
        )
        rel;
      tree
end
