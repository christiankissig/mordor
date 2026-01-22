(** Unordered set and relation operations.

    This module provides efficient unordered set (hash set) operations and
    relation operations built on top of sets. Sets are implemented using Core's
    polymorphic hash sets for good performance. Relations are represented as
    sets of pairs and support standard relational algebra operations like
    composition, closure, and acyclicity checking. *)

(** {1 Unordered Set} *)

(** Unordered set using Core's polymorphic hash set.

    Provides a functional-style API over mutable hash sets. Most operations that
    modify sets return the set for chaining, though the modification happens
    in-place. Operations prefixed with "i" (inplace) explicitly mutate and
    return the same set. *)
module USet : sig
  (** The set type. Polymorphic hash set supporting any type. *)
  type 'a t

  (** {2 Equality} *)

  (** [value_equality a b] checks value equality.

      Uses physical equality first, then polymorphic equality.

      @param a First value.
      @param b Second value.
      @return [true] if values are equal. *)
  val value_equality : 'a -> 'a -> bool

  (** [equal s1 s2] checks set equality.

      Two sets are equal if they contain the same elements.

      @param s1 First set.
      @param s2 Second set.
      @return [true] if sets are equal. *)
  val equal : 'a t -> 'a t -> bool

  (** {2 Construction} *)

  (** [create ()] creates an empty set.

      @return New empty set. *)
  val create : unit -> 'a t

  (** [singleton x] creates a set with single element.

      @param x The element.
      @return Set containing only [x]. *)
  val singleton : 'a -> 'a t

  (** [of_list lst] creates set from list.

      Duplicates in list are automatically removed.

      @param lst List of elements.
      @return Set containing list elements. *)
  val of_list : 'a list -> 'a t

  (** [to_list s] converts set to list.

      Order of elements is unspecified.

      @param s The set.
      @return List of set elements. *)
  val to_list : 'a t -> 'a list

  (** {2 Membership} *)

  (** [mem s x] checks if element is in set.

      @param s The set.
      @param x Element to check.
      @return [true] if [x] is in [s]. *)
  val mem : 'a t -> 'a -> bool

  (** {2 Modification} *)

  (** [add s x] adds element to set.

      Mutates the set and returns it for chaining. If [x] already exists, set is
      unchanged.

      @param s The set to modify.
      @param x Element to add.
      @return The modified set (same as [s]). *)
  val add : 'a t -> 'a -> 'a t

  (** [remove s x] removes element from set.

      Mutates the set and returns it for chaining. If [x] doesn't exist, set is
      unchanged.

      @param s The set to modify.
      @param x Element to remove.
      @return The modified set (same as [s]). *)
  val remove : 'a t -> 'a -> 'a t

  (** {2 Access} *)

  (** [values s] gets all elements as list.

      Alias for {!to_list}. Order is unspecified.

      @param s The set.
      @return List of all elements. *)
  val values : 'a t -> 'a list

  (** [size s] gets number of elements.

      @param s The set.
      @return Number of elements in set. *)
  val size : 'a t -> int

  (** [is_empty s] checks if set is empty.

      @param s The set.
      @return [true] if set has no elements. *)
  val is_empty : 'a t -> bool

  (** {2 Bulk Operations} *)

  (** [clear s] removes all elements.

      Mutates the set and returns it for chaining.

      @param s The set to clear.
      @return The cleared set (same as [s]). *)
  val clear : 'a t -> 'a t

  (** [clone s] creates a copy of set.

      @param s The set to copy.
      @return New set with same elements. *)
  val clone : 'a t -> 'a t

  (** {2 Set Operations} *)

  (** [union s1 s2] computes union.

      Creates new set containing all elements from both sets.

      @param s1 First set.
      @param s2 Second set.
      @return New set with s1 ∪ s2. *)
  val union : 'a t -> 'a t -> 'a t

  (** [flatten ss] flattens set of sets.

      Creates new set containing all elements from all inner sets.

      @param ss Set of sets.
      @return New set with ⋃ ss. *)
  val flatten : 'a t t -> 'a t

  (** [inplace_union s1 s2] computes union in-place.

      Adds all elements from [s2] to [s1], mutating [s1].

      @param s1 Set to modify.
      @param s2 Set to add from.
      @return The modified [s1]. *)
  val inplace_union : 'a t -> 'a t -> 'a t

  (** [intersection s1 s2] computes intersection.

      Creates new set containing only elements in both sets.

      @param s1 First set.
      @param s2 Second set.
      @return New set with s1 ∩ s2. *)
  val intersection : 'a t -> 'a t -> 'a t

  (** [set_minus s1 s2] computes set difference.

      Creates new set with elements in [s1] but not in [s2].

      @param s1 First set.
      @param s2 Set to subtract.
      @return New set with s1 \ s2. *)
  val set_minus : 'a t -> 'a t -> 'a t

  (** [inplace_set_minus s1 s2] computes difference in-place.

      Removes all elements of [s2] from [s1], mutating [s1].

      @param s1 Set to modify.
      @param s2 Set to subtract.
      @return The modified [s1]. *)
  val inplace_set_minus : 'a t -> 'a t -> 'a t

  (** [difference s1 s2] computes symmetric difference.

      Creates new set with elements in exactly one of the sets.

      @param s1 First set.
      @param s2 Second set.
      @return New set with (s1 \ s2) ∪ (s2 \ s1). *)
  val difference : 'a t -> 'a t -> 'a t

  (** {2 Functional Operations} *)

  (** [map f s] applies function to all elements.

      Creates new set with transformed elements.

      @param f Transformation function.
      @param s The set.
      @return New set with f applied to each element. *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** [imap f s] applies function in-place.

      Replaces each element with its transformation, mutating [s].

      @param f Transformation function.
      @param s Set to modify.
      @return The modified [s]. *)
  val imap : ('a -> 'a) -> 'a t -> 'a t

  (** [filter f s] filters elements.

      Creates new set with only elements satisfying predicate.

      @param f Predicate function.
      @param s The set.
      @return New set with elements where f returns true. *)
  val filter : ('a -> bool) -> 'a t -> 'a t

  (** [ifilter f s] filters in-place.

      Removes elements not satisfying predicate, mutating [s].

      @param f Predicate function.
      @param s Set to modify.
      @return The modified [s]. *)
  val ifilter : ('a -> bool) -> 'a t -> 'a t

  (** {2 Asynchronous Operations} *)

  (** [async_map f s] maps asynchronously.

      Applies async function to all elements in parallel.

      @param f Async transformation function.
      @param s The set.
      @return Promise of new set with transformed elements. *)
  val async_map : ('a -> 'b Lwt.t) -> 'a t -> 'b t Lwt.t

  (** [async_filter f s] filters asynchronously.

      Applies async predicate to all elements in parallel.

      @param f Async predicate function.
      @param s The set.
      @return Promise of filtered set. *)
  val async_filter : ('a -> bool Lwt.t) -> 'a t -> 'a t Lwt.t

  (** {2 Iteration} *)

  (** [iter f s] iterates over elements.

      Applies function to each element for side effects. Order is unspecified.

      @param f Function to apply.
      @param s The set. *)
  val iter : ('a -> unit) -> 'a t -> unit

  (** [iter_async f s] iterates asynchronously.

      Applies async function sequentially to each element.

      @param f Async function to apply.
      @param s The set.
      @return Promise that completes after all iterations. *)
  val iter_async : ('a -> unit Lwt.t) -> 'a t -> unit Lwt.t

  (** [fold f s init] folds over elements.

      Accumulates a value by applying function to each element. Order is
      unspecified.

      @param f Accumulator function.
      @param s The set.
      @param init Initial accumulator value.
      @return Final accumulated value. *)
  val fold : ('b -> 'a -> 'b) -> 'a t -> 'b -> 'b

  (** {2 Predicates} *)

  (** [for_all f s] checks if all elements satisfy predicate.

      @param f Predicate function.
      @param s The set.
      @return [true] if f returns true for all elements. *)
  val for_all : ('a -> bool) -> 'a t -> bool

  (** [exists f s] checks if any element satisfies predicate.

      @param f Predicate function.
      @param s The set.
      @return [true] if f returns true for at least one element. *)
  val exists : ('a -> bool) -> 'a t -> bool

  (** [find f s] finds first element satisfying predicate.

      @param f Predicate function.
      @param s The set.
      @return [Some x] if element found, [None] otherwise. *)
  val find : ('a -> bool) -> 'a t -> 'a option

  (** [async_for_all f s] checks all elements asynchronously.

      Sequentially checks predicate, short-circuits on first false.

      @param f Async predicate function.
      @param s The set.
      @return Promise of [true] if all satisfy predicate. *)
  val async_for_all : ('a -> bool Lwt.t) -> 'a t -> bool Lwt.t

  (** [async_exists f s] checks existence asynchronously.

      Sequentially checks predicate, short-circuits on first true.

      @param f Async predicate function.
      @param s The set.
      @return Promise of [true] if any satisfies predicate. *)
  val async_exists : ('a -> bool Lwt.t) -> 'a t -> bool Lwt.t

  (** [subset s1 s2] checks if s1 is subset of s2.

      @param s1 Potential subset.
      @param s2 Potential superset.
      @return [true] if s1 ⊆ s2. *)
  val subset : 'a t -> 'a t -> bool

  (** {2 Conversion} *)

  (** [to_string string_of_val s] converts set to string.

      Uses mathematical set notation: {1,2,3} or ∅ for empty.

      @param string_of_val Function to convert elements to strings.
      @param s The set.
      @return String representation. *)
  val to_string : ('a -> string) -> 'a t -> string
end = struct
  open Core
  open Lwt.Syntax

  type 'a t = 'a Hash_set.Poly.t

  let value_equality a b =
    match (a, b) with
    | x, y when phys_equal x y -> true
    | x, y when Poly.(x = y) -> true
    | _ -> false

  let equal s1 s2 = Hash_set.equal s1 s2
  let create () : 'a t = Hash_set.Poly.create ()

  let singleton x =
    let s = Hash_set.Poly.create () in
      Hash_set.add s x;
      s

  let of_list lst = Hash_set.Poly.of_list lst
  let to_list s = Hash_set.to_list s
  let mem s x = Hash_set.mem s x

  let add s x =
    Hash_set.add s x;
    s

  let remove s x =
    Hash_set.remove s x;
    s

  let values s = Hash_set.to_list s
  let size s = Hash_set.length s
  let is_empty s = Hash_set.is_empty s

  let clear s =
    Hash_set.clear s;
    s

  let clone s = Hash_set.copy s
  let union s1 s2 = Hash_set.union s1 s2

  let flatten ss =
    let result = Hash_set.Poly.create () in
      Hash_set.iter ss ~f:(fun s ->
          Hash_set.iter s ~f:(fun x -> Hash_set.add result x)
      );
      result

  let inplace_union s1 s2 =
    Hash_set.iter s2 ~f:(fun x -> Hash_set.add s1 x);
    s1

  let intersection s1 s2 = Hash_set.inter s1 s2
  let set_minus s1 s2 = Hash_set.diff s1 s2

  let inplace_set_minus s1 s2 =
    Hash_set.iter s2 ~f:(fun x -> Hash_set.remove s1 x);
    s1

  let difference s1 s2 =
    let a = Hash_set.copy s1 in
    let b = Hash_set.copy s2 in
      Hash_set.iter s1 ~f:(fun x -> Hash_set.remove b x);
      Hash_set.iter s2 ~f:(fun x -> Hash_set.remove a x);
      Hash_set.iter b ~f:(fun x -> Hash_set.add a x);
      a

  let map f s =
    let result = Hash_set.Poly.create () in
      Hash_set.iter s ~f:(fun v -> Hash_set.add result (f v));
      result

  let imap f s =
    let pairs = Hash_set.to_list s in
      Hash_set.clear s;
      List.iter pairs ~f:(fun v -> Hash_set.add s (f v));
      s

  let filter f s = Hash_set.filter s ~f

  let ifilter f s =
    Hash_set.filter_inplace s ~f;
    s

  let async_map f s =
    let+ results = Lwt_list.map_p f (Hash_set.to_list s) in
      Hash_set.Poly.of_list results

  let async_filter f s =
    let* vals = Lwt_list.filter_p f (Hash_set.to_list s) in
      Lwt.return (Hash_set.Poly.of_list vals)

  let iter f s = Hash_set.iter s ~f

  let iter_async f s =
    let rec aux = function
      | [] -> Lwt.return_unit
      | v :: rest ->
          let* () = f v in
            aux rest
    in
      aux (Hash_set.to_list s)

  let fold f s init = Hash_set.fold s ~init ~f:(fun acc v -> f acc v)
  let for_all f s = Hash_set.for_all s ~f
  let exists f s = Hash_set.exists s ~f
  let find f s = Hash_set.find s ~f

  let async_for_all f s =
    let vals = Hash_set.to_list s in
    let rec check = function
      | [] -> Lwt.return_true
      | v :: rest ->
          let* result = f v in
            if result then check rest else Lwt.return_false
    in
      check vals

  let async_exists f s =
    let vals = Hash_set.to_list s in
    let rec check = function
      | [] -> Lwt.return_false
      | v :: rest ->
          let* result = f v in
            if result then Lwt.return_true else check rest
    in
      check vals

  let subset s1 s2 = for_all (fun v -> mem s2 v) s1

  let to_string string_of_val s =
    let vals = values s |> fun s -> List.map s ~f:string_of_val in
      if List.is_empty vals then "∅"
      else Printf.sprintf "{%s}" (String.concat ~sep:"," vals)
end

(** {1 Binary Relations} *)

(** Binary relation operations.

    A relation is a set of pairs representing connections between elements.
    Provides standard relational algebra operations including composition,
    closures, and graph-theoretic properties like acyclicity. Relations are
    heavily used to represent orderings and dependencies in the symbolic
    execution engine. *)
module URelation : sig
  (** Binary relation type: set of pairs. *)
  type 'a t = ('a * 'a) USet.t

  (** {2 Construction} *)

  (** [cross s1 s2] computes Cartesian product.

      Creates relation with all possible pairs from the two sets.

      @param s1 First set.
      @param s2 Second set.
      @return Relation s1 × s2. *)
  val cross : 'a USet.t -> 'a USet.t -> 'a t

  (** [identity s] creates identity relation.

      Returns relation containing [(x,x)] for each element in [s].

      @param s The set.
      @return Identity relation on s. *)
  val identity : 'a USet.t -> 'a t

  (** [inverse rel] inverts relation.

      Swaps all pairs: [(a,b)] becomes [(b,a)].

      @param rel The relation.
      @return Inverted relation. *)
  val inverse : 'a t -> 'a t

  (** {2 Composition} *)

  (** [compose rels] composes relations sequentially.

      Computes r1 ; r2 ; ... ; rn where [(a,c)] is in result if there exist
      intermediate elements such that pairs form a chain. Optimized to O(n × k)
      where n is largest relation size and k is number of relations.

      @param rels List of relations to compose.
      @return Composed relation. *)
  val compose : 'a t list -> 'a t

  (** [compose_adj_map rels] composes using pre-computed adjacency maps.

      Like {!compose} but uses pre-computed adjacency maps for efficiency.

      @param rels List of [(relation, adjacency_map)] pairs.
      @return Composed relation. *)
  val compose_adj_map : ('a t * ('a, 'a USet.t) Hashtbl.t) list -> 'a t

  (** {2 Closures} *)

  (** [reflexive_closure domain rel] adds reflexive edges.

      Returns relation with all pairs from [rel] plus [(x,x)] for all [x] in
      domain.

      @param domain The domain set.
      @param rel The relation.
      @return Reflexive closure. *)
  val reflexive_closure : 'a USet.t -> 'a t -> 'a t

  (** [symmetric_closure rel] adds symmetric edges.

      Returns relation with all pairs from [rel] plus inverse pairs.

      @param rel The relation.
      @return Symmetric closure. *)
  val symmetric_closure : 'a t -> 'a t

  (** [transitive_closure rel] computes transitive closure.

      Returns smallest transitive relation containing [rel]. If [(a,b)] and
      [(b,c)] are in result, so is [(a,c)].

      @param rel The relation.
      @return Transitive closure. *)
  val transitive_closure : 'a t -> 'a t

  (** [transitive_reduction rel] computes transitive reduction.

      Removes edges that can be derived transitively through other edges.
      Returns smallest relation with same transitive closure as [rel].

      @param rel The relation.
      @return Transitive reduction. *)
  val transitive_reduction : 'a t -> 'a t

  (** [exhaustive_closure rel] applies relation exhaustively.

      Repeatedly composes relation with itself, removing intermediate steps.

      @param rel The relation.
      @return Exhaustively closed relation. *)
  val exhaustive_closure : 'a t -> 'a t

  (** {2 Properties} *)

  (** [acyclic rel] checks if relation is acyclic.

      A relation is acyclic if its transitive closure contains no reflexive
      edges (no element reaches itself).

      @param rel The relation.
      @return [true] if acyclic. *)
  val acyclic : 'a t -> bool

  (** [is_irreflexive rel] checks if relation is irreflexive.

      A relation is irreflexive if it contains no [(x,x)] pairs.

      @param rel The relation.
      @return [true] if irreflexive. *)
  val is_irreflexive : 'a t -> bool

  (** [is_function rel] checks if relation is a function.

      A relation is a function if each element in the domain maps to at most one
      element in the codomain.

      @param rel The relation.
      @return [true] if relation is a function. *)
  val is_function : 'a t -> bool

  (** {2 Projection} *)

  (** [pi_1 rel] projects first components.

      Returns set of all first elements from pairs in relation.

      @param rel The relation.
      @return Set of first components (domain). *)
  val pi_1 : 'a t -> 'a USet.t

  (** [pi_2 rel] projects second components.

      Returns set of all second elements from pairs in relation.

      @param rel The relation.
      @return Set of second components (codomain). *)
  val pi_2 : 'a t -> 'a USet.t

  (** {2 Representation} *)

  (** [adjacency_map rel] builds adjacency map with USets.

      Creates hash table mapping each element to the set of elements it relates
      to. Useful for efficient graph traversal.

      @param rel The relation.
      @return Hash table from elements to their successors. *)
  val adjacency_map : 'a t -> ('a, 'a USet.t) Hashtbl.t

  (** [adjacency_list_map rel] builds adjacency map with lists.

      Like {!adjacency_map} but uses lists instead of sets.

      @param rel The relation.
      @return Hash table from elements to successor lists. *)
  val adjacency_list_map : 'a t -> ('a, 'a list) Hashtbl.t

  (** [to_map rel] converts relation to map.

      Creates hash table mapping each first element to its corresponding second
      element. If multiple pairs share the same first element, one is chosen
      arbitrarily.

      @param rel The relation.
      @return Hash table from first to second elements. *)
  val to_map : 'a t -> ('a, 'a) Hashtbl.t
end = struct
  type 'a t = ('a * 'a) USet.t

  let pi_1 rel = USet.map (fun (x, _) -> x) rel
  let pi_2 rel = USet.map (fun (_, y) -> y) rel

  let cross s1 s2 =
    let result = USet.create () in
      USet.iter
        (fun v1 -> USet.iter (fun v2 -> USet.add result (v1, v2) |> ignore) s2)
        s1;
      result

  let adjacency_map rel =
    let map = Hashtbl.create (USet.size rel) in
      USet.iter
        (fun (from, to_) ->
          let existing =
            try Hashtbl.find map from with Not_found -> USet.create ()
          in
            USet.add existing to_ |> ignore;
            Hashtbl.replace map from existing
        )
        rel;
      map

  let adjacency_list_map rel =
    let map = Hashtbl.create (USet.size rel) in
      USet.iter
        (fun (from, to_) ->
          let existing = try Hashtbl.find map from with Not_found -> [] in
            Hashtbl.replace map from (to_ :: existing)
        )
        rel;
      map

  let to_map rel =
    let map = Hashtbl.create (USet.size rel) in
      USet.iter (fun (f, t) -> Hashtbl.replace map f t) rel;
      map

  let compose (rels : 'a t list) : 'a t =
    let landmark = Landmark.register "URelation.compose" in
      Landmark.enter landmark;
      let composition =
        match rels with
        | [] -> USet.create ()
        | [ r ] -> USet.clone r
        | r :: rest ->
            List.fold_left
              (fun acc rel ->
                (* Build index: c -> list of d where (c, d) in rel *)
                let index = adjacency_list_map rel in
                (* Compose using index *)
                let result = USet.create () in
                  USet.iter
                    (fun (a, b) ->
                      match Hashtbl.find_opt index b with
                      | Some ds ->
                          List.iter
                            (fun d -> USet.add result (a, d) |> ignore)
                            ds
                      | None -> ()
                    )
                    acc;
                  result
              )
              (USet.clone r) rest
      in
        Landmark.exit landmark;
        composition

  let compose_adj_map (rels : ('a t * ('a, 'a USet.t) Hashtbl.t) list) : 'a t =
    let landmark = Landmark.register "URelation.compose" in
      Landmark.enter landmark;
      let composition =
        match rels with
        | [] -> USet.create ()
        | [ (r, _) ] -> USet.clone r
        | (r, _) :: rest ->
            List.fold_left
              (fun acc (r, index) ->
                let result = USet.create () in
                  USet.iter
                    (fun (a, b) ->
                      match Hashtbl.find_opt index b with
                      | Some ds ->
                          USet.iter
                            (fun d -> USet.add result (a, d) |> ignore)
                            ds
                      | None -> ()
                    )
                    acc;
                  result
              )
              (USet.clone r) rest
      in
        Landmark.exit landmark;
        composition

  let identity s = USet.map (fun x -> (x, x)) s
  let inverse s = USet.map (fun (a, b) -> (b, a)) s

  let transitive_closure s =
    let landmark = Landmark.register "URelation.transitive_closure" in
      Landmark.enter landmark;
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
        Landmark.exit landmark;
        result

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

  let reflexive_closure domain s = identity domain |> USet.union s
  let symmetric_closure s = inverse s |> USet.union s

  let acyclic s =
    let landmark = Landmark.register "URelation.acyclic" in
      Landmark.enter landmark;
      let s_tc = transitive_closure s in
      let result = USet.for_all (fun (a, b) -> not (a = b)) s_tc in
        Landmark.exit landmark;
        result

  let is_irreflexive s = USet.for_all (fun (a, b) -> not (a = b)) s

  let is_function s =
    USet.for_all
      (fun a -> USet.size (USet.filter (fun (x, _) -> x = a) s) <= 1)
      (pi_1 s)
end
