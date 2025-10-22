(** Unordered Set with structural equality *)

(** Equality function for values *)
val value_equality : 'a -> 'a -> bool

(** The type of sets containing elements of type ['a]. Implemented as a hash
    table mapping elements to themselves. *)
type 'a t

(** {1 Creation} *)

(** [create ()] returns a new empty set *)
val create : unit -> 'a t

(** [singleton x] returns a set containing only [x] *)
val singleton : 'a -> 'a t

(** [of_list lst] creates a set from a list of elements *)
val of_list : 'a list -> 'a t

(** {1 Membership and Basic Operations} *)

(** [mem s x] returns [true] if [x] is in set [s], [false] otherwise *)
val mem : 'a t -> 'a -> bool

(** [add s x] returns a set with [x] added to [s] *)
val add : 'a t -> 'a -> 'a t

(** [remove s x] returns a set with [x] removed from [s] *)
val remove : 'a t -> 'a -> 'a t

(** [values s] returns all elements in [s] as a list *)
val values : 'a t -> 'a list

(** [size s] returns the number of elements in [s] *)
val size : 'a t -> int

(** [clear s] removes all elements from [s] and returns it *)
val clear : 'a t -> 'a t

(** [clone s] returns a new set containing the same elements as [s] *)
val clone : 'a t -> 'a t

(** {1 Set Operations} *)

(** [union s1 s2] returns the union of [s1] and [s2] *)
val union : 'a t -> 'a t -> 'a t

(** [inplace_union s1 s2] adds all elements of [s2] to [s1] in-place *)
val inplace_union : 'a t -> 'a t -> 'a t

(** [intersection s1 s2] returns the intersection of [s1] and [s2] *)
val intersection : 'a t -> 'a t -> 'a t

(** [set_minus s1 s2] returns elements in [s1] but not in [s2] *)
val set_minus : 'a t -> 'a t -> 'a t

(** [inplace_set_minus s1 s2] removes all elements of [s2] from [s1] in-place *)
val inplace_set_minus : 'a t -> 'a t -> 'a t

(** [difference s1 s2] returns the symmetric difference of [s1] and [s2] *)
val difference : 'a t -> 'a t -> 'a t

(** {1 Transformation} *)

(** [map f s] returns a new set with [f] applied to each element *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** [imap f s] applies [f] to each element in-place *)
val imap : ('a -> 'a) -> 'a t -> 'a t

(** [filter f s] returns a new set with only elements satisfying [f] *)
val filter : ('a -> bool) -> 'a t -> 'a t

(** [ifilter f s] removes elements not satisfying [f] in-place *)
val ifilter : ('a -> bool) -> 'a t -> 'a t

(** [async_map f s] asynchronously maps [f] over [s] *)
val async_map : ('a -> 'b Lwt.t) -> 'a t -> 'b t Lwt.t

(** [async_filter f s] asynchronously filters [s] using [f] *)
val async_filter : ('a -> bool Lwt.t) -> 'a t -> 'a t Lwt.t

(** {1 Iteration and Folding} *)

(** [iter f s] applies [f] to each element in [s] *)
val iter : ('a -> unit) -> 'a t -> unit

(** [fold f s init] folds [f] over elements in [s] with initial value [init] *)
val fold : ('b -> 'a -> 'b) -> 'a t -> 'b -> 'b

(** [for_all f s] returns [true] if [f] holds for all elements in [s] *)
val for_all : ('a -> bool) -> 'a t -> bool

(** [exists f s] returns [true] if [f] holds for at least one element in [s] *)
val exists : ('a -> bool) -> 'a t -> bool

(** [find f s] returns [Some x] for the first element satisfying [f], or [None]
*)
val find : ('a -> bool) -> 'a t -> 'a option

(** [async_for_all f s] asynchronously checks if [f] holds for all elements *)
val async_for_all : ('a -> bool Lwt.t) -> 'a t -> bool Lwt.t

(** [async_exists f s] asynchronously checks if [f] holds for any element *)
val async_exists : ('a -> bool Lwt.t) -> 'a t -> bool Lwt.t

(** {1 Relational Operations} *)

(** [cross s1 s2] returns the Cartesian product of [s1] and [s2] *)
val cross : 'a t -> 'b t -> ('a * 'b) t

(** [identity_relation s] returns the identity relation over [s] *)
val identity_relation : 'a t -> ('a * 'a) t

(** [inverse_relation s] returns the inverse of relation [s] *)
val inverse_relation : ('a * 'b) t -> ('b * 'a) t

(** [transitive_closure s] computes the transitive closure of relation [s] *)
val transitive_closure : ('a * 'a) t -> ('a * 'a) t

(** [reflexive_closure domain s] returns the reflexive closure of relation [s]
    over [domain] *)
val reflexive_closure : 'a t -> ('a * 'a) t -> ('a * 'a) t

(** [acyclic s] returns [true] if the relation [s] is acyclic *)
val acyclic : ('a * 'a) t -> bool

(** [is_irreflexive s] returns [true] if the relation [s] is irreflexive *)
val is_irreflexive : ('a * 'a) t -> bool

(** {1 Comparison} *)

(** [equal s1 s2] returns [true] if [s1] and [s2] contain the same elements *)
val equal : 'a t -> 'a t -> bool

(** [subset s1 s2] returns [true] if [s1] is a subset of [s2] *)
val subset : 'a t -> 'a t -> bool

(** {1 Conversion} *)

(** [to_string string_of_val s] returns a string representation of [s] using
    [string_of_val] to convert each element to a string *)
val to_string : ('a -> string) -> 'a t -> string
