(** {1 Domain Pool}

    The pool {!Parallel} dispatches work onto, one implementation per platform
    (W2, #178). This is a virtual module: [mordor.native] implements it with
    [Lwt_domain]. A platform with one domain implements it sequentially. *)

(** A pool of domains. *)
type pool

(** [setup n] is a pool of [n] domains. *)
val setup : int -> pool

(** [teardown pool] hands [pool]'s domains back. *)
val teardown : pool -> unit

(** [num_domains pool] is how many domains [pool] runs on. *)
val num_domains : pool -> int

(** [detach pool f] runs [f ()] on [pool], and resolves to its result. *)
val detach : pool -> (unit -> 'a) -> 'a Lwt.t
