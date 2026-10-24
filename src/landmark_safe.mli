(** {1 Profiling}

    Domain-safe profiling landmarks, one implementation per platform (W2, #178).
    This is a virtual module: [mordor.native] implements it with [Landmarks],
    profiling on the main domain only, since [Landmarks] is not domain-safe. A
    platform without profiling makes every call a no-op. *)

(** A landmark. *)
type landmark

(** [register name] registers a landmark. It must be called from the main
    domain, which in practice means at module initialisation. *)
val register : ?id:string -> ?location:string -> string -> landmark

(** [enter landmark] enters [landmark] when profiling, on the main domain, and
    does nothing otherwise. *)
val enter : landmark -> unit

(** [exit landmark] is the counterpart to {!enter}, a no-op under the same
    conditions, so that entries and exits pair up on every domain. *)
val exit : landmark -> unit
