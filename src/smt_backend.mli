(** {1 SMT Backend}

    The solver MoRDor asks, one implementation per platform (W2, #178). This is
    a virtual module: an executable chooses its implementation when it is
    linked, [mordor.native] for the CLI, the web server and the tests, which
    asks Z3. {!Solver} is built on it, and is what the rest of MoRDor uses.

    A backend works on MoRDor's own expressions, so it owns their translation:
    integers, booleans, the arithmetic, comparison and logical operators, and
    [&], [|] and [^] on integers through 64-bit bitvectors. *)

open Types

(** A solver: its assertions, in scopes, and the symbols they name. *)
type solver

(** [create ()] is a solver with no assertions and no symbols. *)
val create : unit -> solver

(** [push solver] opens a scope. *)
val push : solver -> unit

(** [pop solver] retracts what was asserted since the matching {!push}. *)
val pop : solver -> unit

(** [add solver exprs] asserts [exprs]. Raises [Failure] on an operator the
    backend does not translate. *)
val add : solver -> expr list -> unit

(** [check solver] decides what [solver] has asserted: [Some true] if it is
    satisfiable, [Some false] if not, [None] if the backend cannot tell. *)
val check : solver -> bool option

(** [model solver] is the model {!check} found, as a binding for every symbol
    [solver]'s assertions named, or [None] if there is none. *)
val model : solver -> (string, value_type) Hashtbl.t option

(** [statistics solver] is the backend's account of its work, for diagnostics.
*)
val statistics : solver -> string
