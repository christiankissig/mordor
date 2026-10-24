(** The browser's {!Domain_pool}: one domain, so work runs where it is asked
    for. [Parallel] asks for a pool only for more than one thread. *)

type pool = unit

let setup _ = ()
let teardown () = ()
let num_domains () = 1
let detach () f = Lwt.wrap f
