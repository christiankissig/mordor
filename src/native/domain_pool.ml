(** The native {!Domain_pool}: [Lwt_domain]'s pools of OCaml domains. *)

type pool = Lwt_domain.pool

let setup n = Lwt_domain.setup_pool n
let teardown = Lwt_domain.teardown_pool
let num_domains = Lwt_domain.get_num_domains
let detach pool f = Lwt_domain.detach pool f ()
