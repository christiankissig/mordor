(** Executon monads to select asynchronous over synchronous execution *)

module type S = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

(* identity monad — plain synchronous values *)
module Identity : S with type 'a t = 'a = struct
  type 'a t = 'a

  let return x = x
  let bind x f = f x
  let ( >>= ) = bind
end

(* Lwt monad — async values *)
module Lwt_monad : S with type 'a t = 'a Lwt.t = struct
  type 'a t = 'a Lwt.t

  let return = Lwt.return
  let bind = Lwt.bind
  let ( >>= ) = Lwt.( >>= )
end
