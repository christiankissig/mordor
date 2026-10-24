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

(** Sequential loops over a list in Lwt that use no stack per item whose promise
    is already resolved. [Lwt_list]'s binds call the next step at once on a
    resolved promise, so a loop whose steps all resolve at once nests one call
    per item. The server's steps wait on the network and break the chain; the
    browser build's do not, and JavaScript's stack is about 1 MB: 3.2W's 3,400
    execution graphs overflowed it (W4, #180). *)
module Lwt_loop = struct
  (** [iteri_s f l] is [Lwt_list.iteri_s f l]. *)
  let iteri_s f l =
    let rec go i = function
      | [] -> Lwt.return_unit
      | x :: rest -> (
          let p = try f i x with exn -> Lwt.fail exn in
            match Lwt.state p with
            | Lwt.Return () -> go (i + 1) rest
            | Lwt.Fail _ | Lwt.Sleep -> Lwt.bind p (fun () -> go (i + 1) rest)
        )
    in
      go 0 l
end
