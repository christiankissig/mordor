(** Parallel map for lists using Lwt *)
let lwt_pmap f lst = Lwt_list.map_p f lst

let lwt_piter f lst = Lwt_list.iter_p f lst

(** Parallel some (short-circuit OR) for lists using Lwt *)
let rec lwt_psome f = function
  | [] -> Lwt.return false
  | x :: xs ->
      let%lwt result = f x in
        if result then Lwt.return true else lwt_psome f xs

(** Parallel every (short-circuit AND) for lists using Lwt *)
let rec lwt_pevery f = function
  | [] -> Lwt.return true
  | x :: xs ->
      let%lwt result = f x in
        if not result then Lwt.return false else lwt_pevery f xs

(** Parallel all (no short-circuit) for lists using Lwt *)
let lwt_pall f lst =
  let%lwt results = Lwt_list.map_p f lst in
    Lwt.return (List.for_all (fun x -> x) results)
