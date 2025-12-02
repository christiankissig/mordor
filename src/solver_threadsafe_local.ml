(** solver_threadsafe_local.ml - Thread-safe solver with thread-local caching *)

open Expr
open Lwt.Syntax

(** Thread-local cache implementation *)
type local_cache = {
  quick_check_cache : (string, bool option) Hashtbl.t;
  semeq_eq_cache : (string, bool) Hashtbl.t;
  semeq_poteq_cache : (string, bool) Hashtbl.t;
}

(** Initialize thread-local caching *)
let init_thread_cache () =
  {
    quick_check_cache = Hashtbl.create 256;
    semeq_eq_cache = Hashtbl.create 256;
    semeq_poteq_cache = Hashtbl.create 256;
  }

(** Clear the cache *)
let clear_thread_cache cache =
  Hashtbl.clear cache.quick_check_cache;
  Hashtbl.clear cache.semeq_eq_cache;
  Hashtbl.clear cache.semeq_poteq_cache

(** Get cache statistics *)
let cache_stats cache =
  Printf.sprintf
    "quick_check: %d entries, semeq_eq: %d entries, semeq_poteq: %d entries"
    (Hashtbl.length cache.quick_check_cache)
    (Hashtbl.length cache.semeq_eq_cache)
    (Hashtbl.length cache.semeq_poteq_cache)

(** Helper to create cache key from expressions *)
let cache_key_of_exprs exprs =
  let sorted = List.sort Expr.compare exprs in
    String.concat ";" (List.map Expr.to_string sorted)

(** Helper to create cache key from two expressions *)
let cache_key_of_pair a b =
  Printf.sprintf "%s|%s" (Expr.to_string a) (Expr.to_string b)

(** Thread-safe cached quick_check using local cache *)
let quick_check_cached cache exprs =
  let key = cache_key_of_exprs exprs in
    match Hashtbl.find_opt cache.quick_check_cache key with
    | Some result -> Lwt.return result
    | None ->
        let* result = Solver.quick_check exprs in
          Hashtbl.add cache.quick_check_cache key result;
          Lwt.return result

(** Thread-safe cached is_sat using local cache *)
let is_sat_cached cache exprs =
  let* result = quick_check_cached cache exprs in
    match result with
    | Some true -> Lwt.return_true
    | _ -> Lwt.return_false

(** Thread-safe cached is_unsat using local cache *)
let is_unsat_cached cache exprs =
  let* result = quick_check_cached cache exprs in
    match result with
    | Some false -> Lwt.return_true
    | _ -> Lwt.return_false

(** Thread-local semantic equality cache *)
type semeq_cache = {
  eq_cache : (string, bool) Hashtbl.t;
  poteq_cache : (string, bool) Hashtbl.t;
}

(** Create a new semantic equality cache *)
let create_semeq_cache () =
  { eq_cache = Hashtbl.create 256; poteq_cache = Hashtbl.create 256 }

(** Cached semantic equality check with thread-local cache *)
let exeq_cached cache ?(state = []) a b =
  let key = cache_key_of_pair a b in
    match Hashtbl.find_opt cache.eq_cache key with
    | Some result -> Lwt.return result
    | None ->
        let* result = Solver.exeq ~state a b in
          Hashtbl.add cache.eq_cache key result;
          Lwt.return result

(** Cached potential equality check with thread-local cache *)
let expoteq_cached cache ?(state = []) a b =
  let key = cache_key_of_pair a b in
    match Hashtbl.find_opt cache.poteq_cache key with
    | Some result -> Lwt.return result
    | None ->
        let* result = Solver.expoteq ~state a b in
          Hashtbl.add cache.poteq_cache key result;
          Lwt.return result

(** Clear semantic equality cache *)
let clear_semeq_cache cache =
  Hashtbl.clear cache.eq_cache;
  Hashtbl.clear cache.poteq_cache

(** Parallel execution with automatic thread-local caching *)
module ParallelCached = struct
  (** Partition a list into n roughly equal chunks *)
  let partition n lst =
    let len = List.length lst in
    let chunk_size = max 1 ((len + n - 1) / n) in
    let rec aux acc remaining =
      if remaining = [] then List.rev acc
      else
        let chunk, rest =
          let rec take n lst acc =
            if n <= 0 || lst = [] then (List.rev acc, lst)
            else take (n - 1) (List.tl lst) (List.hd lst :: acc)
          in
            take chunk_size remaining []
        in
          aux (chunk :: acc) rest
    in
      aux [] lst

  (** Execute parallel check operations with automatic caching *)
  let parallel_check n_threads tasks =
    let open Lwt.Infix in
    let chunks = partition n_threads tasks in

    let process_chunk chunk =
      (* Each thread gets its own cache *)
      let cache = init_thread_cache () in
        Lwt_list.map_s (fun exprs -> quick_check_cached cache exprs) chunk
    in

    Lwt_list.map_p process_chunk chunks >|= List.flatten

  (** Execute parallel solve operations with automatic caching *)
  let parallel_solve n_threads tasks =
    let open Lwt.Infix in
    let chunks = partition n_threads tasks in

    let process_chunk chunk =
      (* Each thread works independently *)
      Lwt_list.map_s (fun exprs -> Solver.quick_solve exprs) chunk
    in

    Lwt_list.map_p process_chunk chunks >|= List.flatten

  (** Parallel map with automatic thread-local caching *)
  let parallel_map n_threads f items =
    let open Lwt.Infix in
    let chunks = partition n_threads items in

    let process_chunk chunk =
      (* Each thread gets its own cache *)
      let cache = init_thread_cache () in
        Lwt_list.map_s (fun item -> f cache item) chunk
    in

    Lwt_list.map_p process_chunk chunks >|= List.flatten
end
