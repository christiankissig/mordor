(** solver_threadsafe.ml - Thread-safe implementation for constraint solver *)

(** Thread-safe solver handle wrapping the underlying Solver module *)
type t = { solver : Solver.solver }

(** {1 Thread-Safe Solver Creation} *)

let create exprs = { solver = Solver.create exprs }
let create_empty () = { solver = Solver.create [] }

(** {1 Solver Management} *)

let reset t = { solver = Solver.reset t.solver }
let push t = { solver = Solver.push t.solver }
let pop t = { solver = Solver.pop t.solver }
let add_assertions t exprs = { solver = Solver.add_assertions t.solver exprs }

(** {1 Satisfiability Checking} *)

let check t = Solver.check t.solver

let quick_check exprs =
  (* Creates its own context, so thread-safe *)
  Solver.quick_check exprs

let quick_check_cached exprs =
  (* WARNING: Uses global cache in Solver module - NOT thread-safe *)
  Solver.quick_check_cached exprs

let is_sat exprs =
  (* Creates its own context, so thread-safe *)
  Solver.is_sat exprs

let is_sat_cached exprs =
  (* WARNING: Uses global cache in Solver module - NOT thread-safe *)
  Solver.is_sat_cached exprs

let is_unsat exprs =
  (* Creates its own context, so thread-safe *)
  Solver.is_unsat exprs

let is_unsat_cached exprs =
  (* WARNING: Uses global cache in Solver module - NOT thread-safe *)
  Solver.is_unsat_cached exprs

let solve_advanced t = Solver.solve_advanced t.solver

let implies premises conclusion =
  (* Creates its own context, so thread-safe *)
  Solver.implies premises conclusion

(** {1 Solution Extraction} *)

let solve t = Solver.solve t.solver

let quick_solve exprs =
  (* Creates its own context, so thread-safe *)
  Solver.quick_solve exprs

let concrete_value = Solver.concrete_value
let solve_for_vars t vars = Solver.solve_for_vars t.solver vars
let solve_with_ranges t = Solver.solve_with_ranges t.solver
let model_to_string = Solver.model_to_string

(** {1 Expression Analysis} *)

let get_all_symbols = Solver.get_all_symbols
let all_flat = Solver.all_flat

let simplify_disjunction clauses =
  (* Creates its own context, so thread-safe *)
  Solver.simplify_disjunction clauses

(** {1 Solver Introspection} *)

let get_statistics t = Solver.get_statistics t.solver

(** {1 Semantic Equality - Thread-Safe} *)

let exeq ?state e1 e2 =
  (* Creates its own context, so thread-safe *)
  Solver.exeq ?state e1 e2

let expoteq ?state e1 e2 =
  (* Creates its own context, so thread-safe *)
  Solver.expoteq ?state e1 e2

(** Thread-safe semantic equality module *)
module Semeq = struct
  (** Each state has its own underlying Solver.Semeq.state *)
  type state = Solver.Semeq.state

  let create_state () = Solver.Semeq.create_state ()
  let set_state state exprs = Solver.Semeq.set_state state exprs
  let exeq state e1 e2 = Solver.Semeq.exeq state e1 e2
  let expoteq state e1 e2 = Solver.Semeq.expoteq state e1 e2
  let expoteq_value state v1 v2 = Solver.Semeq.expoteq_value state v1 v2
end

(** Thread-safe cache module Note: Cache instances should not be shared between
    threads *)
module SemeqCache = struct
  type cache = Solver.SemeqCache.cache

  let create () = Solver.SemeqCache.create ()

  let exeq_cached cache ?state e1 e2 =
    Solver.SemeqCache.exeq_cached cache ?state e1 e2

  let expoteq_cached cache ?state e1 e2 =
    Solver.SemeqCache.expoteq_cached cache ?state e1 e2

  let clear cache = Solver.SemeqCache.clear cache
end

(** {1 Thread Pool Utilities} *)

module Pool = struct
  (** Partition a list into n roughly equal chunks *)
  let partition n lst =
    let len = List.length lst in
    let chunk_size = (len + n - 1) / n in
    let rec aux i acc remaining =
      if i >= n || remaining = [] then List.rev acc
      else
        let chunk = List.filteri (fun j _ -> j < chunk_size) remaining in
        let rest = List.filteri (fun j _ -> j >= chunk_size) remaining in
          aux (i + 1) (chunk :: acc) rest
    in
      aux 0 [] lst

  (** Execute parallel check operations *)
  let parallel_check n_threads tasks =
    let open Lwt.Infix in
    (* Partition tasks among threads *)
    let chunks = partition n_threads tasks in

    (* Process each chunk in a separate thread *)
    let process_chunk chunk =
      Lwt_list.map_s
        (fun exprs ->
          (* Each iteration creates its own solver with independent context *)
          quick_check exprs
        )
        chunk
    in

    (* Run all chunks in parallel and flatten results *)
    Lwt_list.map_p process_chunk chunks >|= List.flatten

  (** Execute parallel solve operations *)
  let parallel_solve n_threads tasks =
    let open Lwt.Infix in
    let chunks = partition n_threads tasks in

    let process_chunk chunk =
      Lwt_list.map_s
        (fun exprs ->
          (* Each iteration creates its own solver with independent context *)
          quick_solve exprs
        )
        chunk
    in

    Lwt_list.map_p process_chunk chunks >|= List.flatten

  (** Map a function over a list using parallel solver instances *)
  let parallel_map n_threads f items =
    let open Lwt.Infix in
    let chunks = partition n_threads items in

    let process_chunk chunk =
      Lwt_list.map_s
        (fun item ->
          (* Create a new solver instance for each item *)
          let solver = create_empty () in
            f solver item
        )
        chunk
    in

    Lwt_list.map_p process_chunk chunks >|= List.flatten
end
