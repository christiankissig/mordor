(** Coherence checking for memory models *)

open Types
open Executions

(** Cache type for IMM coherence checking *)
type imm_cache = {
  hb : (int * int) uset;
  rf : (int * int) uset;
  rfi : (int * int) uset;
  ar_ : (int * int) uset;
  ex_e : int uset;
  po : (int * int) uset;
  events : (int, event) Hashtbl.t;
  psc_a : (int * int) uset;
  psc_b : (int * int) uset;
  restrict : (int, expr list) Hashtbl.t;
  rmw : (int * int) uset;
  loc_restrict : (int * int) uset -> (int * int) uset;
}

(** Cache type for RC11 coherence checking *)
type rc11_cache = {
  sb : (int * int) uset;
  hb : (int * int) uset;
  rfi : (int * int) uset;
  rf : (int * int) uset;
  ex_e : int uset;
  events : (int, event) Hashtbl.t;
  rmw : (int * int) uset;
  loc_restrict : (int * int) uset -> (int * int) uset;
}

(** Generic cache type *)
type cache =
  | IMMCache of imm_cache
  | RC11Cache of rc11_cache
  | UndefinedCache of {
      rfi : (int * int) uset option;
      rmw : (int * int) uset option;
    }
  | EmptyCache

(** Restrictions configuration *)
type restrictions = { coherent : string }

(** Helper function to create event identity relation *)
val em :
  (int, event) Hashtbl.t ->
  int uset ->
  event_type ->
  mode option ->
  string option ->
  mode option ->
  (int * int) uset

(** Semicolon relation composition *)
val semicolon_rel : (int * int) uset list -> (int * int) uset

(** Generate all permutations of a list *)
val permutations : 'a list -> 'a list list

(** IMM coherence cache builder *)
val imm_coherent_cache :
  symbolic_execution ->
  symbolic_event_structure ->
  (int, event) Hashtbl.t ->
  ((int * int) uset -> (int * int) uset) ->
  imm_cache

(** IMM coherence checker *)
val imm_coherent : (int * int) uset -> imm_cache -> bool

(** RC11 coherence cache builder *)
val rc11_coherent_cache :
  symbolic_execution ->
  symbolic_event_structure ->
  (int, event) Hashtbl.t ->
  ((int * int) uset -> (int * int) uset) ->
  rc11_cache

(** RC11 coherence checker *)
val rc11_coherent : (int * int) uset -> rc11_cache -> bool

(** IMM dependency calculation *)
val imm_deps :
  symbolic_execution ->
  (int, event) Hashtbl.t ->
  (int * int) uset ->
  int uset ->
  (int, expr list) Hashtbl.t ->
  (int * int) uset

(** Main coherence checking function *)
val check_for_coherence :
  symbolic_event_structure ->
  (int, event) Hashtbl.t ->
  symbolic_execution ->
  restrictions ->
  bool ->
  bool Lwt.t
