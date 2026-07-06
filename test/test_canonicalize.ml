open Alcotest
open Eventstructures
open Types
open Uset

(** Unit tests for {!Canonicalize} (S9 / R1). These pin the two properties the
    equivalence methodology relies on:
    - canonical form is independent of execution [id] and of the order in which
      relation pairs were inserted;
    - genuinely different executions produce different canonical forms. *)

module TestData = struct
  let make_event ?(label = 0) ?(typ = Read) ?id ?loc ?rval ?wval ?cond
      ?(rmod = Relaxed) ?(wmod = Relaxed) ?(fmod = Relaxed) ?(volatile = false)
      ?(is_rdmw = false) () : event =
    {
      label;
      typ;
      id;
      loc;
      rval;
      wval;
      cond;
      rmod;
      wmod;
      fmod;
      volatile;
      strong = None;
      is_rdmw;
    }

  (* init (thread 0), write x (thread 1), read x (thread 1). *)
  let make_structure () =
    let s = SymbolicEventStructure.create () in
    let e0 = make_event ~label:0 ~typ:Init () in
    let e1 =
      make_event ~label:1 ~typ:Write ~loc:(EVar "x") ~wval:(ENum (Z.of_int 1)) ()
    in
    let e2 =
      make_event ~label:2 ~typ:Read ~loc:(EVar "x") ~rval:(VSymbol "a") ()
    in
      Hashtbl.add s.events 0 e0;
      Hashtbl.add s.events 1 e1;
      Hashtbl.add s.events 2 e2;
      Hashtbl.add s.thread_index 0 0;
      Hashtbl.add s.thread_index 1 1;
      Hashtbl.add s.thread_index 2 1;
      { s with e = USet.of_list [ 0; 1; 2 ]; po = USet.of_list [ (1, 2) ] }

  let make_execution ?(id = 0) ?(rf = USet.of_list [ (1, 2) ])
      ?(ppo = USet.of_list [ (1, 2) ]) () : symbolic_execution =
    {
      id;
      e = USet.of_list [ 0; 1; 2 ];
      rf;
      dp = USet.create ();
      ppo;
      rmw = USet.create ();
      ex_p = [];
      fix_rf_map = Hashtbl.create 0;
      pointer_map = None;
      final_env = Hashtbl.create 0;
    }
end

open TestData

let sig_of s e =
  Canonicalize.signature ~with_predicates:true (Canonicalize.canonicalize s e)

(* Same execution content, different [id] -> identical canonical signature. *)
let test_id_independent () =
  let s = make_structure () in
  let a = make_execution ~id:0 () in
  let b = make_execution ~id:999 () in
    check string "id must not affect canonical form" (sig_of s a) (sig_of s b)

(* Same relations, different pair insertion order -> identical signature. *)
let test_order_independent () =
  let s = make_structure () in
  let a = make_execution ~ppo:(USet.of_list [ (0, 1); (1, 2) ]) () in
  let b = make_execution ~ppo:(USet.of_list [ (1, 2); (0, 1) ]) () in
    check string "pair insertion order must not affect canonical form"
      (sig_of s a) (sig_of s b)

(* Different rf -> different canonical signature (no false collapse). *)
let test_distinguishes () =
  let s = make_structure () in
  let a = make_execution ~rf:(USet.of_list [ (1, 2) ]) () in
  let b = make_execution ~rf:(USet.of_list [ (0, 2) ]) () in
    if String.equal (sig_of s a) (sig_of s b) then
      fail "distinct rf relations must not canonicalize to the same form"

(* A whole set is invariant under reordering of the executions within it. *)
let test_set_order_independent () =
  let s = make_structure () in
  let e_from_write = make_execution ~id:1 ~rf:(USet.of_list [ (1, 2) ]) () in
  let e_from_init = make_execution ~id:2 ~rf:(USet.of_list [ (0, 2) ]) () in
  let set1 = Canonicalize.canonicalize_set s [ e_from_write; e_from_init ] in
  let set2 = Canonicalize.canonicalize_set s [ e_from_init; e_from_write ] in
    check bool "execution-set canonical form is order-independent" true
      (Canonicalize.equal_sets ~with_predicates:true set1 set2)

let suite =
  ( "Canonicalize",
    [
      test_case "id independence" `Quick test_id_independent;
      test_case "pair-order independence" `Quick test_order_independent;
      test_case "distinguishes different rf" `Quick test_distinguishes;
      test_case "set order independence" `Quick test_set_order_independent;
    ] )
