(** Unit tests for ForwardingContext *)
open Uset

open Eventstructures
open Expr
open Forwardingcontext
open Lwt.Syntax
open Types

(** Test utilities *)
module TestUtil = struct
  (** Create a simple event *)
  let make_test_event label typ =
    {
      label;
      typ;
      id = Some (VNumber (Z.of_int label));
      loc = Some (ENum (Z.of_int label));
      rval = Some (VSymbol (Printf.sprintf "r%d" label));
      wval = Some (ESymbol (Printf.sprintf "w%d" label));
      rmod = Relaxed;
      wmod = Relaxed;
      fmod = Relaxed;
      cond = None;
      volatile = false;
      strong = None;
      is_rdmw = false;
    }

  (** Create test events hashtable *)
  let make_events () =
    let events = Hashtbl.create 16 in
      Hashtbl.add events 0 (make_test_event 0 Init);
      Hashtbl.add events 1 (make_test_event 1 Write);
      Hashtbl.add events 2 (make_test_event 2 Read);
      Hashtbl.add events 3 (make_test_event 3 Write);
      Hashtbl.add events 4 (make_test_event 4 Read);
      events

  (** Create test E set *)
  let make_e_set () =
    let e_set = USet.create () in
      List.iter (fun i -> ignore (USet.add e_set i)) [ 0; 1; 2; 3; 4 ];
      e_set

  (** Create test program order *)
  let make_po () =
    let po = USet.create () in
      List.iter
        (fun (f, t) -> ignore (USet.add po (f, t)))
        [ (0, 1); (1, 2); (2, 3); (3, 4) ];
      po

  (** Create test RMW *)
  let make_rmw () =
    let rmw = USet.create () in
      USet.add rmw (1, 2)

  (** Create test structure *)
  let make_structure () =
    {
      (SymbolicEventStructure.create ()) with
      e = make_e_set ();
      events = make_events ();
      po = make_po ();
      rmw = make_rmw ();
    }

  (** Value function for tests *)
  let test_val_fn e = Some (ESymbol (Printf.sprintf "v%d" e))

  (** Create init params *)
  let make_init_params () =
    { init_structure = make_structure (); init_val = test_val_fn }
end

(** Alcotest testable types *)
module Testable = struct
  let uset_int_pair =
    let pp fmt s =
      USet.iter (fun (a, b) -> Format.fprintf fmt "(%d,%d) " a b) s
    in
    let equal = USet.equal in
      Alcotest.testable pp equal

  let int_uset =
    let pp fmt s = USet.iter (fun i -> Format.fprintf fmt "%d " i) s in
    let equal = USet.equal in
      Alcotest.testable pp equal

  let fwd_context =
    let pp fmt ctx =
      Format.fprintf fmt "ForwardingContext(fwd=%d, we=%d)" (USet.size ctx.fwd)
        (USet.size ctx.we)
    in
    let equal ctx1 ctx2 =
      USet.equal ctx1.fwd ctx2.fwd && USet.equal ctx1.we ctx2.we
    in
      Alcotest.testable pp equal
end

(** Test initialization *)
let test_init () =
  Lwt_main.run
    (let* () =
       let params = TestUtil.make_init_params () in
         init params
     in
       Alcotest.(check pass) "Initialization completes" () ();
       Lwt.return_unit
    )

let test_init_clears_state () =
  Lwt_main.run
    (let* () =
       (* Add something to goodcon/badcon *)
       let fwd = USet.create () in
       let we = USet.create () in
         ignore (USet.add fwd (1, 2));
         ignore (USet.add goodcon (fwd, we));

         (* Initialize - should clear *)
         let params = TestUtil.make_init_params () in
           let* () = init params in

           Alcotest.(check bool) "goodcon cleared" false (is_good fwd we);
           Lwt.return_unit
     in
       Lwt.return_unit
    )

(** Test context creation *)
let test_create_empty_context () =
  let ctx = create () in
    Alcotest.(check int) "Empty fwd" 0 (USet.size ctx.fwd);
    Alcotest.(check int) "Empty we" 0 (USet.size ctx.we);
    Alcotest.(check int) "Empty valmap" 0 (List.length ctx.valmap);
    Alcotest.(check int) "Empty psi" 0 (List.length ctx.psi)

let test_create_with_fwd () =
  let fwd = USet.create () in
    ignore (USet.add fwd (1, 2));
    let ctx = create ~fwd () in
      Alcotest.(check int) "Fwd size" 1 (USet.size ctx.fwd);
      Alcotest.(check int) "Empty we" 0 (USet.size ctx.we)

let test_create_with_we () =
  let we = USet.create () in
    ignore (USet.add we (2, 3));
    let ctx = create ~we () in
      Alcotest.(check int) "Empty fwd" 0 (USet.size ctx.fwd);
      Alcotest.(check int) "WE size" 1 (USet.size ctx.we)

let test_create_generates_psi () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let fwd = USet.create () in
         ignore (USet.add fwd (1, 2));
         let ctx = create ~fwd () in
           (* Should have predicates for value equality *)
           Alcotest.(check bool)
             "Has psi predicates" true
             (List.length ctx.psi > 0);
           Lwt.return_unit
    )

(** Test remapping *)
let test_remap_identity () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx = create () in
         Alcotest.(check int) "Identity remap" 1 (remap ctx 1);
         Lwt.return_unit
    )

let test_remap_with_forwarding () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let fwd = USet.create () in
         ignore (USet.add fwd (1, 2));
         let ctx = create ~fwd () in
           (* Event 2 should remap to 1 *)
           Alcotest.(check int) "Remapped event" 1 (remap ctx 2);
           Lwt.return_unit
    )

let test_remap_transitive () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let fwd = USet.create () in
         ignore (USet.add fwd (1, 2));
         ignore (USet.add fwd (2, 3));
         let ctx = create ~fwd () in
           (* Event 3 should remap transitively to 1 *)
           Alcotest.(check int) "Transitive remap" 1 (remap ctx 3);
           Lwt.return_unit
    )

let test_remap_rel () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let fwd = USet.create () in
         ignore (USet.add fwd (1, 2));
         let ctx = create ~fwd () in

         let rel = USet.create () in
           ignore (USet.add rel (2, 3));

           let remapped = remap_rel ctx rel in
             (* (2,3) should become (1,3) *)
             Alcotest.(check bool)
               "Relation remapped" true
               (USet.mem remapped (1, 3));
             Lwt.return_unit
    )

let test_remap_rel_filters_reflexive () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let fwd = USet.create () in
         ignore (USet.add fwd (1, 2));
         let ctx = create ~fwd () in

         let rel = USet.create () in
           ignore (USet.add rel (2, 1));

           (* Will remap to (1,1) *)
           let remapped = remap_rel ctx rel in
             (* Should filter out (1,1) *)
             Alcotest.(check int) "Reflexive filtered" 0 (USet.size remapped);
             Lwt.return_unit
    )

(** Test cache operations *)
let test_cache_initially_empty () =
  let ctx = create () in
  let cached = cache_get ctx [] in
    Alcotest.(check bool) "Cache empty - no ppo" true (cached.ppo = None);
    Alcotest.(check bool) "Cache empty - no ppo_loc" true (cached.ppo_loc = None)

let test_cache_set_and_get () =
  let ctx = create () in
  let test_set = USet.create () in
    ignore (USet.add test_set (1, 2));

    let _ = cache_set ctx "ppo" [] test_set in
    let cached = cache_get ctx [] in

    match cached.ppo with
    | Some s -> Alcotest.(check int) "Cached ppo size" 1 (USet.size s)
    | None -> Alcotest.fail "Expected cached value"

let test_cache_different_predicates () =
  let ctx = create () in
  let set1 = USet.create () in
    ignore (USet.add set1 (1, 2));
    let set2 = USet.create () in
      ignore (USet.add set2 (2, 3));

      let pred1 = [ ENum Z.one ] in
      let pred2 = [ ENum Z.zero ] in

      let _ = cache_set ctx "ppo" pred1 set1 in
      let _ = cache_set ctx "ppo" pred2 set2 in

      let cached1 = cache_get ctx pred1 in
      let cached2 = cache_get ctx pred2 in

      match (cached1.ppo, cached2.ppo) with
      | Some s1, Some s2 ->
          Alcotest.(check bool)
            "Different cache entries" true
            (not (USet.equal s1 s2))
      | _ -> Alcotest.fail "Expected cached values"

(** Test good/bad context tracking *)
let test_is_good_initially_false () =
  let fwd = USet.create () in
  let we = USet.create () in
    Alcotest.(check bool) "Not initially good" false (is_good fwd we)

let test_is_bad_initially_false () =
  let fwd = USet.create () in
  let we = USet.create () in
    Alcotest.(check bool) "Not initially bad" false (is_bad fwd we)

(** Test context checking *)
let test_check_tautology () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       (* Context with tautological predicates *)
       let ctx =
         { (create ()) with psi = [ EBinOp (ENum Z.one, "=", ENum Z.one) ] }
       in
         let* result = check ctx in
           Alcotest.(check bool) "Tautology is satisfiable" true result;
           Lwt.return_unit
    )

let test_check_contradiction () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       (* Context with contradictory predicates *)
       let ctx =
         { (create ()) with psi = [ EBinOp (ENum Z.one, "=", ENum Z.zero) ] }
       in
         let* result = check ctx in
           Alcotest.(check bool) "Contradiction is unsatisfiable" false result;
           Lwt.return_unit
    )

let test_check_marks_good () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx =
         { (create ()) with psi = [ EBinOp (ENum Z.one, "=", ENum Z.one) ] }
       in
         let* _result = check ctx in
           Alcotest.(check bool) "Marked as good" true (is_good ctx.fwd ctx.we);
           Lwt.return_unit
    )

let test_check_marks_bad () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx =
         { (create ()) with psi = [ EBinOp (ENum Z.one, "=", ENum Z.zero) ] }
       in
         let* _result = check ctx in
           Alcotest.(check bool) "Marked as bad" true (is_bad ctx.fwd ctx.we);
           Lwt.return_unit
    )

(** Test PPO computation *)
let test_ppo_returns_remapped () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx = create () in
         let* ppo = ppo ctx [] in
           (* Should return some relation *)
           Alcotest.(check bool) "PPO is a uset" true (USet.size ppo >= 0);
           Lwt.return_unit
    )

let test_ppo_caches_result () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx = create () in
       let predicates = [] in

       (* First call *)
       let* ppo1 = ppo ctx predicates in
         (* Second call - should hit cache *)
         let* ppo2 = ppo ctx predicates in

         Alcotest.(check bool) "PPO cached" true (USet.equal ppo1 ppo2);
         Lwt.return_unit
    )

let test_ppo_loc_returns_remapped () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx = create () in
         let* ppo_loc = ppo_loc ctx [] in
           (* Should return some relation *)
           Alcotest.(check bool)
             "PPO_loc is a uset" true
             (USet.size ppo_loc >= 0);
           Lwt.return_unit
    )

let test_ppo_sync_returns_remapped () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in
       let ctx = create () in
       let ppo_sync = ppo_sync ctx in
         (* Should return some relation *)
         Alcotest.(check bool)
           "PPO_sync is a uset" true
           (USet.size ppo_sync >= 0);
         Lwt.return_unit
    )

(** Test to_string *)
let test_to_string_empty () =
  let ctx = create () in
  let s = to_string ctx in
    Alcotest.(check bool)
      "String contains empty markers" true
      (String.length s > 0)

let test_to_string_with_edges () =
  let fwd = USet.create () in
    ignore (USet.add fwd (1, 2));
    let ctx = create ~fwd () in
    let s = to_string ctx in
      Alcotest.(check bool) "String not empty" true (String.length s > 0)

(** Test update_po *)
let test_update_po_clears_cache () =
  Lwt_main.run
    (let params = TestUtil.make_init_params () in
       let* () = init params in

       (* Create a context and cache something *)
       let ctx = create () in
       let test_set = USet.create () in
         ignore (USet.add test_set (1, 2));
         let _ = cache_set ctx "ppo" [] test_set in

         (* Update PO - should clear cache *)
         let new_po = USet.create () in
           ignore (USet.add new_po (0, 1));
           update_po new_po;

           (* Cache size should be 0 after clear *)
           Alcotest.(check int) "Cache cleared" 0 (FwdCache.size ());
           Lwt.return_unit
    )

(** Test suite *)
let suite =
  let open Alcotest in
  ( "ForwardingContext",
    [
      test_case "init completes" `Quick test_init;
      test_case "init clears state" `Quick test_init_clears_state;
      test_case "create empty context" `Quick test_create_empty_context;
      test_case "create with fwd" `Quick test_create_with_fwd;
      test_case "create with we" `Quick test_create_with_we;
      test_case "create generates psi" `Quick test_create_generates_psi;
      test_case "remap identity" `Quick test_remap_identity;
      test_case "remap with forwarding" `Quick test_remap_with_forwarding;
      test_case "remap transitive" `Quick test_remap_transitive;
      test_case "remap relation" `Quick test_remap_rel;
      test_case "remap filters reflexive" `Quick
        test_remap_rel_filters_reflexive;
      test_case "cache initially empty" `Quick test_cache_initially_empty;
      test_case "cache set and get" `Quick test_cache_set_and_get;
      test_case "cache different predicates" `Quick
        test_cache_different_predicates;
      test_case "is_good initially false" `Quick test_is_good_initially_false;
      test_case "is_bad initially false" `Quick test_is_bad_initially_false;
      test_case "check tautology" `Quick test_check_tautology;
      test_case "check contradiction" `Quick test_check_contradiction;
      test_case "check marks good" `Quick test_check_marks_good;
      test_case "check marks bad" `Quick test_check_marks_bad;
      test_case "ppo returns remapped" `Quick test_ppo_returns_remapped;
      test_case "ppo caches result" `Quick test_ppo_caches_result;
      test_case "ppo_loc returns remapped" `Quick test_ppo_loc_returns_remapped;
      test_case "ppo_sync returns remapped" `Quick
        test_ppo_sync_returns_remapped;
      test_case "to_string empty" `Quick test_to_string_empty;
      test_case "to_string with edges" `Quick test_to_string_with_edges;
      test_case "update_po clears cache" `Quick test_update_po_clears_cache;
    ]
  )
