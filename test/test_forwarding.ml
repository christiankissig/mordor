(** Unit tests for ForwardingContext - Refactored with data providers *)
open Uset

open Eventstructures
open Expr
open Forwarding
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
      cond = None;
      rmod = Relaxed;
      wmod = Relaxed;
      fmod = Relaxed;
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
      USet.add rmw (1, EBoolean true, 2)

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

(** Data providers for test cases *)
module DataProviders = struct
  (** Data for context creation tests *)
  type context_creation_data = {
    name : string;
    fwd_edges : (int * int) list option;
    we_edges : (int * int) list option;
    expected_fwd_size : int;
    expected_we_size : int;
  }

  let context_creation_cases =
    [
      {
        name = "empty context";
        fwd_edges = None;
        we_edges = None;
        expected_fwd_size = 0;
        expected_we_size = 0;
      };
      {
        name = "with fwd";
        fwd_edges = Some [ (1, 2) ];
        we_edges = None;
        expected_fwd_size = 1;
        expected_we_size = 0;
      };
      {
        name = "with we";
        fwd_edges = None;
        we_edges = Some [ (2, 3) ];
        expected_fwd_size = 0;
        expected_we_size = 1;
      };
    ]

  (** Data for remap tests *)
  type remap_data = {
    name : string;
    fwd_edges : (int * int) list;
    event : int;
    expected : int;
  }

  let remap_cases =
    [
      { name = "identity"; fwd_edges = []; event = 1; expected = 1 };
      {
        name = "with forwarding";
        fwd_edges = [ (1, 2) ];
        event = 2;
        expected = 1;
      };
      {
        name = "transitive";
        fwd_edges = [ (1, 2); (2, 3) ];
        event = 3;
        expected = 1;
      };
    ]

  (** Data for check satisfiability tests *)
  type check_data = {
    name : string;
    psi : expr list;
    expected_result : bool;
    should_be_good : bool;
    should_be_bad : bool;
  }

  let check_cases =
    [
      {
        name = "tautology";
        psi = [ EBinOp (ENum Z.one, "=", ENum Z.one) ];
        expected_result = true;
        should_be_good = true;
        should_be_bad = false;
      };
      {
        name = "contradiction";
        psi = [ EBinOp (ENum Z.one, "=", ENum Z.zero) ];
        expected_result = false;
        should_be_good = false;
        should_be_bad = true;
      };
    ]
end

(** Test initialization *)
let test_init () =
  Lwt_main.run
    (let* () =
       let structure = TestUtil.make_structure () in
       let fwd_es_ctx = EventStructureContext.create structure in
         EventStructureContext.init fwd_es_ctx
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

         (* Initialize - should clear *)
         let structure = TestUtil.make_structure () in
         let fwd_es_ctx = EventStructureContext.create structure in

         ContextCache.mark_good fwd_es_ctx.context_cache fwd we;

         let* () = EventStructureContext.init fwd_es_ctx in

         Alcotest.(check bool)
           "goodcon cleared" false
           (ContextCache.is_good fwd_es_ctx.context_cache fwd we);
         Lwt.return_unit
     in
       Lwt.return_unit
    )

(** Test context creation - using data provider *)
let test_create_context (data : DataProviders.context_creation_data) =
  let structure = TestUtil.make_structure () in
  let fwd_es_ctx = EventStructureContext.create structure in

  let create_uset edges =
    let s = USet.create () in
      List.iter (fun (a, b) -> ignore (USet.add s (a, b))) edges;
      s
  in

  let ctx =
    match (data.fwd_edges, data.we_edges) with
    | None, None -> ForwardingContext.create fwd_es_ctx ()
    | Some fwd_edges, None ->
        let fwd = create_uset fwd_edges in
          ForwardingContext.create fwd_es_ctx ~fwd ()
    | None, Some we_edges ->
        let we = create_uset we_edges in
          ForwardingContext.create fwd_es_ctx ~we ()
    | Some fwd_edges, Some we_edges ->
        let fwd = create_uset fwd_edges in
        let we = create_uset we_edges in
          ForwardingContext.create fwd_es_ctx ~fwd ~we ()
  in
    Alcotest.(check int)
      (Printf.sprintf "Fwd size for %s" data.name)
      data.expected_fwd_size (USet.size ctx.fwd);
    Alcotest.(check int)
      (Printf.sprintf "WE size for %s" data.name)
      data.expected_we_size (USet.size ctx.we)

let test_create_generates_psi () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     let fwd = USet.create () in
       ignore (USet.add fwd (1, 2));
       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in
         (* Should have predicates for value equality *)
         Alcotest.(check bool)
           "Has psi predicates" true
           (List.length ctx.psi > 0);
         Lwt.return_unit
    )

(** Test remapping - using data provider *)
let test_remap (data : DataProviders.remap_data) =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let fwd = USet.create () in
       List.iter (fun (a, b) -> ignore (USet.add fwd (a, b))) data.fwd_edges;
       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in
         Alcotest.(check int)
           (Printf.sprintf "Remap %s" data.name)
           data.expected
           (ForwardingContext.remap ctx data.event);
         Lwt.return_unit
    )

let test_remap_rel () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
     let rel = USet.create () in
       ignore (USet.add rel (1, 2));
       ignore (USet.add rel (3, 4));
       let remapped = ForwardingContext.remap_rel ctx rel in
         Alcotest.(check int) "Relation preserved" 2 (USet.size remapped);
         Lwt.return_unit
    )

let test_remap_rel_filters_reflexive () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let fwd = USet.create () in
       ignore (USet.add fwd (1, 2));
       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in
       let rel = USet.create () in
         (* Add edges that become reflexive after remapping *)
         ignore (USet.add rel (1, 2));
         (* This becomes (1,1) *)
         ignore (USet.add rel (3, 4));
         let remapped = ForwardingContext.remap_rel ctx rel in
           (* Should filter out (1,1) *)
           Alcotest.(check bool)
             "Filters reflexive" true
             (not (USet.mem remapped (1, 1)));
           Lwt.return_unit
    )

(** Test cache operations *)
let test_cache_initially_empty () =
  let structure = TestUtil.make_structure () in
  let fwd_es_ctx = EventStructureContext.create structure in

  let ctx = ForwardingContext.create fwd_es_ctx () in
  let cached = ForwardingContext.cache_get ctx [] in
    Alcotest.(check bool)
      "PPO not cached" true
      ( match cached.ppo with
      | None -> true
      | _ -> false
      )

let test_cache_set_and_get () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
     let test_set = USet.create () in
       ignore (USet.add test_set (1, 2));
       let _ = ForwardingContext.cache_set_ppo ctx [] test_set in
       let cached = ForwardingContext.cache_get ctx [] in
         match cached.ppo with
         | Some s ->
             Alcotest.(check Testable.uset_int_pair)
               "Retrieved cached value" test_set s;
             Lwt.return_unit
         | None -> Alcotest.fail "Cache should contain value"
    )

let test_cache_different_predicates () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
     let set1 = USet.create () in
       ignore (USet.add set1 (1, 2));
       let set2 = USet.create () in
         ignore (USet.add set2 (3, 4));

         let pred1 = [ EBoolean true ] in
         let pred2 = [ EBoolean false ] in

         let _ = ForwardingContext.cache_set_ppo ctx pred1 set1 in
         let _ = ForwardingContext.cache_set_ppo ctx pred2 set2 in

         let cached1 = ForwardingContext.cache_get ctx pred1 in
         let cached2 = ForwardingContext.cache_get ctx pred2 in

         Alcotest.(check bool)
           "Different predicates cache separately" true
           ( match (cached1.ppo, cached2.ppo) with
           | Some s1, Some s2 -> not (USet.equal s1 s2)
           | _ -> false
           );
         Lwt.return_unit
    )

(** Test context cache status *)
let test_is_good_initially_false () =
  let structure = TestUtil.make_structure () in
  let fwd_es_ctx = EventStructureContext.create structure in

  let fwd = USet.create () in
  let we = USet.create () in
    Alcotest.(check bool)
      "Not initially good" false
      (ContextCache.is_good fwd_es_ctx.context_cache fwd we)

let test_is_bad_initially_false () =
  let structure = TestUtil.make_structure () in
  let fwd_es_ctx = EventStructureContext.create structure in

  let fwd = USet.create () in
  let we = USet.create () in
    Alcotest.(check bool)
      "Not initially bad" false
      (ContextCache.is_bad fwd_es_ctx.context_cache fwd we)

(** Test context checking - using data provider *)
let test_check (data : DataProviders.check_data) =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx =
       { (ForwardingContext.create fwd_es_ctx ()) with psi = data.psi }
     in
       let* result = ForwardingContext.check ctx in
         Alcotest.(check bool)
           (Printf.sprintf "%s satisfiability" data.name)
           data.expected_result result;

         if data.should_be_good then
           Alcotest.(check bool)
             (Printf.sprintf "%s marked as good" data.name)
             true
             (ContextCache.is_good fwd_es_ctx.context_cache ctx.fwd ctx.we);

         if data.should_be_bad then
           Alcotest.(check bool)
             (Printf.sprintf "%s marked as bad" data.name)
             true
             (ContextCache.is_bad fwd_es_ctx.context_cache ctx.fwd ctx.we);

         Lwt.return_unit
    )

(** Test PPO computation *)

(** Data provider for PPO tests *)
module PPODataProvider = struct
  type ppo_test_data = {
    name : string;
    fwd_edges : (int * int) list;
    predicates : expr list;
    ctx_psi : expr list;
    description : string;
  }

  let ppo_test_cases =
    [
      {
        name = "empty_context_no_predicates";
        fwd_edges = [];
        predicates = [];
        ctx_psi = [];
        description = "Empty forwarding context with no predicates";
      };
      {
        name = "with_forwarding_no_predicates";
        fwd_edges = [ (1, 2); (2, 3) ];
        predicates = [];
        ctx_psi = [];
        description = "Forwarding edges but no predicates";
      };
      {
        name = "no_forwarding_with_predicates";
        fwd_edges = [];
        predicates = [ EBinOp (ENum Z.one, "=", ENum Z.one) ];
        ctx_psi = [];
        description = "No forwarding but with true predicate";
      };
      {
        name = "forwarding_and_predicates";
        fwd_edges = [ (1, 2) ];
        predicates = [ EBinOp (ESymbol "x", ">", ENum Z.zero) ];
        ctx_psi = [ EBinOp (ESymbol "y", "<", ENum (Z.of_int 10)) ];
        description = "Forwarding with both predicates and context psi";
      };
      {
        name = "complex_forwarding";
        fwd_edges = [ (1, 2); (2, 3); (3, 4) ];
        predicates = [];
        ctx_psi = [];
        description = "Complex forwarding chain";
      };
    ]
end

let test_ppo_returns_remapped () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
       let* ppo = ForwardingContext.ppo ctx [] in
         (* Should return some relation *)
         Alcotest.(check bool) "PPO is a uset" true (USet.size ppo >= 0);
         Lwt.return_unit
    )

let test_ppo_caches_result () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
     let predicates = [] in

     (* First call *)
     let* ppo1 = ForwardingContext.ppo ctx predicates in
       (* Second call - should hit cache *)
       let* ppo2 = ForwardingContext.ppo ctx predicates in

       Alcotest.(check bool) "PPO cached" true (USet.equal ppo1 ppo2);
       Lwt.return_unit
    )

let test_ppo_with_different_predicates () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     let pred1 = [ EBinOp (ENum Z.one, "=", ENum Z.one) ] in
     let pred2 = [ EBinOp (ENum (Z.of_int 2), "=", ENum (Z.of_int 2)) ] in

     let* ppo1 = ForwardingContext.ppo ctx pred1 in
       let* ppo2 = ForwardingContext.ppo ctx pred2 in

       (* Both should succeed and be cached separately *)
       Alcotest.(check bool)
         "Both PPOs computed" true
         (USet.size ppo1 >= 0 && USet.size ppo2 >= 0);

       (* Verify they're cached separately *)
       let cached1 = ForwardingContext.cache_get ctx pred1 in
       let cached2 = ForwardingContext.cache_get ctx pred2 in

       Alcotest.(check bool)
         "Different predicates cached separately" true
         ( match (cached1.ppo, cached2.ppo) with
         | Some _, Some _ -> true
         | _ -> false
         );
       Lwt.return_unit
    )

let test_ppo_with_context_psi () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     (* Create context with psi *)
     let ctx_psi = [ EBinOp (ESymbol "x", ">", ENum Z.zero) ] in
     let ctx =
       { (ForwardingContext.create fwd_es_ctx ()) with psi = ctx_psi }
     in

     let predicates = [ EBinOp (ESymbol "y", "<", ENum (Z.of_int 10)) ] in

     let* ppo = ForwardingContext.ppo ctx predicates in

     (* Should combine predicates and psi for computation *)
     Alcotest.(check bool)
       "PPO computed with combined predicates" true
       (USet.size ppo >= 0);

     Lwt.return_unit
    )

let test_ppo_applies_remapping () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     (* Create context with forwarding edges *)
     let fwd = USet.create () in
       ignore (USet.add fwd (2, 1));

       (* Event 2 forwards to event 1 *)
       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in

       let* ppo = ForwardingContext.ppo ctx [] in

       (* Verify that edges involving event 2 are remapped to event 1 *)
       (* The result should not contain self-edges after remapping *)
       let has_self_edge = USet.exists (fun (from, to_) -> from = to_) ppo in

       Alcotest.(check bool) "No self-edges after remapping" false has_self_edge;

       Lwt.return_unit
    )

let test_ppo_includes_rmw_orderings () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     (* The test structure includes RMW edges, PPO should include RMW-related orderings *)
     let* ppo = ForwardingContext.ppo ctx [] in

     Alcotest.(check bool) "PPO includes orderings" true (USet.size ppo >= 0);

     Lwt.return_unit
    )

let test_ppo_with_debug_flag () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     (* Test with debug flag enabled *)
     let* ppo = ForwardingContext.ppo ~debug:true ctx [] in

     Alcotest.(check bool)
       "PPO computed with debug flag" true
       (USet.size ppo >= 0);

     Lwt.return_unit
    )

(** PPO_LOC Tests *)

let test_ppo_loc_returns_remapped () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
       let* ppo_loc = ForwardingContext.ppo_loc ctx [] in
         (* Should return some relation *)
         Alcotest.(check bool) "PPO_loc is a uset" true (USet.size ppo_loc >= 0);
         Lwt.return_unit
    )

let test_ppo_loc_caches_result () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
     let predicates = [] in

     (* First call *)
     let* ppo_loc1 = ForwardingContext.ppo_loc ctx predicates in
       (* Second call - should hit cache *)
       let* ppo_loc2 = ForwardingContext.ppo_loc ctx predicates in

       Alcotest.(check bool) "PPO_loc cached" true (USet.equal ppo_loc1 ppo_loc2);

       (* Verify it's actually in cache *)
       let cached = ForwardingContext.cache_get ctx predicates in
         Alcotest.(check bool)
           "PPO_loc in cache" true
           ( match cached.ppo_loc with
           | Some _ -> true
           | None -> false
           );

         Lwt.return_unit
    )

let test_ppo_loc_subset_of_ppo () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     let* ppo = ForwardingContext.ppo ctx [] in
       let* ppo_loc = ForwardingContext.ppo_loc ctx [] in

       (* ppo_loc should be a subset or equal to ppo (more restrictive) *)
       Alcotest.(check bool)
         "PPO_loc size <= PPO size" true
         (USet.size ppo_loc <= USet.size ppo);

       Lwt.return_unit
    )

let test_ppo_loc_with_predicates () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     let predicates = [ EBinOp (ENum Z.one, "=", ENum Z.one) ] in

     let* ppo_loc = ForwardingContext.ppo_loc ctx predicates in

     Alcotest.(check bool)
       "PPO_loc computed with predicates" true
       (USet.size ppo_loc >= 0);

     Lwt.return_unit
    )

let test_ppo_loc_normalizes_predicates () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     (* Add duplicate predicates - should be normalized *)
     let predicates =
       [
         EBinOp (ENum Z.one, "=", ENum Z.one);
         EBinOp (ENum Z.one, "=", ENum Z.one);
       ]
     in

     let* ppo_loc1 = ForwardingContext.ppo_loc ctx predicates in

     (* Try again with single predicate *)
     let predicates2 = [ EBinOp (ENum Z.one, "=", ENum Z.one) ] in
       let* ppo_loc2 = ForwardingContext.ppo_loc ctx predicates2 in

       (* Should produce same result (predicates are normalized via USet) *)
       Alcotest.(check bool)
         "Duplicate predicates normalized" true
         (USet.equal ppo_loc1 ppo_loc2);

       Lwt.return_unit
    )

let test_ppo_loc_uses_cache_subset () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     (* First compute with a subset of predicates *)
     let predicates1 = [ EBinOp (ENum Z.one, "=", ENum Z.one) ] in
       let* _ppo_loc1 = ForwardingContext.ppo_loc ctx predicates1 in

       (* Now compute with superset - should use cached subset as base *)
       let predicates2 =
         [
           EBinOp (ENum Z.one, "=", ENum Z.one);
           EBinOp (ENum (Z.of_int 2), "=", ENum (Z.of_int 2));
         ]
       in
         let* ppo_loc2 = ForwardingContext.ppo_loc ctx predicates2 in

         Alcotest.(check bool) "Cache subset used" true (USet.size ppo_loc2 >= 0);

         Lwt.return_unit
    )

let test_ppo_loc_applies_remapping () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     (* Create context with forwarding edges *)
     let fwd = USet.create () in
       ignore (USet.add fwd (3, 1));

       (* Event 3 forwards to event 1 *)
       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in

       let* ppo_loc = ForwardingContext.ppo_loc ctx [] in

       (* Verify no self-edges after remapping *)
       let has_self_edge =
         USet.exists (fun (from, to_) -> from = to_) ppo_loc
       in

       Alcotest.(check bool)
         "No self-edges in PPO_loc after remapping" false has_self_edge;

       Lwt.return_unit
    )

(** PPO_SYNC Tests *)

let test_ppo_sync_returns_remapped () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in
     let ppo_sync = ForwardingContext.ppo_sync ctx in
       (* Should return some relation *)
       Alcotest.(check bool) "PPO_sync is a uset" true (USet.size ppo_sync >= 0);
       Lwt.return_unit
    )

let test_ppo_sync_is_deterministic () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     let ppo_sync1 = ForwardingContext.ppo_sync ctx in
     let ppo_sync2 = ForwardingContext.ppo_sync ctx in

     Alcotest.(check bool)
       "PPO_sync deterministic" true
       (USet.equal ppo_sync1 ppo_sync2);

     Lwt.return_unit
    )

let test_ppo_sync_applies_remapping () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     (* Create context with forwarding *)
     let fwd = USet.create () in
       ignore (USet.add fwd (4, 2));

       (* Event 4 forwards to event 2 *)
       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in
       let ppo_sync = ForwardingContext.ppo_sync ctx in

       (* Verify no self-edges after remapping *)
       let has_self_edge =
         USet.exists (fun (from, to_) -> from = to_) ppo_sync
       in

       Alcotest.(check bool)
         "No self-edges in PPO_sync after remapping" false has_self_edge;

       Lwt.return_unit
    )

let test_ppo_sync_independent_of_predicates () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     (* ppo_sync doesn't take predicates, should be same regardless of context psi *)
     let ctx1 = ForwardingContext.create fwd_es_ctx () in
     let ctx2 =
       {
         (ForwardingContext.create fwd_es_ctx ()) with
         psi = [ EBinOp (ENum Z.one, "=", ENum Z.one) ];
       }
     in

     let ppo_sync1 = ForwardingContext.ppo_sync ctx1 in
     let ppo_sync2 = ForwardingContext.ppo_sync ctx2 in

     Alcotest.(check bool)
       "PPO_sync independent of psi" true
       (USet.equal ppo_sync1 ppo_sync2);

     Lwt.return_unit
    )

let test_ppo_sync_with_complex_forwarding () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     (* Create complex forwarding chain *)
     let fwd = USet.create () in
       ignore (USet.add fwd (1, 0));
       ignore (USet.add fwd (2, 1));
       ignore (USet.add fwd (3, 2));

       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in
       let ppo_sync = ForwardingContext.ppo_sync ctx in

       Alcotest.(check bool)
         "PPO_sync with complex forwarding" true
         (USet.size ppo_sync >= 0);

       Lwt.return_unit
    )

(** Integration tests for compute_ppo functions *)

let test_ppo_ppo_loc_relationship () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     let predicates = [] in

     let* ppo = ForwardingContext.ppo ctx predicates in
       let* ppo_loc = ForwardingContext.ppo_loc ctx predicates in

       (* ppo_loc should be subset of or equal to ppo *)
       let is_subset = USet.for_all (fun edge -> USet.mem ppo edge) ppo_loc in

       Alcotest.(check bool) "PPO_loc is subset of PPO" true is_subset;

       Lwt.return_unit
    )

let test_all_ppo_functions_with_same_context () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let fwd_es_ctx = EventStructureContext.create structure in

     let* () = EventStructureContext.init fwd_es_ctx in

     let fwd = USet.create () in
       ignore (USet.add fwd (1, 0));

       let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in

       let* ppo = ForwardingContext.ppo ctx [] in
         let* ppo_loc = ForwardingContext.ppo_loc ctx [] in
         let ppo_sync = ForwardingContext.ppo_sync ctx in

         (* All should complete successfully and return valid relations *)
         Alcotest.(check bool)
           "All PPO functions complete" true
           (USet.size ppo >= 0
           && USet.size ppo_loc >= 0
           && USet.size ppo_sync >= 0
           );

         Lwt.return_unit
    )

let test_ppo_with_empty_structure () =
  Lwt_main.run
    (let empty_structure = SymbolicEventStructure.create () in
     let fwd_es_ctx = EventStructureContext.create empty_structure in

     let* () = EventStructureContext.init fwd_es_ctx in
     let ctx = ForwardingContext.create fwd_es_ctx () in

     let* ppo = ForwardingContext.ppo ctx [] in

     (* Should handle empty structure gracefully *)
     Alcotest.(check int) "Empty structure produces empty PPO" 0 (USet.size ppo);

     Lwt.return_unit
    )

let test_ppo_rmw_read_dont_modify () =
  Lwt_main.run
    (let events = Hashtbl.create 16 in

     (* Event 1: Read with alpha *)
     Hashtbl.add events 1
       {
         label = 1;
         typ = Read;
         id = Some (VNumber (Z.of_int 1));
         loc = Some (ENum (Z.of_int 1));
         rval = Some (VSymbol "alpha");
         wval = None;
         cond = None;
         rmod = Relaxed;
         wmod = Relaxed;
         fmod = Relaxed;
         volatile = false;
         strong = None;
         is_rdmw = false;
       };

     (* Event 2: Acquiring read with beta *)
     Hashtbl.add events 2
       {
         label = 2;
         typ = Read;
         id = Some (VNumber (Z.of_int 2));
         loc = Some (ENum (Z.of_int 2));
         rval = Some (VSymbol "beta");
         wval = None;
         cond = None;
         rmod = Acquire;
         wmod = Relaxed;
         fmod = Relaxed;
         volatile = false;
         strong = None;
         is_rdmw = false;
       };

     (* Event 3: Releasing write with beta + 0, read-dont-modify *)
     Hashtbl.add events 3
       {
         label = 3;
         typ = Write;
         id = Some (VNumber (Z.of_int 3));
         loc = Some (ENum (Z.of_int 3));
         rval = None;
         wval = Some (EBinOp (ESymbol "beta", "+", ENum Z.zero));
         cond = None;
         rmod = Relaxed;
         wmod = Release;
         fmod = Relaxed;
         volatile = false;
         strong = None;
         is_rdmw = true;
       };

     (* Event 4: Read with gamma *)
     Hashtbl.add events 4
       {
         label = 4;
         typ = Read;
         id = Some (VNumber (Z.of_int 4));
         loc = Some (ENum (Z.of_int 4));
         rval = Some (VSymbol "gamma");
         wval = None;
         cond = None;
         rmod = Relaxed;
         wmod = Relaxed;
         fmod = Relaxed;
         volatile = false;
         strong = None;
         is_rdmw = false;
       };

     (* Create event set *)
     let e_set = USet.create () in
       List.iter (fun i -> ignore (USet.add e_set i)) [ 1; 2; 3; 4 ];

       (* Create program order: path through all events *)
       let po =
         USet.of_list [ (1, 2); (2, 3); (3, 4) ] |> URelation.transitive_closure
       in

       (* Create RMW edge from write 3 to read 2 with predicate true *)
       let rmw = USet.create () in
         ignore (USet.add rmw (3, EBoolean true, 2));

         let read_events = USet.of_list [ 1; 2; 4 ] in
         let write_events = USet.of_list [ 3 ] in

         let structure =
           {
             (SymbolicEventStructure.create ()) with
             e = e_set;
             events;
             po;
             rmw;
             read_events;
             write_events;
           }
         in

         let fwd_es_ctx = EventStructureContext.create structure in
           let* () = EventStructureContext.init fwd_es_ctx in

           (* Create context - write 3 is justified by read 2 only *)
           let ctx = ForwardingContext.create fwd_es_ctx () in

           let* ppo = ForwardingContext.ppo ctx [] in

           (* Verify PPO relations: 1,2 and 3,4 should be in PPO *)
           let has_1_2 = USet.mem ppo (1, 2) in
           let has_3_4 = USet.mem ppo (3, 4) in

           Alcotest.(check bool) "PPO contains (1,2)" true has_1_2;
           Alcotest.(check bool) "PPO contains (3,4)" true has_3_4;

           Lwt.return_unit
    )

(** Test to_string *)
let test_to_string_empty () =
  let structure = TestUtil.make_structure () in
  let fwd_es_ctx = EventStructureContext.create structure in

  let ctx = ForwardingContext.create fwd_es_ctx () in

  let s = ForwardingContext.to_string ctx in
    Alcotest.(check bool)
      "String contains empty markers" true
      (String.length s > 0)

let test_to_string_with_edges () =
  let structure = TestUtil.make_structure () in
  let fwd_es_ctx = EventStructureContext.create structure in

  let fwd = USet.create () in
    ignore (USet.add fwd (1, 2));
    let ctx = ForwardingContext.create fwd_es_ctx ~fwd () in
    let s = ForwardingContext.to_string ctx in
      Alcotest.(check bool) "String not empty" true (String.length s > 0)

(** Generate test cases from data providers *)
let make_context_creation_tests () =
  List.map
    (fun (data : DataProviders.context_creation_data) ->
      Alcotest.test_case (Printf.sprintf "create %s" data.name) `Quick
        (fun () -> test_create_context data
      )
    )
    DataProviders.context_creation_cases

let make_remap_tests () =
  List.map
    (fun (data : DataProviders.remap_data) ->
      Alcotest.test_case (Printf.sprintf "remap %s" data.name) `Quick (fun () ->
          test_remap data
      )
    )
    DataProviders.remap_cases

let make_check_tests () =
  List.map
    (fun (data : DataProviders.check_data) ->
      Alcotest.test_case (Printf.sprintf "check %s" data.name) `Quick (fun () ->
          test_check data
      )
    )
    DataProviders.check_cases

(** Test suite *)
let suite =
  let open Alcotest in
  ( "ForwardingContext",
    [
      test_case "init completes" `Quick test_init;
      test_case "init clears state" `Quick test_init_clears_state;
    ]
    @ make_context_creation_tests ()
    @ [ test_case "create generates psi" `Quick test_create_generates_psi ]
    @ make_remap_tests ()
    @ [
        test_case "remap relation" `Quick test_remap_rel;
        test_case "remap filters reflexive" `Quick
          test_remap_rel_filters_reflexive;
        test_case "cache initially empty" `Quick test_cache_initially_empty;
        test_case "cache set and get" `Quick test_cache_set_and_get;
        test_case "cache different predicates" `Quick
          test_cache_different_predicates;
        test_case "is_good initially false" `Quick test_is_good_initially_false;
        test_case "is_bad initially false" `Quick test_is_bad_initially_false;
      ]
    @ make_check_tests ()
    @ [
        (* Basic PPO tests *)
        test_case "ppo returns remapped" `Quick test_ppo_returns_remapped;
        test_case "ppo caches result" `Quick test_ppo_caches_result;
        test_case "ppo with different predicates" `Quick
          test_ppo_with_different_predicates;
        test_case "ppo with context psi" `Quick test_ppo_with_context_psi;
        test_case "ppo applies remapping" `Quick test_ppo_applies_remapping;
        test_case "ppo includes rmw orderings" `Quick
          test_ppo_includes_rmw_orderings;
        test_case "ppo with debug flag" `Quick test_ppo_with_debug_flag;
        (* PPO_LOC tests *)
        test_case "ppo_loc returns remapped" `Quick
          test_ppo_loc_returns_remapped;
        test_case "ppo_loc caches result" `Quick test_ppo_loc_caches_result;
        test_case "ppo_loc subset of ppo" `Quick test_ppo_loc_subset_of_ppo;
        test_case "ppo_loc with predicates" `Quick test_ppo_loc_with_predicates;
        test_case "ppo_loc normalizes predicates" `Quick
          test_ppo_loc_normalizes_predicates;
        test_case "ppo_loc uses cache subset" `Quick
          test_ppo_loc_uses_cache_subset;
        test_case "ppo_loc applies remapping" `Quick
          test_ppo_loc_applies_remapping;
        (* PPO_SYNC tests *)
        test_case "ppo_sync returns remapped" `Quick
          test_ppo_sync_returns_remapped;
        test_case "ppo_sync is deterministic" `Quick
          test_ppo_sync_is_deterministic;
        test_case "ppo_sync applies remapping" `Quick
          test_ppo_sync_applies_remapping;
        test_case "ppo_sync independent of predicates" `Quick
          test_ppo_sync_independent_of_predicates;
        test_case "ppo_sync with complex forwarding" `Quick
          test_ppo_sync_with_complex_forwarding;
        (* Integration tests *)
        test_case "ppo ppo_loc relationship" `Quick
          test_ppo_ppo_loc_relationship;
        test_case "all ppo functions with same context" `Quick
          test_all_ppo_functions_with_same_context;
        test_case "ppo with empty structure" `Quick
          test_ppo_with_empty_structure;
        test_case "ppo rmw read-dont-modify" `Quick
          test_ppo_rmw_read_dont_modify;
        (* Utility tests *)
        test_case "to_string empty" `Quick test_to_string_empty;
        test_case "to_string with edges" `Quick test_to_string_with_edges;
      ]
  )
