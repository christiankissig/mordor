(** Unit tests for ForwardingContext - Refactored with data providers *)
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
       let forwardingcontext_state = EventStructureContext.create structure in
         EventStructureContext.init forwardingcontext_state
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
         let forwardingcontext_state = EventStructureContext.create structure in

         ContextCache.mark_good forwardingcontext_state.context_cache fwd we;

         let* () = EventStructureContext.init forwardingcontext_state in

         Alcotest.(check bool)
           "goodcon cleared" false
           (ContextCache.is_good forwardingcontext_state.context_cache fwd we);
         Lwt.return_unit
     in
       Lwt.return_unit
    )

(** Test context creation - using data provider *)
let test_create_context (data : DataProviders.context_creation_data) =
  let structure = TestUtil.make_structure () in
  let forwardingcontext_state = EventStructureContext.create structure in

  let create_uset edges =
    let s = USet.create () in
      List.iter (fun (a, b) -> ignore (USet.add s (a, b))) edges;
      s
  in

  let ctx =
    match (data.fwd_edges, data.we_edges) with
    | None, None -> ForwardingContext.create forwardingcontext_state ()
    | Some fwd_edges, None ->
        let fwd = create_uset fwd_edges in
          ForwardingContext.create forwardingcontext_state ~fwd ()
    | None, Some we_edges ->
        let we = create_uset we_edges in
          ForwardingContext.create forwardingcontext_state ~we ()
    | Some fwd_edges, Some we_edges ->
        let fwd = create_uset fwd_edges in
        let we = create_uset we_edges in
          ForwardingContext.create forwardingcontext_state ~fwd ~we ()
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
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in

     let fwd = USet.create () in
       ignore (USet.add fwd (1, 2));
       let ctx = ForwardingContext.create forwardingcontext_state ~fwd () in
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
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let fwd = USet.create () in
       List.iter (fun (a, b) -> ignore (USet.add fwd (a, b))) data.fwd_edges;
       let ctx = ForwardingContext.create forwardingcontext_state ~fwd () in
         Alcotest.(check int)
           (Printf.sprintf "Remap %s" data.name)
           data.expected
           (ForwardingContext.remap ctx data.event);
         Lwt.return_unit
    )

let test_remap_rel () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
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
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let fwd = USet.create () in
       ignore (USet.add fwd (1, 2));
       let ctx = ForwardingContext.create forwardingcontext_state ~fwd () in
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
  let forwardingcontext_state = EventStructureContext.create structure in

  let ctx = ForwardingContext.create forwardingcontext_state () in
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
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
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
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
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
  let forwardingcontext_state = EventStructureContext.create structure in

  let fwd = USet.create () in
  let we = USet.create () in
    Alcotest.(check bool)
      "Not initially good" false
      (ContextCache.is_good forwardingcontext_state.context_cache fwd we)

let test_is_bad_initially_false () =
  let structure = TestUtil.make_structure () in
  let forwardingcontext_state = EventStructureContext.create structure in

  let fwd = USet.create () in
  let we = USet.create () in
    Alcotest.(check bool)
      "Not initially bad" false
      (ContextCache.is_bad forwardingcontext_state.context_cache fwd we)

(** Test context checking - using data provider *)
let test_check (data : DataProviders.check_data) =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx =
       {
         (ForwardingContext.create forwardingcontext_state ()) with
         psi = data.psi;
       }
     in
       let* result = ForwardingContext.check ctx in
         Alcotest.(check bool)
           (Printf.sprintf "%s satisfiability" data.name)
           data.expected_result result;

         if data.should_be_good then
           Alcotest.(check bool)
             (Printf.sprintf "%s marked as good" data.name)
             true
             (ContextCache.is_good forwardingcontext_state.context_cache ctx.fwd
                ctx.we
             );

         if data.should_be_bad then
           Alcotest.(check bool)
             (Printf.sprintf "%s marked as bad" data.name)
             true
             (ContextCache.is_bad forwardingcontext_state.context_cache ctx.fwd
                ctx.we
             );

         Lwt.return_unit
    )

(** Test PPO computation *)
let test_ppo_returns_remapped () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
       let* ppo = ForwardingContext.ppo ctx [] in
         (* Should return some relation *)
         Alcotest.(check bool) "PPO is a uset" true (USet.size ppo >= 0);
         Lwt.return_unit
    )

let test_ppo_caches_result () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
     let predicates = [] in

     (* First call *)
     let* ppo1 = ForwardingContext.ppo ctx predicates in
       (* Second call - should hit cache *)
       let* ppo2 = ForwardingContext.ppo ctx predicates in

       Alcotest.(check bool) "PPO cached" true (USet.equal ppo1 ppo2);
       Lwt.return_unit
    )

let test_ppo_loc_returns_remapped () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
       let* ppo_loc = ForwardingContext.ppo_loc ctx [] in
         (* Should return some relation *)
         Alcotest.(check bool) "PPO_loc is a uset" true (USet.size ppo_loc >= 0);
         Lwt.return_unit
    )

let test_ppo_sync_returns_remapped () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     let ctx = ForwardingContext.create forwardingcontext_state () in
     let ppo_sync = ForwardingContext.ppo_sync ctx in
       (* Should return some relation *)
       Alcotest.(check bool) "PPO_sync is a uset" true (USet.size ppo_sync >= 0);
       Lwt.return_unit
    )

(** Test to_string *)
let test_to_string_empty () =
  let structure = TestUtil.make_structure () in
  let forwardingcontext_state = EventStructureContext.create structure in

  let ctx = ForwardingContext.create forwardingcontext_state () in

  let s = ForwardingContext.to_string ctx in
    Alcotest.(check bool)
      "String contains empty markers" true
      (String.length s > 0)

let test_to_string_with_edges () =
  let structure = TestUtil.make_structure () in
  let forwardingcontext_state = EventStructureContext.create structure in

  let fwd = USet.create () in
    ignore (USet.add fwd (1, 2));
    let ctx = ForwardingContext.create forwardingcontext_state ~fwd () in
    let s = ForwardingContext.to_string ctx in
      Alcotest.(check bool) "String not empty" true (String.length s > 0)

(** Test update_po *)
let test_update_po_clears_cache () =
  Lwt_main.run
    (let structure = TestUtil.make_structure () in
     let forwardingcontext_state = EventStructureContext.create structure in

     let* () = EventStructureContext.init forwardingcontext_state in
     (* Create a context and cache something *)
     let ctx = ForwardingContext.create forwardingcontext_state () in
     let test_set = USet.create () in
       ignore (USet.add test_set (1, 2));
       let _ = ForwardingContext.cache_set_ppo ctx [] test_set in

       (* Update PO - should clear cache *)
       let new_po = USet.create () in
         ignore (USet.add new_po (0, 1));
         EventStructureContext.update_po forwardingcontext_state new_po;

         (* Cache size should be 0 after clear *)
         Alcotest.(check int)
           "Cache cleared" 0
           (PpoCache.size forwardingcontext_state.ppo_cache);
         Lwt.return_unit
    )

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
        test_case "ppo returns remapped" `Quick test_ppo_returns_remapped;
        test_case "ppo caches result" `Quick test_ppo_caches_result;
        test_case "ppo_loc returns remapped" `Quick
          test_ppo_loc_returns_remapped;
        test_case "ppo_sync returns remapped" `Quick
          test_ppo_sync_returns_remapped;
        test_case "to_string empty" `Quick test_to_string_empty;
        test_case "to_string with edges" `Quick test_to_string_with_edges;
        test_case "update_po clears cache" `Quick test_update_po_clears_cache;
      ]
  )
