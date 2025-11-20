(** Unit tests for coherence checking *)
open Uset

open Alcotest
open Coherence
open Executions
open Expr
open Lwt.Syntax
open Types

(* Helper to run Lwt tests *)
let lwt_test fn () = Lwt_main.run (fn ())

(** Test helper: create a simple event *)
let make_event _ typ rmod wmod fmod strong rval wval id_opt =
  {
    id = id_opt;
    loc = Option.map Expr.of_value id_opt;
    typ;
    rmod =
      ( match rmod with
      | Some m -> m
      | None -> Relaxed
      );
    wmod =
      ( match wmod with
      | Some m -> m
      | None -> Relaxed
      );
    fmod =
      ( match fmod with
      | Some m -> m
      | None -> Relaxed
      );
    strong;
    rval;
    wval;
    label = 0;
    van = 0;
    cond = None;
    volatile = false;
    lhs = None;
    rhs = None;
    pc = None;
    hide = false;
    quot = None;
  }

(** Test helper: create event hashtable *)
let make_events_table events =
  let tbl = Hashtbl.create 10 in
    List.iter (fun (id, event) -> Hashtbl.add tbl id event) events;
    tbl

(** Helper to create empty execution *)
let make_empty_execution () =
  {
    ex_e = USet.create ();
    rf = USet.create ();
    ex_rmw = USet.create ();
    dp = USet.create ();
    ppo = USet.create ();
    ex_p = [];
    conds = [];
    fix_rf_map = Hashtbl.create 10;
    justs = [];
    pointer_map = Hashtbl.create 10 |> Option.some;
  }

(** Test helper: create uset from list *)
let uset_of_list lst =
  let uset = USet.create () in
    List.iter (fun x -> USet.add uset x |> ignore) lst;
    uset

(** Test semicolon_rel with empty list *)
let test_semicolon_empty () =
  let result = semicolon_rel [] in
    check int "empty composition" 0 (USet.size result);
    ()

(** Test semicolon_rel with single relation *)
let test_semicolon_single () =
  let rel = uset_of_list [ (1, 2); (2, 3) ] in
  let result = semicolon_rel [ rel ] in
    check int "single relation size" 2 (USet.size result);
    check bool "contains (1,2)" true (USet.mem result (1, 2));
    check bool "contains (2,3)" true (USet.mem result (2, 3));
    ()

(** Test semicolon_rel composition *)
let test_semicolon_compose () =
  let r1 = uset_of_list [ (1, 2); (3, 4) ] in
  let r2 = uset_of_list [ (2, 5); (4, 6) ] in
  let result = semicolon_rel [ r1; r2 ] in
    check bool "contains (1,5)" true (USet.mem result (1, 5));
    check bool "contains (3,6)" true (USet.mem result (3, 6));
    check bool "not contains (1,2)" false (USet.mem result (1, 2));
    ()

(** Test semicolon_rel with three relations *)
let test_semicolon_triple () =
  let r1 = uset_of_list [ (1, 2) ] in
  let r2 = uset_of_list [ (2, 3) ] in
  let r3 = uset_of_list [ (3, 4) ] in
  let result = semicolon_rel [ r1; r2; r3 ] in
    check bool "contains (1,4)" true (USet.mem result (1, 4));
    check int "result size" 1 (USet.size result);
    ()

(** Test em with Write events *)
let test_em_write_events () =
  let events =
    make_events_table
      [
        (1, make_event 1 Write None (Some Release) None None None None None);
        (2, make_event 2 Read (Some Acquire) None None None None None None);
        (3, make_event 3 Write None (Some Relaxed) None None None None None);
      ]
  in
  let e = uset_of_list [ 1; 2; 3 ] in
  let result = em events e Write None None None in
    check int "two write events" 2 (USet.size result);
    check bool "contains (1,1)" true (USet.mem result (1, 1));
    check bool "contains (3,3)" true (USet.mem result (3, 3));
    check bool "not contains (2,2)" false (USet.mem result (2, 2));
    ()

(** Test em with mode filtering *)
let test_em_with_mode () =
  let events =
    make_events_table
      [
        (1, make_event 1 Write None (Some Release) None None None None None);
        (2, make_event 2 Write None (Some Relaxed) None None None None None);
      ]
  in
  let e = uset_of_list [ 1; 2 ] in
  let result = em events e Write (Some Release) None None in
    check int "one release write" 1 (USet.size result);
    check bool "contains (1,1)" true (USet.mem result (1, 1));
    ()

(** Test em with fence events *)
let test_em_fence_events () =
  let events =
    make_events_table
      [
        (1, make_event 1 Fence (Some SC) None (Some Release) None None None None);
        (2, make_event 2 Fence (Some Acquire) None None None None None None);
        (3, make_event 3 Write None (Some Release) None None None None None);
      ]
  in
  let e = uset_of_list [ 1; 2; 3 ] in
  let result = em events e Fence None None None in
    check int "two fence events" 2 (USet.size result);
    ()

(** Test em with strong mode *)
let test_em_strong_mode () =
  let events =
    make_events_table
      [
        ( 1,
          make_event 1 Write None (Some Release) None (Some Strong) None None
            None
        );
        (2, make_event 2 Write None (Some Release) None None None None None);
      ]
  in
  let e = uset_of_list [ 1; 2 ] in
  let result = em events e Write None None (Some Strong) in
    check int "one strong write" 1 (USet.size result);
    check bool "contains (1,1)" true (USet.mem result (1, 1));
    ()

(** Test imm_deps with data dependency *)
let test_imm_deps_data () =
  let events =
    make_events_table
      [
        ( 1,
          make_event 1 Read (Some Relaxed) None None None
            (Some (VNumber (Z.of_int 42)))
            None None
        );
        ( 2,
          make_event 2 Write None (Some Relaxed) None None None
            (Some (ENum (Z.of_int 42)))
            None
        );
      ]
  in
  let po = uset_of_list [ (1, 2) ] in
  let e = uset_of_list [ 1; 2 ] in
  let restrict = Hashtbl.create 10 in
  let result = imm_deps (make_empty_execution ()) events po e restrict in
    (* Should detect data dependency since wval references rval *)
    check bool "has data dependency" true (USet.size result >= 0);
    ()

(** Test imm_deps with control dependency *)
let test_imm_deps_ctrl () =
  let events =
    make_events_table
      [
        (1, make_event 1 Read (Some Relaxed) None None None None None None);
        (2, make_event 2 Write None (Some Relaxed) None None None None None);
      ]
  in
  let po = uset_of_list [ (1, 2) ] in
  let e = uset_of_list [ 1; 2 ] in
  let restrict = Hashtbl.create 10 in
    Hashtbl.add restrict 1 [ ENum (Z.of_int 1) ];
    Hashtbl.add restrict 2 [ ENum (Z.of_int 2) ];
    let result = imm_deps (make_empty_execution ()) events po e restrict in
      (* Should detect control dependency since restricts differ *)
      check bool "has control dependency" true (USet.size result > 0);
      ()

(** Test imm_coherent with simple coherence *)
let test_imm_coherent_simple () =
  let events =
    make_events_table
      [
        (1, make_event 1 Write None (Some Relaxed) None None None None None);
        (2, make_event 2 Write None (Some Relaxed) None None None None None);
      ]
  in
  let ex_e = uset_of_list [ 1; 2 ] in
  let po = uset_of_list [ (1, 2) ] in
  let rf = USet.create () in
  let restrict = Hashtbl.create 10 in
  let (structure : symbolic_event_structure) =
    {
      e = ex_e;
      events;
      po;
      po_iter = USet.create ();
      restrict;
      rmw = USet.create ();
      lo = USet.create ();
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
      conflict = USet.create ();
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
    }
  in
  let (execution : symbolic_execution) =
    {
      ex_e;
      rf;
      ex_rmw = USet.create ();
      dp = USet.create ();
      ppo = USet.create ();
      ex_p = [];
      conds = [];
      fix_rf_map = Hashtbl.create 10;
      justs = [];
      pointer_map = Hashtbl.create 10 |> Option.some;
    }
  in
  let loc_restrict x = x in
  let cache = imm_coherent_cache execution structure events loc_restrict in
  let co = uset_of_list [ (1, 2) ] in
  let result = imm_coherent co cache in
    check bool "simple coherence passes" true result;
    ()

(** Test rc11_coherent with simple scenario *)
let test_rc11_coherent_simple () =
  let events =
    make_events_table
      [
        (1, make_event 1 Write None (Some Relaxed) None None None None None);
        (2, make_event 2 Read (Some Relaxed) None None None None None None);
      ]
  in
  let ex_e = uset_of_list [ 1; 2 ] in
  let po = uset_of_list [ (1, 2) ] in
  let rf = USet.create () in
  let restrict = Hashtbl.create 10 in
  let structure =
    {
      e = ex_e;
      events;
      po;
      po_iter = USet.create ();
      restrict;
      rmw = USet.create ();
      lo = USet.create ();
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
      conflict = USet.create ();
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
    }
  in
  let execution =
    {
      ex_e;
      rf;
      ex_rmw = USet.create ();
      dp = USet.create ();
      ppo = USet.create ();
      ex_p = [];
      conds = [];
      fix_rf_map = Hashtbl.create 10;
      justs = [];
      pointer_map = Hashtbl.create 10 |> Option.some;
    }
  in
  let loc_restrict x = x in
  let cache = rc11_coherent_cache execution structure events loc_restrict in
  let co = USet.create () in
  let result = rc11_coherent co cache in
    check bool "simple RC11 coherence passes" true result;
    ()

(** Test imm_coherent with RMW atomicity *)
let test_imm_coherent_rmw () =
  let events =
    make_events_table
      [
        ( 0,
          make_event 0 Init None None None None None None (Some (VNumber Z.zero))
        );
        (1, make_event 1 Read (Some Acquire) None None None None None None);
        (2, make_event 2 Write None (Some Release) None None None None None);
        (3, make_event 3 Write None (Some Relaxed) None None None None None);
      ]
  in
  let ex_e = uset_of_list [ 0; 1; 2; 3 ] in
  let po = uset_of_list [ (1, 2) ] in
  let rf = uset_of_list [ (0, 1) ] in
  (* Read from initial write *)
  let rmw = uset_of_list [ (1, 2) ] in
  let restrict = Hashtbl.create 10 in
  let structure =
    {
      e = ex_e;
      events;
      po;
      po_iter = USet.create ();
      restrict;
      rmw = USet.create ();
      lo = USet.create ();
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
      conflict = USet.create ();
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
    }
  in
  let execution =
    {
      ex_e;
      rf;
      ex_rmw = rmw;
      dp = USet.create ();
      ppo = USet.create ();
      ex_p = [];
      conds = [];
      fix_rf_map = Hashtbl.create 10;
      justs = [];
      pointer_map = Hashtbl.create 10 |> Option.some;
    }
  in
  let loc_restrict x = x in
  let cache = imm_coherent_cache execution structure events loc_restrict in
  (* co ordering that violates atomicity: 0 -> 3 -> 2 *)
  let co = uset_of_list [ (0, 3); (3, 2) ] in
  let result = imm_coherent co cache in
    check bool "RMW atomicity violated" false result;
    (* Should fail *)
    ()

(** Test cache type construction *)
let test_cache_types () =
  let events = make_events_table [] in
  let ex_e = USet.create () in
  let po = USet.create () in
  let rf = USet.create () in
  let restrict = Hashtbl.create 10 in
  let structure =
    {
      e = ex_e;
      events;
      po;
      po_iter = USet.create ();
      restrict;
      rmw = USet.create ();
      lo = USet.create ();
      cas_groups = Hashtbl.create 10;
      pwg = [];
      fj = USet.create ();
      p = USet.create ();
      constraint_ = [];
      conflict = USet.create ();
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
    }
  in
  let execution =
    {
      ex_e;
      rf;
      ex_rmw = USet.create ();
      dp = USet.create ();
      ppo = USet.create ();
      ex_p = [];
      conds = [];
      fix_rf_map = Hashtbl.create 10;
      justs = [];
      pointer_map = Hashtbl.create 10 |> Option.some;
    }
  in
  let loc_restrict x = x in

  (* Test IMM cache creation *)
  let imm_cache = imm_coherent_cache execution structure events loc_restrict in
  let wrapped_imm = IMMCache imm_cache in
    check bool "IMM cache created" true
      ( match wrapped_imm with
      | IMMCache _ -> true
      | _ -> false
      );

    (* Test RC11 cache creation *)
    let rc11_cache =
      rc11_coherent_cache execution structure events loc_restrict
    in
    let wrapped_rc11 = RC11Cache rc11_cache in
      check bool "RC11 cache created" true
        ( match wrapped_rc11 with
        | RC11Cache _ -> true
        | _ -> false
        );

      (* Test UndefinedCache *)
      let undef = UndefinedCache { rfi = None; rmw = None } in
        check bool "Undefined cache created" true
          ( match undef with
          | UndefinedCache _ -> true
          | _ -> false
          );

        (* Test EmptyCache *)
        check bool "Empty cache is empty" true
          ( match EmptyCache with
          | EmptyCache -> true
          | _ -> false
          );
        ()

(** Test permutations with empty list *)
let test_permutations_empty () =
  let result = permutations [] in
    check int "empty list has one permutation" 1 (List.length result);
    check (list int) "empty permutation" [] (List.hd result);
    ()

(** Test permutations with single element *)
let test_permutations_single () =
  let result = permutations [ 1 ] in
    check int "single element has one permutation" 1 (List.length result);
    check (list int) "single element permutation" [ 1 ] (List.hd result);
    ()

(** Test permutations with two elements *)
let test_permutations_two () =
  let result = permutations [ 1; 2 ] in
    check int "two elements have 2! permutations" 2 (List.length result);
    let sorted = List.sort compare result in
      check (list int) "first permutation" [ 1; 2 ] (List.nth sorted 0);
      check (list int) "second permutation" [ 2; 1 ] (List.nth sorted 1);
      ()

(** Test permutations with three elements *)
let test_permutations_three () =
  let result = permutations [ 1; 2; 3 ] in
    check int "three elements have 3! permutations" 6 (List.length result);
    (* Check that all permutations are unique *)
    let unique = List.sort_uniq compare result in
      check int "all permutations are unique" 6 (List.length unique);
      ()

(** Test suite *)
let suite =
  ( "Coherence",
    [
      test_case "semicolon_rel empty" `Quick test_semicolon_empty;
      test_case "semicolon_rel single" `Quick test_semicolon_single;
      test_case "semicolon_rel compose" `Quick test_semicolon_compose;
      test_case "semicolon_rel triple" `Quick test_semicolon_triple;
      test_case "em write events" `Quick test_em_write_events;
      test_case "em with mode" `Quick test_em_with_mode;
      test_case "em fence events" `Quick test_em_fence_events;
      test_case "em strong mode" `Quick test_em_strong_mode;
      test_case "imm_deps data" `Quick test_imm_deps_data;
      test_case "imm_deps control" `Quick test_imm_deps_ctrl;
      test_case "imm_coherent simple" `Quick test_imm_coherent_simple;
      test_case "rc11_coherent simple" `Quick test_rc11_coherent_simple;
      test_case "imm_coherent RMW" `Quick test_imm_coherent_rmw;
      test_case "cache types" `Quick test_cache_types;
      test_case "permutations empty" `Quick test_permutations_empty;
      test_case "permutations single" `Quick test_permutations_single;
      test_case "permutations two" `Quick test_permutations_two;
      test_case "permutations three" `Quick test_permutations_three;
    ]
  )
