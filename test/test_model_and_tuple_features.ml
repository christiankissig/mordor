open Alcotest
open Assertion
open Context
open Ir
open Types
open Uset

(** {1 Model Assertions Tests} *)

module TestModelAssertions = struct
  (** Test model options table lookups *)

  let test_model_options_ub11 () =
    let opts = get_model_options "UB11" in
      check bool "UB11 exists" true (Option.is_some opts);
      match opts with
      | Some { coherent; ubopt } ->
          check bool "UB11 has no coherent" true (Option.is_none coherent);
          check bool "UB11 has ubopt" true ubopt
      | None -> fail "UB11 options not found"

  let test_model_options_imm () =
    let opts = get_model_options "IMM" in
      check bool "IMM exists" true (Option.is_some opts);
      match opts with
      | Some { coherent; ubopt } ->
          check (option string) "IMM coherent is imm" (Some "imm") coherent;
          check bool "IMM no ubopt" false ubopt
      | None -> fail "IMM options not found"

  let test_model_options_rc11 () =
    let opts = get_model_options "RC11" in
      check bool "RC11 exists" true (Option.is_some opts);
      match opts with
      | Some { coherent; ubopt } ->
          check (option string) "RC11 coherent is rc11" (Some "rc11") coherent;
          check bool "RC11 no ubopt" false ubopt
      | None -> fail "RC11 options not found"

  let test_model_options_immub () =
    let opts = get_model_options "IMMUB" in
      check bool "IMMUB exists" true (Option.is_some opts);
      match opts with
      | Some { coherent; ubopt } ->
          check (option string) "IMMUB coherent is imm" (Some "imm") coherent;
          check bool "IMMUB has ubopt" true ubopt
      | None -> fail "IMMUB options not found"

  let test_model_options_undefined () =
    let opts = get_model_options "Sevcik" in
      check bool "Sevcik exists" true (Option.is_some opts);
      match opts with
      | Some { coherent; ubopt } ->
          check bool "Sevcik has no coherent" true (Option.is_none coherent);
          check bool "Sevcik no ubopt" false ubopt
      | None -> fail "Sevcik options not found"

  let suite =
    [
      test_case "model_options_ub11" `Quick test_model_options_ub11;
      test_case "model_options_imm" `Quick test_model_options_imm;
      test_case "model_options_rc11" `Quick test_model_options_rc11;
      test_case "model_options_immub" `Quick test_model_options_immub;
      test_case "model_options_undefined" `Quick test_model_options_undefined;
    ]
end

(** {1 Set Membership Tests} *)

module TestSetMembership = struct
  (** Helper to create minimal execution *)
  let make_test_execution ppo_pairs =
    let ppo = USet.create () in
      List.iter (fun (a, b) -> USet.add ppo (a, b) |> ignore) ppo_pairs;
      {
        ex_e = USet.create ();
        rf = USet.create ();
        ex_rmw = USet.create ();
        dp = USet.create ();
        ppo;
        ex_p = [];
        fix_rf_map = Hashtbl.create 0;
        pointer_map = Some (Hashtbl.create 0);
        final_env = Hashtbl.create 0;
      }

  (** Helper to create minimal structure *)
  let make_test_structure () =
    {
      e = USet.create ();
      events = Hashtbl.create 0;
      po = USet.create ();
      po_iter = USet.create ();
      rmw = USet.create ();
      lo = USet.create ();
      restrict = Hashtbl.create 0;
      cas_groups = Hashtbl.create 0;
      pwg = [];
      fj = USet.create ();
      p = Hashtbl.create 0;
      constraint_ = [];
      conflict = USet.create ();
      origin = Hashtbl.create 0;
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
    }

  let test_has_set_operation_in () =
    let expr = EBinOp (ENum (Z.of_int 3), "in", EVar ".ppo") in
      check bool "detects in operator" true (has_set_operation expr)

  let test_has_set_operation_notin () =
    let expr = EBinOp (ENum (Z.of_int 3), "notin", EVar ".ppo") in
      check bool "detects notin operator" true (has_set_operation expr)

  let test_has_set_operation_nested () =
    let e1 = EBinOp (ENum (Z.of_int 3), "in", EVar ".ppo") in
    let e2 = EBinOp (ENum (Z.of_int 4), "notin", EVar ".po") in
    let expr = EBinOp (e1, "&&", e2) in
      check bool "detects nested set operations" true (has_set_operation expr)

  let test_has_set_operation_none () =
    let expr = EBinOp (ENum (Z.of_int 3), "+", ENum (Z.of_int 4)) in
      check bool "no set operation in arithmetic" false (has_set_operation expr)

  let test_eval_tuple_valid () =
    let expr = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
    let a, b = eval_tuple expr in
      check int "tuple first element" 3 a;
      check int "tuple second element" 4 b

  let test_eval_tuple_invalid () =
    let expr = EBinOp (EVar "x", ",", ENum (Z.of_int 4)) in
      check_raises "eval_tuple raises on non-integer"
        (Failure "Invalid tuple in set membership: expected (int, int)")
        (fun () -> ignore (eval_tuple expr)
      )

  let test_get_relation_ppo () =
    let structure = make_test_structure () in
    let execution = make_test_execution [ (1, 2); (2, 3) ] in
    let rel = get_relation ".ppo" structure execution in
      check bool "ppo relation has (1,2)" true (USet.mem rel (1, 2));
      check bool "ppo relation has (2,3)" true (USet.mem rel (2, 3))

  let test_get_relation_unknown () =
    let structure = make_test_structure () in
    let execution = make_test_execution [] in
    let rel = get_relation ".unknown" structure execution in
      check int "unknown relation is empty" 0 (USet.size rel)

  let test_eval_set_expr_in_true () =
    let structure = make_test_structure () in
    let execution = make_test_execution [ (3, 4) ] in
    let tuple = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
    let expr = EBinOp (tuple, "in", EVar ".ppo") in
    let result = eval_set_expr expr structure execution in
      check bool "(3,4) in .ppo is true" true result

  let test_eval_set_expr_notin_true () =
    let structure = make_test_structure () in
    let execution = make_test_execution [ (1, 2) ] in
    let tuple = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
    let expr = EBinOp (tuple, "notin", EVar ".ppo") in
    let result = eval_set_expr expr structure execution in
      check bool "(3,4) notin .ppo is true" true result

  let test_eval_set_expr_and () =
    let structure = make_test_structure () in
    let execution = make_test_execution [ (1, 2) ] in
    let t1 = EBinOp (ENum (Z.of_int 1), ",", ENum (Z.of_int 2)) in
    let e1 = EBinOp (t1, "in", EVar ".ppo") in
    let t2 = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
    let e2 = EBinOp (t2, "notin", EVar ".ppo") in
    let expr = EBinOp (e1, "&&", e2) in
    let result = eval_set_expr expr structure execution in
      check bool "conjunction evaluates correctly" true result

  let suite =
    [
      test_case "has_set_operation_in" `Quick test_has_set_operation_in;
      test_case "has_set_operation_notin" `Quick test_has_set_operation_notin;
      test_case "has_set_operation_nested" `Quick test_has_set_operation_nested;
      test_case "has_set_operation_none" `Quick test_has_set_operation_none;
      test_case "eval_tuple_valid" `Quick test_eval_tuple_valid;
      test_case "eval_tuple_invalid" `Quick test_eval_tuple_invalid;
      test_case "get_relation_ppo" `Quick test_get_relation_ppo;
      test_case "get_relation_unknown" `Quick test_get_relation_unknown;
      test_case "eval_set_expr_in_true" `Quick test_eval_set_expr_in_true;
      test_case "eval_set_expr_notin_true" `Quick test_eval_set_expr_notin_true;
      test_case "eval_set_expr_and" `Quick test_eval_set_expr_and;
    ]
end

(** {1 Context Model Options Tests} *)

module TestContextModelOptions = struct
  let test_default_options_coherent () =
    let opts = default_options in
      check string "default coherent is undefined" "undefined" opts.coherent

  let test_default_options_model_name () =
    let opts = default_options in
      check (option string) "default model_name is None" None opts.model_name

  let test_default_options_ubopt () =
    let opts = default_options in
      check bool "default ubopt is false" false opts.ubopt

  let test_model_name_mutable () =
    let opts = { default_options with model_name = None } in
      opts.model_name <- Some "UB11";
      check (option string) "model_name can be set" (Some "UB11")
        opts.model_name

  let test_ubopt_mutable () =
    let opts = { default_options with ubopt = false } in
      opts.ubopt <- true;
      check bool "ubopt can be set" true opts.ubopt

  let suite =
    [
      test_case "default_options_coherent" `Quick test_default_options_coherent;
      test_case "default_options_model_name" `Quick
        test_default_options_model_name;
      test_case "default_options_ubopt" `Quick test_default_options_ubopt;
      test_case "model_name_mutable" `Quick test_model_name_mutable;
      test_case "ubopt_mutable" `Quick test_ubopt_mutable;
    ]
end

(** {1 Combined Test Suite} *)

let suite =
  ( "Model and Tuple Features",
    TestModelAssertions.suite
    @ TestSetMembership.suite
    @ TestContextModelOptions.suite
  )
