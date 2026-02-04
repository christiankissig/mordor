open Alcotest
open Assertion
open Context
open Eventstructures
open Executions
open Ir
open Types
open Uset

(** {1 Model Assertions Tests} *)

module TestModelAssertions = struct
  (** Test model options table lookups *)

  type model_test_data = {
    model_name : string;
    expected_coherent : string option;
    expected_ubopt : bool;
  }

  (** Data provider for model options tests *)
  let model_options_test_data =
    [
      { model_name = "UB11"; expected_coherent = None; expected_ubopt = true };
      {
        model_name = "IMM";
        expected_coherent = Some "imm";
        expected_ubopt = false;
      };
      {
        model_name = "RC11";
        expected_coherent = Some "rc11";
        expected_ubopt = false;
      };
      {
        model_name = "IMMUB";
        expected_coherent = Some "imm";
        expected_ubopt = true;
      };
      {
        model_name = "Sevcik";
        expected_coherent = None;
        expected_ubopt = false;
      };
    ]

  (** Parameterized test function for model options *)
  let test_model_options { model_name; expected_coherent; expected_ubopt } () =
    let opts = get_model_options model_name in
      check bool
        (Printf.sprintf "%s exists" model_name)
        true (Option.is_some opts);
      match opts with
      | Some { coherent; ubopt } ->
          check (option string)
            (Printf.sprintf "%s coherent" model_name)
            expected_coherent coherent;
          check bool (Printf.sprintf "%s ubopt" model_name) expected_ubopt ubopt
      | None -> fail (Printf.sprintf "%s options not found" model_name)

  let suite =
    List.map
      (fun (data : model_test_data) ->
        test_case
          (Printf.sprintf "model_options_%s"
             (String.lowercase_ascii data.model_name)
          )
          `Quick (test_model_options data)
      )
      model_options_test_data
end

(** {1 Set Membership Tests} *)

module TestSetMembership = struct
  (** Helper to create minimal execution *)
  let make_test_execution ppo_pairs =
    let ppo = USet.create () in
      List.iter (fun (a, b) -> USet.add ppo (a, b) |> ignore) ppo_pairs;
      {
        id = 0;
        e = USet.create ();
        rf = USet.create ();
        rmw = USet.create ();
        dp = USet.create ();
        ppo;
        ex_p = [];
        fix_rf_map = Hashtbl.create 0;
        pointer_map = Some (Hashtbl.create 0);
        final_env = Hashtbl.create 0;
      }

  (** Helper to create minimal structure *)
  let make_test_structure () = SymbolicEventStructure.create ()

  (** {2 has_set_operation Tests} *)

  type has_set_op_test_data = {
    name : string;
    expr : expr;
    expected : bool;
    description : string;
  }

  let has_set_operation_test_data =
    [
      {
        name = "in";
        expr = EBinOp (ENum (Z.of_int 3), "in", EVar ".ppo");
        expected = true;
        description = "detects in operator";
      };
      {
        name = "notin";
        expr = EBinOp (ENum (Z.of_int 3), "notin", EVar ".ppo");
        expected = true;
        description = "detects notin operator";
      };
      {
        name = "nested";
        expr =
          EBinOp
            ( EBinOp (ENum (Z.of_int 3), "in", EVar ".ppo"),
              "&&",
              EBinOp (ENum (Z.of_int 4), "notin", EVar ".po")
            );
        expected = true;
        description = "detects nested set operations";
      };
      {
        name = "none";
        expr = EBinOp (ENum (Z.of_int 3), "+", ENum (Z.of_int 4));
        expected = false;
        description = "no set operation in arithmetic";
      };
    ]

  let test_has_set_operation { expr; expected; description; _ } () =
    check bool description expected (SetOperations.has_set_operation expr)

  (** {2 eval_tuple Tests} *)

  let test_eval_tuple_valid () =
    let expr = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
    let a, b = SetOperations.eval_tuple expr in
      check int "tuple first element" 3 a;
      check int "tuple second element" 4 b

  let test_eval_tuple_invalid () =
    let expr = EBinOp (EVar "x", ",", ENum (Z.of_int 4)) in
      check_raises "eval_tuple raises on non-integer"
        (Failure "Invalid tuple in set membership: expected (int, int)")
        (fun () -> ignore (SetOperations.eval_tuple expr)
      )

  (** {2 get_relation Tests} *)

  type relation_test_data = {
    name : string;
    relation : string;
    ppo_pairs : (int * int) list;
    expected_pairs : (int * int) list;
    expected_size : int option;
  }

  let relation_test_data =
    [
      {
        name = "ppo";
        relation = ".ppo";
        ppo_pairs = [ (1, 2); (2, 3) ];
        expected_pairs = [ (1, 2); (2, 3) ];
        expected_size = None;
      };
      {
        name = "unknown";
        relation = ".unknown";
        ppo_pairs = [];
        expected_pairs = [];
        expected_size = Some 0;
      };
    ]

  let test_get_relation
      { relation; ppo_pairs; expected_pairs; expected_size; _ } () =
    let structure = make_test_structure () in
    let execution = make_test_execution ppo_pairs in
    let rel = Execution.get_relation relation structure execution in
      ( match expected_size with
      | Some size ->
          check int
            (Printf.sprintf "%s relation size" relation)
            size (USet.size rel)
      | None -> ()
      );
      List.iter
        (fun (a, b) ->
          check bool
            (Printf.sprintf "%s relation has (%d,%d)" relation a b)
            true
            (USet.mem rel (a, b))
        )
        expected_pairs

  (** {2 eval_set_expr Tests} *)

  type set_expr_test_data = {
    name : string;
    ppo_pairs : (int * int) list;
    expr_builder : unit -> expr;
    expected : bool;
    description : string;
  }

  let set_expr_test_data =
    [
      {
        name = "in_true";
        ppo_pairs = [ (3, 4) ];
        expr_builder =
          (fun () ->
            let tuple = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
              EBinOp (tuple, "in", EVar ".ppo")
          );
        expected = true;
        description = "(3,4) in .ppo is true";
      };
      {
        name = "notin_true";
        ppo_pairs = [ (1, 2) ];
        expr_builder =
          (fun () ->
            let tuple = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
              EBinOp (tuple, "notin", EVar ".ppo")
          );
        expected = true;
        description = "(3,4) notin .ppo is true";
      };
      {
        name = "and";
        ppo_pairs = [ (1, 2) ];
        expr_builder =
          (fun () ->
            let t1 = EBinOp (ENum (Z.of_int 1), ",", ENum (Z.of_int 2)) in
            let e1 = EBinOp (t1, "in", EVar ".ppo") in
            let t2 = EBinOp (ENum (Z.of_int 3), ",", ENum (Z.of_int 4)) in
            let e2 = EBinOp (t2, "notin", EVar ".ppo") in
              EBinOp (e1, "&&", e2)
          );
        expected = true;
        description = "conjunction evaluates correctly";
      };
    ]

  let test_eval_set_expr { ppo_pairs; expr_builder; expected; description; _ }
      () =
    let structure = make_test_structure () in
    let execution = make_test_execution ppo_pairs in
    let expr = expr_builder () in
    let result = SetOperations.eval_set_expr expr structure execution in
      check bool description expected result

  let suite =
    List.map
      (fun (data : has_set_op_test_data) ->
        test_case
          (Printf.sprintf "has_set_operation_%s" data.name)
          `Quick
          (test_has_set_operation data)
      )
      has_set_operation_test_data
    @ [
        test_case "eval_tuple_valid" `Quick test_eval_tuple_valid;
        test_case "eval_tuple_invalid" `Quick test_eval_tuple_invalid;
      ]
    @ List.map
        (fun (data : relation_test_data) ->
          test_case
            (Printf.sprintf "get_relation_%s" data.name)
            `Quick (test_get_relation data)
        )
        relation_test_data
    @ List.map
        (fun (data : set_expr_test_data) ->
          test_case
            (Printf.sprintf "eval_set_expr_%s" data.name)
            `Quick (test_eval_set_expr data)
        )
        set_expr_test_data
end

(** {1 Context Model Options Tests} *)

module TestContextModelOptions = struct
  (** Test default options individually with specific functions *)
  let test_default_options_coherent () =
    let opts = default_options in
      check string "default coherent is undefined" "undefined" opts.coherent

  let test_default_options_model_name () =
    let opts = default_options in
      check string "default model_name is undefined" "undefined" opts.model

  let test_default_options_ubopt () =
    let opts = default_options in
      check bool "default ubopt is false" false opts.ubopt

  (** Test mutable fields individually *)
  let test_model_name_mutable () =
    let opts = { default_options with model = "undefined" } in
      opts.model <- "UB11";
      check string "model can be set" "UB11" opts.model

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
