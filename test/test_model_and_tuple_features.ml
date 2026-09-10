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
  (* [events] is the execution's event set. A relation only relates events the
     execution runs, and a membership test naming one it does not run is not
     answered - so any event a test asks about has to be in here, whether or not
     it is an endpoint of [ppo_pairs]. *)
  (** Helper to create minimal execution *)
  let make_test_execution ?(events = []) ppo_pairs =
    let ppo = USet.create () in
      List.iter (fun (a, b) -> USet.add ppo (a, b) |> ignore) ppo_pairs;
      let e = USet.create () in
        List.iter
          (fun (a, b) ->
            USet.add e a |> ignore;
            USet.add e b |> ignore
          )
          ppo_pairs;
        List.iter (fun ev -> USet.add e ev |> ignore) events;
        {
          id = 0;
          e;
          rf = USet.create ();
          rmw = USet.create ();
          dp = USet.create ();
          ppo;
          fwd = USet.create ();
          we = USet.create ();
          ex_p = [];
          justifications = [];
          co = None;
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
    events : int list;  (** Events the execution runs, beyond ppo endpoints. *)
    expr_builder : unit -> expr;
    expected : bool;
    description : string;
  }

  let set_expr_test_data =
    [
      {
        name = "in_true";
        ppo_pairs = [ (3, 4) ];
        events = [];
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
        events = [ 3; 4 ];
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
        events = [ 3; 4 ];
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

  let test_eval_set_expr
      { ppo_pairs; events; expr_builder; expected; description; _ } () =
    let structure = make_test_structure () in
    let execution = make_test_execution ~events ppo_pairs in
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
  (* The coherence model applied when a litmus test names none. It has to be a
     model that checks something: [undefined] verifies only RMW atomicity, so a
     test written without a model was getting no coherence and no thin-air
     check at all. *)
  (** Test default options individually with specific functions *)
  let test_default_options_coherent () =
    let opts = default_options in
      check string "default coherent is smrd" "smrd" opts.coherent

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

  (* A name the table does not have is fatal. Before this it warned and left the
     coherence model at whatever was already in effect -- the [smrd] default --
     so a [C11] or [RA] test was answered by sMRD without anything saying so.
     That is what put 43 files in litmus-tests-{cpp,promising,ra}/. *)
  (* [make_context] stores the options record it is given, and
     [apply_model_options] mutates it, so pass a copy -- otherwise a test that
     applies [rc11] leaves [default_options.coherent] set for whatever runs
     next. *)
  let apply model opts =
    let ctx = make_context { opts with exhaustive = opts.exhaustive } () in
      apply_model_options ctx model;
      ctx

  let contains haystack needle =
    let n = String.length needle and h = String.length haystack in
    let rec go i =
      i + n <= h && (String.sub haystack i n = needle || go (i + 1))
    in
      go 0

  let test_unknown_model_fails () =
    match
      apply "c11" { default_options with allow_unknown_model = false } |> ignore
    with
    | () -> fail "unknown model did not raise"
    | exception Failure msg ->
        check bool "names the model" true (contains msg "\"c11\"");
        check bool "names the escape hatch" true
          (contains msg "--allow-unknown-model")

  (* [promising] is unknown like any other, but says why: it is operational, so
     there is no axiomatic model to map it onto rather than one nobody wrote. *)
  let test_promising_says_why () =
    match
      apply "promising" { default_options with allow_unknown_model = false }
      |> ignore
    with
    | () -> fail "promising did not raise"
    | exception Failure msg ->
        check bool "explains promising" true (contains msg "operational")

  let test_unknown_model_allowed_leaves_coherent () =
    let opts = { default_options with allow_unknown_model = true } in
    let ctx = apply "c11" opts in
      check string "coherence model untouched" "smrd" ctx.options.coherent;
      check string "model name recorded" "c11" ctx.options.model

  (* [coherent = None] in the table is the other case: a name MoRDor knows and
     deliberately maps onto the default. It must keep working. *)
  let test_known_model_mapped_to_default_is_not_unknown () =
    let ctx = apply "sevcik" default_options in
      check string "coherence model left at the default" "smrd"
        ctx.options.coherent;
      check string "model name recorded" "sevcik" ctx.options.model

  let test_known_model_sets_coherent () =
    let ctx = apply "rc11" default_options in
      check string "rc11 applied" "rc11" ctx.options.coherent

  (* [_] means "any model". The grammar maps UNDERSCORE to the empty string, so
     that -- not ["_"] -- is the name that reaches the table, and it has to be
     known or the #86 check rejects every [_] annotation. *)
  let test_underscore_model_is_known () =
    let ctx = apply "" default_options in
      check string "coherence model left at the default" "smrd"
        ctx.options.coherent

  let test_default_options_allow_unknown_model () =
    check bool "unknown models are fatal by default" false
      default_options.allow_unknown_model

  let suite =
    [
      test_case "default_options_coherent" `Quick test_default_options_coherent;
      test_case "default_options_model_name" `Quick
        test_default_options_model_name;
      test_case "default_options_ubopt" `Quick test_default_options_ubopt;
      test_case "model_name_mutable" `Quick test_model_name_mutable;
      test_case "ubopt_mutable" `Quick test_ubopt_mutable;
      test_case "default_options_allow_unknown_model" `Quick
        test_default_options_allow_unknown_model;
      test_case "unknown_model_fails" `Quick test_unknown_model_fails;
      test_case "promising_says_why" `Quick test_promising_says_why;
      test_case "unknown_model_allowed_leaves_coherent" `Quick
        test_unknown_model_allowed_leaves_coherent;
      test_case "known_model_mapped_to_default_is_not_unknown" `Quick
        test_known_model_mapped_to_default_is_not_unknown;
      test_case "known_model_sets_coherent" `Quick test_known_model_sets_coherent;
      test_case "underscore_model_is_known" `Quick test_underscore_model_is_known;
    ]
end

(** {1 Combined Test Suite} *)

let suite =
  ( "Model and Tuple Features",
    TestModelAssertions.suite
    @ TestSetMembership.suite
    @ TestContextModelOptions.suite
  )
