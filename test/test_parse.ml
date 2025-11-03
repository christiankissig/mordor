open Parse
open Ast

(** Helper functions for testing *)

let check_int_expr msg expected expr =
  match expr with
  | EInt n -> Alcotest.(check bool) msg true (Z.equal n expected)
  | _ -> Alcotest.fail (msg ^ " - Expected EInt")

let check_register_expr msg expected expr =
  match expr with
  | ERegister r -> Alcotest.(check string) msg expected r
  | _ -> Alcotest.fail (msg ^ " - Expected ERegister")

let check_global_expr msg expected expr =
  match expr with
  | EGlobal g -> Alcotest.(check string) msg expected g
  | _ -> Alcotest.fail (msg ^ " - Expected EGlobal")

(** Expression Parsing Tests *)

let test_parse_int () =
  let expr = parse_expr "42" in
    check_int_expr "parsed 42" (Z.of_int 42) expr

let test_parse_hex_int () =
  let expr = parse_expr "0x10" in
    check_int_expr "parsed 0x10" (Z.of_int 16) expr

let test_parse_negative_int () =
  let expr = parse_expr "-5" in
    match expr with
    | EUnOp ("-", EInt n) ->
        Alcotest.(check bool) "parsed -5" true (Z.equal n (Z.of_int 5))
    | _ -> Alcotest.fail "Expected EUnOp with EInt"

let test_parse_register_expr () =
  let expr = parse_expr "r0" in
    check_register_expr "parsed r0" "r0" expr

let test_parse_global_expr () =
  let expr = parse_expr "x" in
    check_global_expr "parsed x" "x" expr

let test_parse_atloc_expr () =
  let expr = parse_expr "@x" in
    match expr with
    | EAtLoc l -> Alcotest.(check string) "parsed @x" "@x" l
    | _ -> Alcotest.fail "Expected EAtLoc"

let test_parse_aset_expr () =
  let expr = parse_expr ".myset" in
    match expr with
    | EASet s -> Alcotest.(check string) "parsed .myset" "myset" s
    | _ -> Alcotest.fail "Expected EASet"

let test_parse_addition () =
  let expr = parse_expr "r0 + r1" in
    match expr with
    | EBinOp (ERegister "r0", "+", ERegister "r1") -> ()
    | _ -> Alcotest.fail "Expected r0 + r1"

let test_parse_subtraction () =
  let expr = parse_expr "x - 1" in
    match expr with
    | EBinOp (EGlobal "x", "-", EInt n) when Z.equal n Z.one -> ()
    | _ -> Alcotest.fail "Expected x - 1"

let test_parse_multiplication () =
  let expr = parse_expr "r0 * 2" in
    match expr with
    | EBinOp (ERegister "r0", "*", EInt n) when Z.equal n (Z.of_int 2) -> ()
    | _ -> Alcotest.fail "Expected r0 * 2"

let test_parse_division () =
  let expr = parse_expr "x / 2" in
    match expr with
    | EBinOp (EGlobal "x", "/", EInt n) when Z.equal n (Z.of_int 2) -> ()
    | _ -> Alcotest.fail "Expected x / 2"

let test_parse_modulo () =
  let expr = parse_expr "x % 3" in
    match expr with
    | EBinOp (EGlobal "x", "%", EInt n) when Z.equal n (Z.of_int 3) -> ()
    | _ -> Alcotest.fail "Expected x % 3"

let test_parse_comparison () =
  let expr = parse_expr "r0 == 1" in
    match expr with
    | EBinOp (ERegister "r0", "==", EInt n) when Z.equal n Z.one -> ()
    | _ -> Alcotest.fail "Expected r0 == 1"

let test_parse_inequality () =
  let expr = parse_expr "r0 != 0" in
    match expr with
    | EBinOp (ERegister "r0", "!=", EInt n) when Z.equal n Z.zero -> ()
    | _ -> Alcotest.fail "Expected r0 != 0"

let test_parse_less_than () =
  let expr = parse_expr "x < 10" in
    match expr with
    | EBinOp (EGlobal "x", "<", EInt _) -> ()
    | _ -> Alcotest.fail "Expected x < 10"

let test_parse_greater_than () =
  let expr = parse_expr "x > 5" in
    match expr with
    | EBinOp (EGlobal "x", ">", EInt _) -> ()
    | _ -> Alcotest.fail "Expected x > 5"

let test_parse_less_equal () =
  let expr = parse_expr "x <= 10" in
    match expr with
    | EBinOp (EGlobal "x", "<=", EInt _) -> ()
    | _ -> Alcotest.fail "Expected x <= 10"

let test_parse_greater_equal () =
  let expr = parse_expr "x >= 5" in
    match expr with
    | EBinOp (EGlobal "x", ">=", EInt _) -> ()
    | _ -> Alcotest.fail "Expected x >= 5"

let test_parse_logical_and () =
  let expr = parse_expr "r0 == 1 && r1 == 1" in
    match expr with
    | EBinOp (EBinOp _, "&&", EBinOp _) -> ()
    | _ -> Alcotest.fail "Expected logical AND"

let test_parse_logical_or () =
  let expr = parse_expr "r0 == 1 || r1 == 1" in
    match expr with
    | EBinOp (EBinOp _, "||", EBinOp _) -> ()
    | _ -> Alcotest.fail "Expected logical OR"

let test_parse_bitwise_and () =
  let expr = parse_expr "x & 0xFF" in
    match expr with
    | EBinOp (EGlobal "x", "&", EInt _) -> ()
    | _ -> Alcotest.fail "Expected bitwise AND"

let test_parse_bitwise_or () =
  let expr = parse_expr "x | y" in
    match expr with
    | EBinOp (EGlobal "x", "|", EGlobal "y") -> ()
    | _ -> Alcotest.fail "Expected bitwise OR"

let test_parse_bitwise_xor () =
  let expr = parse_expr "x ^ y" in
    match expr with
    | EBinOp (EGlobal "x", "^", EGlobal "y") -> ()
    | _ -> Alcotest.fail "Expected bitwise XOR"

let test_parse_unary_not () =
  let expr = parse_expr "!r0" in
    match expr with
    | EUnOp ("!", ERegister "r0") -> ()
    | _ -> Alcotest.fail "Expected unary NOT"

let test_parse_unary_bitwise_not () =
  let expr = parse_expr "~r0" in
    match expr with
    | EUnOp ("~", ERegister "r0") -> ()
    | _ -> Alcotest.fail "Expected unary bitwise NOT"

let test_parse_unary_negate () =
  let expr = parse_expr "-(r0)" in
    match expr with
    | EUnOp ("-", ERegister "r0") -> ()
    | _ -> Alcotest.fail "Expected unary negation"

let test_parse_unary_deref () =
  let expr = parse_expr "*r0" in
    match expr with
    | EUnOp ("*", ERegister "r0") -> ()
    | _ -> Alcotest.fail "Expected dereference"

let test_parse_unary_address_of () =
  let expr = parse_expr "&x" in
    match expr with
    | EUnOp ("&", EGlobal "x") -> ()
    | _ -> Alcotest.fail "Expected address-of"

let test_parse_precedence_add_mul () =
  let expr = parse_expr "1 + 2 * 3" in
    match expr with
    | EBinOp (EInt _, "+", EBinOp (EInt _, "*", EInt _)) -> ()
    | _ -> Alcotest.fail "Expected (1 + (2 * 3)) precedence"

let test_parse_precedence_mul_add () =
  let expr = parse_expr "2 * 3 + 1" in
    match expr with
    | EBinOp (EBinOp (EInt _, "*", EInt _), "+", EInt _) -> ()
    | _ -> Alcotest.fail "Expected ((2 * 3) + 1) precedence"

let test_parse_parentheses () =
  let expr = parse_expr "(1 + 2) * 3" in
    match expr with
    | EBinOp (EBinOp (EInt _, "+", EInt _), "*", EInt _) -> ()
    | _ -> Alcotest.fail "Expected ((1 + 2) * 3) with parentheses"

let test_parse_tuple () =
  let expr = parse_expr "r0, r1" in
    match expr with
    | ETuple (ERegister "r0", ERegister "r1") -> ()
    | _ -> Alcotest.fail "Expected tuple (r0, r1)"

let test_parse_load_expr () =
  let expr = parse_expr "load(relaxed, x)" in
    match expr with
    | ELoad
        { address = EGlobal "x"; load = { mode = Relaxed; volatile = false } }
      -> ()
    | _ -> Alcotest.fail "Expected load(relaxed, x)"

let test_parse_forall () =
  let expr = parse_expr "forall r0" in
    match expr with
    | EUnOp ("forall", ERegister "r0") -> ()
    | _ -> Alcotest.fail "Expected forall r0"

let test_parse_complex_expr () =
  let expr = parse_expr "(r0 + 1) * (r1 - 2)" in
    match expr with
    | EBinOp (EBinOp _, "*", EBinOp _) -> ()
    | _ -> Alcotest.fail "Expected complex expression"

let test_parse_in_operator () =
  let expr = parse_expr "r0 in .myset" in
    match expr with
    | EBinOp (ERegister "r0", "in", EASet _) -> ()
    | _ -> Alcotest.fail "Expected r0 in .myset"

let test_parse_notin_operator () =
  let expr = parse_expr "r0 notin .myset" in
    match expr with
    | EBinOp (ERegister "r0", "notin", EASet _) -> ()
    | _ -> Alcotest.fail "Expected r0 notin .myset"

(** Statement Parsing Tests *)

let test_parse_register_store () =
  let src = "%% r0 := 42" in
  let ast = parse src in
    match ast.program with
    | [ SRegisterStore { register = "r0"; expr = EInt n } ]
      when Z.equal n (Z.of_int 42) -> ()
    | _ -> Alcotest.fail "Expected r0 := 42"

let test_parse_register_store_expr () =
  let src = "%% r0 := r1 + 1" in
  let ast = parse src in
    match ast.program with
    | [ SRegisterStore { register = "r0"; expr = EBinOp _ } ] -> ()
    | _ -> Alcotest.fail "Expected r0 := r1 + 1"

let test_parse_global_store_simple () =
  let src = "%% x := 1" in
  let ast = parse src in
    match ast.program with
    | [
     SGlobalStore
       {
         global = "x";
         expr = EInt n;
         assign = { mode = Relaxed; volatile = false };
       };
    ]
      when Z.equal n Z.one -> ()
    | _ -> Alcotest.fail "Expected x := 1"

let test_parse_global_store_relaxed () =
  let src = "%% x :rlx= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { global = "x"; assign = { mode = Relaxed; _ }; _ } ] -> ()
    | _ -> Alcotest.fail "Expected x :rlx= 1"

let test_parse_global_store_release () =
  let src = "%% x :rel= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { global = "x"; assign = { mode = Release; _ }; _ } ] -> ()
    | _ -> Alcotest.fail "Expected x :rel= 1"

let test_parse_global_store_acquire () =
  let src = "%% x :acq= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { global = "x"; assign = { mode = Acquire; _ }; _ } ] -> ()
    | _ -> Alcotest.fail "Expected x :acq= 1"

let test_parse_global_store_sc () =
  let src = "%% x :sc= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { global = "x"; assign = { mode = SC; _ }; _ } ] -> ()
    | _ -> Alcotest.fail "Expected x :sc= 1"

let test_parse_register_load_global () =
  let src = "%% r0 := x" in
  let ast = parse src in
    match ast.program with
    | [ SRegisterStore { register = "r0"; expr = EGlobal "x" } ] -> ()
    | _ -> Alcotest.fail "Expected r0 := x"

let test_parse_deref_store () =
  let src = "%% *r0 := 42" in
  let ast = parse src in
    match ast.program with
    | [ SStore { address = ERegister "r0"; expr = EInt _; _ } ] -> ()
    | _ -> Alcotest.fail "Expected *r0 := 42"

let test_parse_load_explicit () =
  let src = "%% r0 := load(acquire, x)" in
  let ast = parse src in
    match ast.program with
    | [
     SRegisterStore
       { register = "r0"; expr = ELoad { load = { mode = Acquire; _ }; _ } };
    ] -> ()
    | _ -> Alcotest.fail "Expected r0 := load(acquire, x)"

let test_parse_store_explicit () =
  let src = "%% store(release, x, 1)" in
  let ast = parse src in
    match ast.program with
    | [ SStore { assign = { mode = Release; _ }; _ } ] -> ()
    | _ -> Alcotest.fail "Expected store(release, x, 1)"

let test_parse_if_simple () =
  let src = "%% if (r0 == 1) r1 := 2" in
  let ast = parse src in
    match ast.program with
    | [ SIf { condition = EBinOp _; then_body = _; else_body = None } ] -> ()
    | _ -> Alcotest.fail "Expected if statement"

let test_parse_if_else () =
  let src = "%% if (r0 == 1) r1 := 2 else r1 := 3" in
  let ast = parse src in
    match ast.program with
    | [ SIf { condition = EBinOp _; then_body = _; else_body = Some _ } ] -> ()
    | _ -> Alcotest.fail "Expected if-else statement"

let test_parse_if_block () =
  let src = "%% if (r0 == 1) { r1 := 2; r2 := 3 }" in
  let ast = parse src in
    match ast.program with
    | [ SIf { then_body = [ _; _ ]; _ } ] -> ()
    | _ -> Alcotest.fail "Expected if with block"

let test_parse_while_loop () =
  let src = "%% while (r0 < 10) r0 := r0 + 1" in
  let ast = parse src in
    match ast.program with
    | [ SWhile { condition = EBinOp _; body = _ } ] -> ()
    | _ -> Alcotest.fail "Expected while loop"

let test_parse_do_while () =
  let src = "%% do r0 := r0 + 1 while (r0 < 10)" in
  let ast = parse src in
    match ast.program with
    | [ SDo { body = _; condition = EBinOp _ } ] -> ()
    | _ -> Alcotest.fail "Expected do-while loop"

let test_parse_qwhile_loop () =
  let src = "%% qdo r0 := r0 + 1 qwhile (r0 < 10)" in
  let ast = parse src in
    match ast.program with
    | [ SQDo { body = _; condition = EBinOp _ } ] -> ()
    | _ -> Alcotest.fail "Expected qdo-qwhile loop"

let test_parse_fence () =
  let src = "%% fence(sc)" in
  let ast = parse src in
    match ast.program with
    | [ SFence { mode = SC } ] -> ()
    | _ -> Alcotest.fail "Expected fence(sc)"

let test_parse_fence_acquire () =
  let src = "%% fence(acquire)" in
  let ast = parse src in
    match ast.program with
    | [ SFence { mode = Acquire } ] -> ()
    | _ -> Alcotest.fail "Expected fence(acquire)"

let test_parse_cas () =
  let src = "%% r0 := cas(sc, x, 0, 1)" in
  let ast = parse src in
    match ast.program with
    | [ SCAS { register = "r0"; mode = SC; _ } ] -> ()
    | _ -> Alcotest.fail "Expected CAS operation"

let test_parse_fadd () =
  let src = "%% r0 := fadd(relaxed, x, 1)" in
  let ast = parse src in
    match ast.program with
    | [ SFADD { register = "r0"; mode = Relaxed; _ } ] -> ()
    | _ -> Alcotest.fail "Expected FADD operation"

let test_parse_lock () =
  let src = "%% lock" in
  let ast = parse src in
    match ast.program with
    | [ SLock { global = None } ] -> ()
    | _ -> Alcotest.fail "Expected lock"

let test_parse_lock_with_global () =
  let src = "%% lock mutex" in
  let ast = parse src in
    match ast.program with
    | [ SLock { global = Some "mutex" } ] -> ()
    | _ -> Alcotest.fail "Expected lock mutex"

let test_parse_unlock () =
  let src = "%% unlock" in
  let ast = parse src in
    match ast.program with
    | [ SUnlock { global = None } ] -> ()
    | _ -> Alcotest.fail "Expected unlock"

let test_parse_unlock_with_global () =
  let src = "%% unlock mutex" in
  let ast = parse src in
    match ast.program with
    | [ SUnlock { global = Some "mutex" } ] -> ()
    | _ -> Alcotest.fail "Expected unlock mutex"

let test_parse_malloc_stmt () =
  let src = "%% r0 := malloc(8)" in
  let ast = parse src in
    match ast.program with
    | [ SMalloc { register = "r0"; size = EInt _; _ } ] -> ()
    | _ -> Alcotest.fail "Expected r0 := malloc(8)"

let test_parse_free () =
  let src = "%% free(r0)" in
  let ast = parse src in
    match ast.program with
    | [ SFree { register = "r0" } ] -> ()
    | _ -> Alcotest.fail "Expected free(r0)"

let test_parse_labeled_stmt () =
  let src = "%% `label` x := 1" in
  let ast = parse src in
    match ast.program with
    | [ SLabeled { label = [ "label" ]; stmt = SGlobalStore _ } ] -> ()
    | _ -> Alcotest.fail "Expected labeled statement"

let test_parse_multiple_labels () =
  let src = "%% `label1` `label2` x := 1" in
  let ast = parse src in
    match ast.program with
    | [ SLabeled { label = [ "label2"; "label1" ]; stmt = SGlobalStore _ } ] ->
        ()
    | _ -> Alcotest.fail "Expected multiple labels"

let test_parse_multiple_statements () =
  let src = "%% x := 1; y := 2; r0 := x" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore _; SGlobalStore _; SRegisterStore _ ] -> ()
    | _ -> Alcotest.fail "Expected 3 statements"

let test_parse_thread_parallel () =
  let src = "%% {x := 1} ||| {y := 2}" in
  let ast = parse src in
    match ast.program with
    | [
     SThreads
       {
         threads =
           [
             [ SGlobalStore { global = "x"; _ } ];
             [ SGlobalStore { global = "y"; _ } ];
           ];
       };
    ] -> ()
    | _ -> Alcotest.fail "Expected parallel threads"

let test_parse_multiple_threads () =
  let src = "%% {x := 1} ||| {y := 2} ||| {r0 := x}" in
  let ast = parse src in
    match ast.program with
    | [
     SThreads
       {
         threads =
           [ [ SGlobalStore _ ]; [ SGlobalStore _ ]; [ SRegisterStore _ ] ];
       };
    ] -> ()
    | _ -> Alcotest.fail "Expected 3 threads"

(** Configuration Parsing Tests *)

let test_parse_config_name () =
  let src = "name = mytest\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config -> Alcotest.(check string) "config name" "mytest" config.name
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_name_with_numbers () =
  let src = "name = test123\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config -> Alcotest.(check string) "config name" "test123" config.name
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_values () =
  let src = "values = {0, 1, 2}\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check int) "3 values" 3 (List.length config.values)
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_values_hex () =
  let src = "values = {0x0, 0x1, 0xFF}\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check int) "3 hex values" 3 (List.length config.values)
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_defacto () =
  let src = "[r0 = 1]\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check int)
          "1 defacto constraint" 1
          (List.length config.defacto)
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_multiple_defacto () =
  let src = "[r0 = 1]\n[x = 0]\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check int)
          "2 defacto constraints" 2
          (List.length config.defacto)
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_constraint () =
  let src = "[[r0 = 1]]\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check int) "1 constraint" 1 (List.length config.constraint_)
    | None -> Alcotest.fail "Expected config section"

let test_parse_config_multiple_constraints () =
  let src = "[[r0 = 1]]\n[[x = 0]]\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check int) "2 constraints" 2 (List.length config.constraint_)
    | None -> Alcotest.fail "Expected config section"

let test_parse_full_config () =
  let src = "name = test\nvalues = {0, 1}\n[x = 0]\n[[r0 = 1]]\n%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check string) "name" "test" config.name;
        Alcotest.(check int) "values" 2 (List.length config.values);
        Alcotest.(check int) "defacto" 1 (List.length config.defacto);
        Alcotest.(check int) "constraint" 1 (List.length config.constraint_)
    | None -> Alcotest.fail "Expected config section"

let test_parse_minimal_config () =
  let src = "%%r := 0" in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check string) "empty name" "" config.name;
        Alcotest.(check int) "no values" 0 (List.length config.values)
    | None -> Alcotest.fail "Expected config section"

(** Assertion Parsing Tests *)

let test_parse_assertion_allow () =
  let src = "x := 1;\n%% allow r0 = 1 []" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { outcome = "allow"; condition = EBinOp _; _ }) -> ()
    | _ -> Alcotest.fail "Expected allow assertion"

let test_parse_assertion_forbid () =
  let src = "x := 1;\n%% forbid r0 = 1 []" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { outcome = "forbid"; _ }) -> ()
    | _ -> Alcotest.fail "Expected forbid assertion"

let test_parse_assertion_with_model () =
  let src = "x := 1;\n%% allow r0 = 1 [sc]" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { outcome = "allow"; model = Some "sc"; _ }) -> ()
    | _ -> Alcotest.fail "Expected assertion with sc model"

let test_parse_assertion_complex_condition () =
  let src = "x := 1;\n%% forbid r0 = 1 && r1 = 0 []" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { condition = EBinOp (_, "&&", _); _ }) -> ()
    | _ -> Alcotest.fail "Expected complex condition"

let test_parse_assertion_model_only () =
  let src = "x := 1;\n%% [rc11]" in
  let ast = parse src in
    match ast.assertion with
    | Some (AModel { model = "rc11" }) -> ()
    | _ -> Alcotest.fail "Expected model-only assertion"

let test_parse_no_assertion () =
  let src = "x := 1" in
  let ast = parse src in
    match ast.assertion with
    | None -> ()
    | _ -> Alcotest.fail "Expected no assertion"

(** Full Litmus Test Parsing *)

let test_parse_message_passing () =
  let src =
    "name = MP\n\
     values = {0, 1}\n\
     %%\n\
     {x := 1; y := 1} ||| {r0 := y; r1 := x}\n\
     %% forbid r0 = 1 && r1 = 0 []"
  in
  let ast = parse src in
    ( match ast.config with
    | Some config -> Alcotest.(check string) "MP test name" "MP" config.name
    | None -> Alcotest.fail "Expected config section"
    );
    match ast.assertion with
    | Some (AOutcome { outcome = "forbid"; _ }) -> ()
    | _ -> Alcotest.fail "Expected forbid assertion"

let test_parse_store_buffer () =
  let src =
    "name = SB\n\
     %%\n\
     {x := 1; r0 := y} ||| {y := 1; r1 := x}\n\
     %% forbid r0 = 0 && r1 = 0 []"
  in
  let ast = parse src in
    match ast.config with
    | Some config -> Alcotest.(check string) "SB test name" "SB" config.name
    | None -> Alcotest.fail "Expected config section"

let test_parse_load_buffering () =
  let src =
    "%%\n{r0 := x; y := 1} ||| {r1 := y; x := 1}\n%% forbid r0 = 1 && r1 = 1 []"
  in
  let ast = parse src in
    ()

let test_parse_single_thread () =
  let src = "%% x := 1; r0 := x" in
  let ast = parse src in
    Alcotest.(check int) "2 statements" 2 (List.length ast.program)

let test_parse_with_comments () =
  let src = "// This is a comment\n%% x := 1 // another comment\n" in
  let ast = parse src in
    Alcotest.(check int) "1 statement" 1 (List.length ast.program)

let test_parse_complex_litmus () =
  let src =
    "name = Complex\n\
     values = {0, 1, 2}\n\
     [x = 0]\n\
     [y = 0]\n\
     [[r0 != r1]]\n\
     %%\n\
     {`thread1` x :rel= 1; fence(sc); y :rel= 1} |||\n\
     {`thread2` r0 := y; fence(sc); r1 := x}\n\
     %% forbid r0 = 1 && r1 = 0 [sc]"
  in
  let ast = parse src in
    match ast.config with
    | Some config ->
        Alcotest.(check string) "name" "Complex" config.name;
        Alcotest.(check int) "values" 3 (List.length config.values);
        Alcotest.(check int) "defacto" 2 (List.length config.defacto);
        Alcotest.(check int) "constraint" 1 (List.length config.constraint_)
    | None -> Alcotest.fail "Expected config section"

(** Test Suite *)

let suite =
  ( "Parser",
    [
      (* Expression parsing tests *)
      Alcotest.test_case "Parse integer" `Quick test_parse_int;
      Alcotest.test_case "Parse hex integer" `Quick test_parse_hex_int;
      Alcotest.test_case "Parse negative integer" `Quick test_parse_negative_int;
      Alcotest.test_case "Parse register" `Quick test_parse_register_expr;
      Alcotest.test_case "Parse global" `Quick test_parse_global_expr;
      Alcotest.test_case "Parse atloc" `Quick test_parse_atloc_expr;
      (* TODO Alcotest.test_case "Parse aset" `Quick test_parse_aset_expr; *)
      Alcotest.test_case "Parse addition" `Quick test_parse_addition;
      Alcotest.test_case "Parse subtraction" `Quick test_parse_subtraction;
      Alcotest.test_case "Parse multiplication" `Quick test_parse_multiplication;
      Alcotest.test_case "Parse division" `Quick test_parse_division;
      Alcotest.test_case "Parse modulo" `Quick test_parse_modulo;
      Alcotest.test_case "Parse comparison" `Quick test_parse_comparison;
      Alcotest.test_case "Parse inequality" `Quick test_parse_inequality;
      Alcotest.test_case "Parse less than" `Quick test_parse_less_than;
      Alcotest.test_case "Parse greater than" `Quick test_parse_greater_than;
      Alcotest.test_case "Parse less equal" `Quick test_parse_less_equal;
      Alcotest.test_case "Parse greater equal" `Quick test_parse_greater_equal;
      Alcotest.test_case "Parse logical and" `Quick test_parse_logical_and;
      Alcotest.test_case "Parse logical or" `Quick test_parse_logical_or;
      Alcotest.test_case "Parse bitwise and" `Quick test_parse_bitwise_and;
      Alcotest.test_case "Parse bitwise or" `Quick test_parse_bitwise_or;
      Alcotest.test_case "Parse bitwise xor" `Quick test_parse_bitwise_xor;
      Alcotest.test_case "Parse unary not" `Quick test_parse_unary_not;
      Alcotest.test_case "Parse unary bitwise not" `Quick
        test_parse_unary_bitwise_not;
      Alcotest.test_case "Parse unary negate" `Quick test_parse_unary_negate;
      Alcotest.test_case "Parse unary deref" `Quick test_parse_unary_deref;
      Alcotest.test_case "Parse address-of" `Quick test_parse_unary_address_of;
      Alcotest.test_case "Parse precedence add/mul" `Quick
        test_parse_precedence_add_mul;
      Alcotest.test_case "Parse precedence mul/add" `Quick
        test_parse_precedence_mul_add;
      Alcotest.test_case "Parse parentheses" `Quick test_parse_parentheses;
      Alcotest.test_case "Parse tuple" `Quick test_parse_tuple;
      Alcotest.test_case "Parse load expr" `Quick test_parse_load_expr;
      Alcotest.test_case "Parse forall" `Quick test_parse_forall;
      Alcotest.test_case "Parse complex expression" `Quick
        test_parse_complex_expr;
      Alcotest.test_case "Parse in operator" `Quick test_parse_in_operator;
      Alcotest.test_case "Parse notin operator" `Quick test_parse_notin_operator;
      (* Statement parsing tests *)
      Alcotest.test_case "Parse register store" `Quick test_parse_register_store;
      Alcotest.test_case "Parse register store expr" `Quick
        test_parse_register_store_expr;
      Alcotest.test_case "Parse global store simple" `Quick
        test_parse_global_store_simple;
      Alcotest.test_case "Parse global store relaxed" `Quick
        test_parse_global_store_relaxed;
      Alcotest.test_case "Parse global store release" `Quick
        test_parse_global_store_release;
      Alcotest.test_case "Parse global store acquire" `Quick
        test_parse_global_store_acquire;
      Alcotest.test_case "Parse global store sc" `Quick
        test_parse_global_store_sc;
      Alcotest.test_case "Parse register load global" `Quick
        test_parse_register_load_global;
      Alcotest.test_case "Parse deref store" `Quick test_parse_deref_store;
      Alcotest.test_case "Parse load explicit" `Quick test_parse_load_explicit;
      Alcotest.test_case "Parse store explicit" `Quick test_parse_store_explicit;
      Alcotest.test_case "Parse if simple" `Quick test_parse_if_simple;
      Alcotest.test_case "Parse if-else" `Quick test_parse_if_else;
      Alcotest.test_case "Parse if block" `Quick test_parse_if_block;
      Alcotest.test_case "Parse while loop" `Quick test_parse_while_loop;
      Alcotest.test_case "Parse do-while" `Quick test_parse_do_while;
      Alcotest.test_case "Parse qwhile loop" `Quick test_parse_qwhile_loop;
      Alcotest.test_case "Parse fence" `Quick test_parse_fence;
      Alcotest.test_case "Parse fence acquire" `Quick test_parse_fence_acquire;
      Alcotest.test_case "Parse CAS" `Quick test_parse_cas;
      Alcotest.test_case "Parse FADD" `Quick test_parse_fadd;
      Alcotest.test_case "Parse lock" `Quick test_parse_lock;
      Alcotest.test_case "Parse lock with global" `Quick
        test_parse_lock_with_global;
      Alcotest.test_case "Parse unlock" `Quick test_parse_unlock;
      Alcotest.test_case "Parse unlock with global" `Quick
        test_parse_unlock_with_global;
      Alcotest.test_case "Parse malloc stmt" `Quick test_parse_malloc_stmt;
      Alcotest.test_case "Parse free" `Quick test_parse_free;
      Alcotest.test_case "Parse labeled statement" `Quick
        test_parse_labeled_stmt;
      Alcotest.test_case "Parse multiple labels" `Quick
        test_parse_multiple_labels;
      Alcotest.test_case "Parse multiple statements" `Quick
        test_parse_multiple_statements;
      Alcotest.test_case "Parse thread parallel" `Quick
        test_parse_thread_parallel;
      Alcotest.test_case "Parse multiple threads" `Quick
        test_parse_multiple_threads;
      (* Configuration parsing tests *)
      Alcotest.test_case "Parse config name" `Quick test_parse_config_name;
      Alcotest.test_case "Parse config name with numbers" `Quick
        test_parse_config_name_with_numbers;
      Alcotest.test_case "Parse config values" `Quick test_parse_config_values;
      Alcotest.test_case "Parse config values hex" `Quick
        test_parse_config_values_hex;
      Alcotest.test_case "Parse config defacto" `Quick test_parse_config_defacto;
      Alcotest.test_case "Parse config multiple defacto" `Quick
        test_parse_config_multiple_defacto;
      Alcotest.test_case "Parse config constraint" `Quick
        test_parse_config_constraint;
      Alcotest.test_case "Parse config multiple constraints" `Quick
        test_parse_config_multiple_constraints;
      Alcotest.test_case "Parse full config" `Quick test_parse_full_config;
      Alcotest.test_case "Parse minimal config" `Quick test_parse_minimal_config;
      (* Assertion parsing tests *)
      Alcotest.test_case "Parse allow assertion" `Quick
        test_parse_assertion_allow;
      Alcotest.test_case "Parse forbid assertion" `Quick
        test_parse_assertion_forbid;
      Alcotest.test_case "Parse assertion with model" `Quick
        test_parse_assertion_with_model;
      Alcotest.test_case "Parse assertion complex condition" `Quick
        test_parse_assertion_complex_condition;
      Alcotest.test_case "Parse assertion model only" `Quick
        test_parse_assertion_model_only;
      Alcotest.test_case "Parse no assertion" `Quick test_parse_no_assertion;
      (* Full litmus test parsing *)
      Alcotest.test_case "Parse message passing" `Quick
        test_parse_message_passing;
      Alcotest.test_case "Parse store buffer" `Quick test_parse_store_buffer;
      Alcotest.test_case "Parse load buffering" `Quick test_parse_load_buffering;
      Alcotest.test_case "Parse single thread" `Quick test_parse_single_thread;
      Alcotest.test_case "Parse with comments" `Quick test_parse_with_comments;
      Alcotest.test_case "Parse complex litmus" `Quick test_parse_complex_litmus;
    ]
  )
