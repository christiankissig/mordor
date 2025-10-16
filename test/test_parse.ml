open Parse

(** Helper functions for testing *)

let check_token_type msg expected actual =
  Alcotest.(check bool) msg true (expected = actual.typ)

let check_token_list msg expected_types tokens =
  let actual_types = List.map (fun t -> t.typ) tokens in
    Alcotest.(check int)
      (msg ^ " - count")
      (List.length expected_types)
      (List.length actual_types);
    List.iter2
      (fun exp act -> Alcotest.(check bool) msg true (exp = act))
      expected_types actual_types

(** Tokenization Tests *)

let test_tokenize_keywords () =
  let tokens = tokenize "nonatomic na relaxed rlx release rel acquire acq" in
  let expected =
    [
      NONATOMIC;
      NONATOMIC;
      RELAXED;
      RELAXED;
      RELEASE;
      RELEASE;
      ACQUIRE;
      ACQUIRE;
      EOF;
    ]
  in
    check_token_list "memory order keywords" expected tokens

let test_tokenize_control_flow () =
  let tokens = tokenize "if else while do skip fence" in
  let expected = [ IF; ELSE; WHILE; DO; SKIP; FENCE; EOF ] in
    check_token_list "control flow keywords" expected tokens

let test_tokenize_atomic_ops () =
  let tokens = tokenize "FADD fadd CAS cas load store" in
  let expected = [ FADD; FADD; CAS; CAS; LOAD; STORE; EOF ] in
    check_token_list "atomic operation keywords" expected tokens

let test_tokenize_numbers () =
  let tokens = tokenize "0 42 123 0x10 0xFF" in
    List.iter
      (fun tok ->
        match tok.typ with
        | INT _ -> ()
        | EOF -> ()
        | _ -> Alcotest.fail "Expected INT token"
      )
      tokens

let test_tokenize_registers () =
  let tokens = tokenize "r0 r1 r42 rax" in
  let check_reg tok expected =
    match tok.typ with
    | REGISTER r -> Alcotest.(check string) "register name" expected r
    | _ -> Alcotest.fail "Expected REGISTER token"
  in
    check_reg (List.nth tokens 0) "r0";
    check_reg (List.nth tokens 1) "r1";
    check_reg (List.nth tokens 2) "r42";
    check_reg (List.nth tokens 3) "rax"

let test_tokenize_globals () =
  let tokens = tokenize "x y flag counter" in
  let check_global tok expected =
    match tok.typ with
    | GLOBAL g -> Alcotest.(check string) "global name" expected g
    | _ -> Alcotest.fail "Expected GLOBAL token"
  in
    check_global (List.nth tokens 0) "x";
    check_global (List.nth tokens 1) "y";
    check_global (List.nth tokens 2) "flag";
    check_global (List.nth tokens 3) "counter"

let test_tokenize_atloc () =
  let tokens = tokenize "@x @loc @addr" in
  let check_atloc tok expected =
    match tok.typ with
    | ATLOC l -> Alcotest.(check string) "atloc name" expected l
    | _ -> Alcotest.fail "Expected ATLOC token"
  in
    check_atloc (List.nth tokens 0) "@x";
    check_atloc (List.nth tokens 1) "@loc";
    check_atloc (List.nth tokens 2) "@addr"

let test_tokenize_strings () =
  let tokens = tokenize "\"hello\" \"world\"" in
    match (List.nth tokens 0).typ with
    | STRING s -> Alcotest.(check string) "string content" "hello" s
    | _ -> Alcotest.fail "Expected STRING token"

let test_tokenize_backticks () =
  let tokens = tokenize "`label1` `label2`" in
    match (List.nth tokens 0).typ with
    | BACKTICK l -> Alcotest.(check string) "backtick label" "label1" l
    | _ -> Alcotest.fail "Expected BACKTICK token"

let test_tokenize_assignment_ops () =
  let tokens = tokenize ":= :rlx= :rel= :acq= :sc=" in
  let expected = [ ASSIGN; COLONRLX; COLONREL; COLONACQ; COLONSC; EOF ] in
    check_token_list "assignment operators" expected tokens

let test_tokenize_volatile_assignment_ops () =
  let tokens = tokenize ":v= :vrlx= :vrel= :vacq= :vsc=" in
  let expected = [ COLONV; COLONVRLX; COLONVREL; COLONVACQ; COLONVSC; EOF ] in
    check_token_list "volatile assignment operators" expected tokens

let test_tokenize_comparison_ops () =
  let tokens = tokenize "= != < > <= >=" in
  let expected = [ EQ; NEQ; LT; GT; LEQ; GEQ; EOF ] in
    check_token_list "comparison operators" expected tokens

let test_tokenize_arithmetic_ops () =
  let tokens = tokenize "+ - * /" in
  let expected = [ PLUS; MINUS; STAR; SLASH; EOF ] in
    check_token_list "arithmetic operators" expected tokens

let test_tokenize_logical_ops () =
  let tokens = tokenize "&& || !" in
  let expected = [ AND; OR; BANG; EOF ] in
    check_token_list "logical operators" expected tokens

let test_tokenize_bitwise_ops () =
  let tokens = tokenize "& | ^ ~" in
  let expected = [ AMPERSAND; PIPE; CARET; TILDE; EOF ] in
    check_token_list "bitwise operators" expected tokens

let test_tokenize_arrows () =
  let tokens = tokenize "=> ~~>" in
  let expected = [ ARROW; RARROW; EOF ] in
    check_token_list "arrow operators" expected tokens

let test_tokenize_brackets () =
  let tokens = tokenize "( ) { } [ ] [[ ]]" in
  let expected =
    [
      LPAREN;
      RPAREN;
      LBRACE;
      RBRACE;
      LBRACKET;
      RBRACKET;
      LDBRACKET;
      RDBRACKET;
      EOF;
    ]
  in
    check_token_list "brackets" expected tokens

let test_tokenize_parallel () =
  let tokens = tokenize "|||" in
    check_token_type "parallel operator" PARALLEL (List.nth tokens 0)

let test_tokenize_punctuation () =
  let tokens = tokenize "; , . # %%" in
  let expected = [ SEMICOLON; COMMA; DOT; HASH; PERCENT; EOF ] in
    check_token_list "punctuation" expected tokens

let test_tokenize_comments () =
  let tokens = tokenize "x // this is a comment\ny" in
  (* Comments should be filtered out *)
  let non_eof = List.filter (fun t -> t.typ <> EOF) tokens in
    Alcotest.(check int) "comments filtered" 2 (List.length non_eof)

let test_tokenize_whitespace () =
  let tokens = tokenize "  x   \n  y  \t z  " in
  let non_eof = List.filter (fun t -> t.typ <> EOF) tokens in
    Alcotest.(check int) "whitespace ignored" 3 (List.length non_eof)

(** Expression Parsing Tests *)

let test_parse_int () =
  let p = make_parser "42" in
  let expr = parse_expr p () in
    match expr with
    | EInt n -> Alcotest.(check bool) "parsed 42" true (Z.equal n (Z.of_int 42))
    | _ -> Alcotest.fail "Expected EInt"

let test_parse_hex_int () =
  let p = make_parser "0x10" in
  let expr = parse_expr p () in
    match expr with
    | EInt n ->
        Alcotest.(check bool) "parsed 0x10" true (Z.equal n (Z.of_int 16))
    | _ -> Alcotest.fail "Expected EInt"

let test_parse_register_expr () =
  let p = make_parser "r0" in
  let expr = parse_expr p () in
    match expr with
    | ERegister r -> Alcotest.(check string) "parsed r0" "r0" r
    | _ -> Alcotest.fail "Expected ERegister"

let test_parse_global_expr () =
  let p = make_parser "x" in
  let expr = parse_expr p () in
    match expr with
    | EGlobal g -> Alcotest.(check string) "parsed x" "x" g
    | _ -> Alcotest.fail "Expected EGlobal"

let test_parse_atloc_expr () =
  let p = make_parser "@loc" in
  let expr = parse_expr p () in
    match expr with
    | EAtLoc l -> Alcotest.(check string) "parsed @loc" "@loc" l
    | _ -> Alcotest.fail "Expected EAtLoc"

let test_parse_aset_expr () =
  let p = make_parser ".x" in
  let expr = parse_expr p () in
    match expr with
    | EASet s -> Alcotest.(check string) "parsed .x" "x" s
    | _ -> Alcotest.fail "Expected EASet"

let test_parse_addition () =
  let p = make_parser "1 + 2" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EInt _, "+", EInt _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with +"

let test_parse_subtraction () =
  let p = make_parser "5 - 3" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EInt _, "-", EInt _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with -"

let test_parse_multiplication () =
  let p = make_parser "3 * 4" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EInt _, "*", EInt _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with *"

let test_parse_division () =
  let p = make_parser "8 / 2" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EInt _, "/", EInt _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with /"

let test_parse_comparison () =
  let p = make_parser "r0 = 1" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (ERegister _, "=", EInt _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with ="

let test_parse_inequality () =
  let p = make_parser "r0 != 1" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (ERegister _, "!=", EInt _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with !="

let test_parse_logical_and () =
  let p = make_parser "r0 && r1" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (ERegister _, "&&", ERegister _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with &&"

let test_parse_logical_or () =
  let p = make_parser "r0 || r1" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (ERegister _, "||", ERegister _) -> ()
    | _ -> Alcotest.fail "Expected EBinOp with ||"

let test_parse_unary_not () =
  let p = make_parser "!r0" in
  let expr = parse_expr p () in
    match expr with
    | EUnOp ("!", ERegister _) -> ()
    | _ -> Alcotest.fail "Expected EUnOp with !"

let test_parse_unary_bitwise_not () =
  let p = make_parser "~r0" in
  let expr = parse_expr p () in
    match expr with
    | EUnOp ("~", ERegister _) -> ()
    | _ -> Alcotest.fail "Expected EUnOp with ~"

let test_parse_unary_address_of () =
  let p = make_parser "&x" in
  let expr = parse_expr p () in
    match expr with
    | EUnOp ("&", EGlobal _) -> ()
    | _ -> Alcotest.fail "Expected EUnOp with &"

let test_parse_precedence_add_mul () =
  let p = make_parser "1 + 2 * 3" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EInt _, "+", EBinOp (EInt _, "*", EInt _)) -> ()
    | _ -> Alcotest.fail "Expected correct precedence: 1 + (2 * 3)"

let test_parse_precedence_mul_add () =
  let p = make_parser "2 * 3 + 1" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EBinOp (EInt _, "*", EInt _), "+", EInt _) -> ()
    | _ -> Alcotest.fail "Expected correct precedence: (2 * 3) + 1"

let test_parse_parentheses () =
  let p = make_parser "(1 + 2) * 3" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp (EBinOp (EInt _, "+", EInt _), "*", EInt _) -> ()
    | _ -> Alcotest.fail "Expected parentheses to override precedence"

let test_parse_tuple () =
  let p = make_parser "[r0, r1]" in
  let expr = parse_expr p () in
    match expr with
    | ETuple (ERegister _, ERegister _) -> ()
    | _ -> Alcotest.fail "Expected ETuple"

let test_parse_malloc () =
  let p = make_parser "malloc 8" in
  let expr = parse_expr p () in
    match expr with
    | EMalloc (EInt _) -> ()
    | _ -> Alcotest.fail "Expected EMalloc"

let test_parse_complex_expr () =
  let p = make_parser "r0 + 1 * 2 = 3" in
  let expr = parse_expr p () in
    match expr with
    | EBinOp
        (EBinOp (ERegister _, "+", EBinOp (EInt _, "*", EInt _)), "=", EInt _)
      -> ()
    | _ -> Alcotest.fail "Expected complex nested expression"

(** Statement Parsing Tests *)

let test_parse_global_store_simple () =
  let src = "x := 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { global = "x"; expr = EInt n; assign } ] ->
        Alcotest.(check bool) "value is 1" true (Z.equal n Z.one);
        Alcotest.(check bool) "mode is Relaxed" true (assign.mode = Relaxed)
    | _ -> Alcotest.fail "Expected global store x := 1"

let test_parse_global_store_relaxed () =
  let src = "x :rlx= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { global = "x"; assign; _ } ] ->
        Alcotest.(check bool) "mode is Relaxed" true (assign.mode = Relaxed);
        Alcotest.(check bool) "not volatile" true (not assign.volatile)
    | _ -> Alcotest.fail "Expected relaxed global store"

let test_parse_global_store_release () =
  let src = "x :rel= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { assign; _ } ] ->
        Alcotest.(check bool) "mode is Release" true (assign.mode = Release)
    | _ -> Alcotest.fail "Expected release global store"

let test_parse_global_store_volatile () =
  let src = "x :v= 1" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalStore { assign; _ } ] ->
        Alcotest.(check bool) "volatile" true assign.volatile
    | _ -> Alcotest.fail "Expected volatile global store"

let test_parse_global_load_simple () =
  let src = "r0 := x" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalLoad { register = "r0"; global = "x"; assign } ] ->
        Alcotest.(check bool) "mode is Relaxed" true (assign.mode = Relaxed)
    | _ -> Alcotest.fail "Expected global load r0 := x"

let test_parse_global_load_acquire () =
  let src = "r0 :acq= x" in
  let ast = parse src in
    match ast.program with
    | [ SGlobalLoad { assign; _ } ] ->
        Alcotest.(check bool) "mode is Acquire" true (assign.mode = Acquire)
    | _ -> Alcotest.fail "Expected acquire global load"

let test_parse_register_store () =
  let src = "r0 := 42" in
  let ast = parse src in
    match ast.program with
    | [ SRegisterStore { register = "r0"; expr = EInt n } ] ->
        Alcotest.(check bool) "value is 42" true (Z.equal n (Z.of_int 42))
    | _ -> Alcotest.fail "Expected register store r0 := 42"

let test_parse_deref_load () =
  let src = "r0 := *r1" in
  let ast = parse src in
    match ast.program with
    | [ SDeref { register = "r0"; pointer = ERegister "r1"; _ } ] -> ()
    | _ -> Alcotest.fail "Expected deref load r0 := *r1"

let test_parse_deref_store () =
  let src = "*r0 := 1" in
  let ast = parse src in
    match ast.program with
    | [ SDerefStore { pointer = ERegister "r0"; expr = EInt _; _ } ] -> ()
    | _ -> Alcotest.fail "Expected deref store *r0 := 1"

let test_parse_if_simple () =
  let src = "if (r0) { x := 1 }" in
  let ast = parse src in
    match ast.program with
    | [
     SIf
       {
         condition = ERegister "r0";
         body = [ SGlobalStore _ ];
         else_body = None;
       };
    ] -> ()
    | _ -> Alcotest.fail "Expected if statement"

let test_parse_if_else () =
  let src = "if (r0 = 1) { x := 1 } else { y := 2 }" in
  let ast = parse src in
    match ast.program with
    | [
     SIf
       {
         condition = EBinOp _;
         body = [ SGlobalStore _ ];
         else_body = Some [ SGlobalStore _ ];
       };
    ] -> ()
    | _ -> Alcotest.fail "Expected if-else statement"

let test_parse_while_loop () =
  let src = "while (r0) { x := 1 }" in
  let ast = parse src in
    match ast.program with
    | [ SWhile { condition = ERegister "r0"; body = [ SGlobalStore _ ] } ] -> ()
    | _ -> Alcotest.fail "Expected while loop"

let test_parse_do_while () =
  let src = "do { x := 1 } while (r0)" in
  let ast = parse src in
    match ast.program with
    | [ SDo { body = [ SGlobalStore _ ]; condition = ERegister "r0" } ] -> ()
    | _ -> Alcotest.fail "Expected do-while loop"

let test_parse_qwhile_loop () =
  let src = "qwhile (r0) { x := 1 }" in
  let ast = parse src in
    match ast.program with
    | [ SQWhile { condition = ERegister "r0"; body = [ SGlobalStore _ ] } ] ->
        ()
    | _ -> Alcotest.fail "Expected qwhile loop"

let test_parse_qdo () =
  let src = "qdo { x := 1 } qwhile (r0)" in
  let ast = parse src in
    match ast.program with
    | [ SQDo { body = [ SGlobalStore _ ]; condition = ERegister "r0" } ] -> ()
    | _ -> Alcotest.fail "Expected qdo loop"

let test_parse_fence () =
  let src = "fence(sc)" in
  let ast = parse src in
    match ast.program with
    | [ SFence { mode = SC } ] -> ()
    | _ -> Alcotest.fail "Expected fence with SC"

let test_parse_cas () =
  let src = "r0 := CAS(x, 0, 1)" in
  let ast = parse src in
    match ast.program with
    | [ SCas { register = "r0"; params; _ } ] ->
        Alcotest.(check int) "3 params" 3 (List.length params)
    | _ -> Alcotest.fail "Expected CAS operation"

let test_parse_fadd () =
  let src = "r0 := FADD(x, 1)" in
  let ast = parse src in
    match ast.program with
    | [ SFAdd { register = "r0"; params; _ } ] ->
        Alcotest.(check int) "2 params" 2 (List.length params)
    | _ -> Alcotest.fail "Expected FADD operation"

let test_parse_lock () =
  let src = "lock x" in
  let ast = parse src in
    match ast.program with
    | [ SLock { global = Some "x" } ] -> ()
    | _ -> Alcotest.fail "Expected lock x"

let test_parse_unlock () =
  let src = "unlock x" in
  let ast = parse src in
    match ast.program with
    | [ SUnlock { global = Some "x" } ] -> ()
    | _ -> Alcotest.fail "Expected unlock x"

let test_parse_skip () =
  let src = "skip" in
  let ast = parse src in
    Alcotest.(check int) "empty program" 0 (List.length ast.program)

let test_parse_labeled_stmt () =
  let src = "`label` x := 1" in
  let ast = parse src in
    match ast.program with
    | [ SLabeled { label = [ "label" ]; stmt = SGlobalStore _ } ] -> ()
    | _ -> Alcotest.fail "Expected labeled statement"

let test_parse_thread_parallel () =
  let src = "{ x := 1 } ||| { y := 2 }" in
  let ast = parse src in
    match ast.program with
    | [
     SThread
       {
         lhs = [ SGlobalStore { global = "x"; _ } ];
         rhs = [ SGlobalStore { global = "y"; _ } ];
       };
    ] -> ()
    | _ -> Alcotest.fail "Expected thread parallel composition"

let test_parse_multiple_statements () =
  let src = "x := 1; y := 2; z := 3" in
  let ast = parse src in
    Alcotest.(check int) "3 statements" 3 (List.length ast.program)

(** Configuration Parsing Tests *)

let test_parse_config_name () =
  let src = "name = mytest\n%%" in
  let ast = parse src in
    Alcotest.(check string) "config name" "mytest" ast.config.name

let test_parse_config_values () =
  let src = "values = {0, 1, 2}\n%%" in
  let ast = parse src in
    Alcotest.(check int) "3 values" 3 (List.length ast.config.values)

let test_parse_config_defacto () =
  let src = "[r0 = 1]\n%%" in
  let ast = parse src in
    Alcotest.(check int)
      "1 defacto constraint" 1
      (List.length ast.config.defacto)

let test_parse_config_constraint () =
  let src = "[[r0 = 1]]\n%%" in
  let ast = parse src in
    Alcotest.(check int) "1 constraint" 1 (List.length ast.config.constraint_)

let test_parse_full_config () =
  let src = "name = test\nvalues = {0, 1}\n[x = 0]\n[[r0 = 1]]\n%%" in
  let ast = parse src in
    Alcotest.(check string) "name" "test" ast.config.name;
    Alcotest.(check int) "values" 2 (List.length ast.config.values);
    Alcotest.(check int) "defacto" 1 (List.length ast.config.defacto);
    Alcotest.(check int) "constraint" 1 (List.length ast.config.constraint_)

(** Assertion Parsing Tests *)

let test_parse_assertion_allow () =
  let src = "%% x := 1\n%% allow r0 = 1 []" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { outcome = "allow"; condition = EBinOp _; _ }) -> ()
    | _ -> Alcotest.fail "Expected allow assertion"

let test_parse_assertion_forbid () =
  let src = "%% x := 1\n%% forbid r0 = 1 []" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { outcome = "forbid"; _ }) -> ()
    | _ -> Alcotest.fail "Expected forbid assertion"

let test_parse_assertion_with_model () =
  let src = "%% x := 1\n%% allow r0 = 1 [sc]" in
  let ast = parse src in
    match ast.assertion with
    | Some (AOutcome { outcome = "allow"; model = Some "sc"; _ }) -> ()
    | _ -> Alcotest.fail "Expected assertion with model"

(** Full Litmus Test Parsing *)

let test_parse_message_passing () =
  let src =
    "name = MP\n\
     values = {0, 1}\n\
     %%\n\
     { x := 1; y := 1 } ||| { r0 := y; r1 := x }\n\
     %% forbid r0 = 1 && r1 = 0 []"
  in
  let ast = parse src in
    Alcotest.(check string) "MP test name" "MP" ast.config.name;
    Alcotest.(check int) "1 thread statement" 1 (List.length ast.program);
    match ast.assertion with
    | Some (AOutcome { outcome = "forbid"; _ }) -> ()
    | _ -> Alcotest.fail "Expected forbid assertion"

let test_parse_store_buffer () =
  let src =
    "%%\n\
     { x := 1; r0 := y } ||| { y := 1; r1 := x }\n\
     %% forbid r0 = 0 && r1 = 0 []"
  in
  let ast = parse src in
    match ast.program with
    | [ SThread _ ] -> ()
    | _ -> Alcotest.fail "Expected parallel threads"

let test_parse_empty_litmus () =
  let src = "%%" in
  let ast = parse src in
    Alcotest.(check int) "empty program" 0 (List.length ast.program)

(** Test Suite *)

let suite =
  ( "Parser",
    [
      (* Tokenization tests *)
      Alcotest.test_case "Tokenize keywords" `Quick test_tokenize_keywords;
      Alcotest.test_case "Tokenize control flow" `Quick
        test_tokenize_control_flow;
      Alcotest.test_case "Tokenize atomic ops" `Quick test_tokenize_atomic_ops;
      Alcotest.test_case "Tokenize numbers" `Quick test_tokenize_numbers;
      Alcotest.test_case "Tokenize registers" `Quick test_tokenize_registers;
      Alcotest.test_case "Tokenize globals" `Quick test_tokenize_globals;
      Alcotest.test_case "Tokenize atloc" `Quick test_tokenize_atloc;
      Alcotest.test_case "Tokenize strings" `Quick test_tokenize_strings;
      Alcotest.test_case "Tokenize backticks" `Quick test_tokenize_backticks;
      Alcotest.test_case "Tokenize assignment ops" `Quick
        test_tokenize_assignment_ops;
      Alcotest.test_case "Tokenize volatile assignment" `Quick
        test_tokenize_volatile_assignment_ops;
      Alcotest.test_case "Tokenize comparison ops" `Quick
        test_tokenize_comparison_ops;
      Alcotest.test_case "Tokenize arithmetic ops" `Quick
        test_tokenize_arithmetic_ops;
      Alcotest.test_case "Tokenize logical ops" `Quick test_tokenize_logical_ops;
      Alcotest.test_case "Tokenize bitwise ops" `Quick test_tokenize_bitwise_ops;
      Alcotest.test_case "Tokenize arrows" `Quick test_tokenize_arrows;
      Alcotest.test_case "Tokenize brackets" `Quick test_tokenize_brackets;
      Alcotest.test_case "Tokenize parallel" `Quick test_tokenize_parallel;
      Alcotest.test_case "Tokenize punctuation" `Quick test_tokenize_punctuation;
      Alcotest.test_case "Tokenize comments" `Quick test_tokenize_comments;
      Alcotest.test_case "Tokenize whitespace" `Quick test_tokenize_whitespace;
      (* Expression parsing tests *)
      Alcotest.test_case "Parse integer" `Quick test_parse_int;
      Alcotest.test_case "Parse hex integer" `Quick test_parse_hex_int;
      Alcotest.test_case "Parse register" `Quick test_parse_register_expr;
      Alcotest.test_case "Parse global" `Quick test_parse_global_expr;
      Alcotest.test_case "Parse atloc" `Quick test_parse_atloc_expr;
      Alcotest.test_case "Parse aset" `Quick test_parse_aset_expr;
      Alcotest.test_case "Parse addition" `Quick test_parse_addition;
      Alcotest.test_case "Parse subtraction" `Quick test_parse_subtraction;
      Alcotest.test_case "Parse multiplication" `Quick test_parse_multiplication;
      Alcotest.test_case "Parse division" `Quick test_parse_division;
      Alcotest.test_case "Parse comparison" `Quick test_parse_comparison;
      Alcotest.test_case "Parse inequality" `Quick test_parse_inequality;
      Alcotest.test_case "Parse logical and" `Quick test_parse_logical_and;
      Alcotest.test_case "Parse logical or" `Quick test_parse_logical_or;
      Alcotest.test_case "Parse unary not" `Quick test_parse_unary_not;
      Alcotest.test_case "Parse unary bitwise not" `Quick
        test_parse_unary_bitwise_not;
      Alcotest.test_case "Parse address-of" `Quick test_parse_unary_address_of;
      Alcotest.test_case "Parse precedence add/mul" `Quick
        test_parse_precedence_add_mul;
      Alcotest.test_case "Parse precedence mul/add" `Quick
        test_parse_precedence_mul_add;
      Alcotest.test_case "Parse parentheses" `Quick test_parse_parentheses;
      Alcotest.test_case "Parse tuple" `Quick test_parse_tuple;
      Alcotest.test_case "Parse malloc" `Quick test_parse_malloc;
      Alcotest.test_case "Parse complex expression" `Quick
        test_parse_complex_expr;
      (* Statement parsing tests *)
      Alcotest.test_case "Parse global store simple" `Quick
        test_parse_global_store_simple;
      Alcotest.test_case "Parse global store relaxed" `Quick
        test_parse_global_store_relaxed;
      Alcotest.test_case "Parse global store release" `Quick
        test_parse_global_store_release;
      Alcotest.test_case "Parse global store volatile" `Quick
        test_parse_global_store_volatile;
      Alcotest.test_case "Parse global load simple" `Quick
        test_parse_global_load_simple;
      Alcotest.test_case "Parse global load acquire" `Quick
        test_parse_global_load_acquire;
      Alcotest.test_case "Parse register store" `Quick test_parse_register_store;
      Alcotest.test_case "Parse deref load" `Quick test_parse_deref_load;
      Alcotest.test_case "Parse deref store" `Quick test_parse_deref_store;
      Alcotest.test_case "Parse if simple" `Quick test_parse_if_simple;
      Alcotest.test_case "Parse if-else" `Quick test_parse_if_else;
      Alcotest.test_case "Parse while loop" `Quick test_parse_while_loop;
      Alcotest.test_case "Parse do-while" `Quick test_parse_do_while;
      Alcotest.test_case "Parse qwhile loop" `Quick test_parse_qwhile_loop;
      Alcotest.test_case "Parse qdo" `Quick test_parse_qdo;
      Alcotest.test_case "Parse fence" `Quick test_parse_fence;
      Alcotest.test_case "Parse CAS" `Quick test_parse_cas;
      Alcotest.test_case "Parse FADD" `Quick test_parse_fadd;
      Alcotest.test_case "Parse lock" `Quick test_parse_lock;
      Alcotest.test_case "Parse unlock" `Quick test_parse_unlock;
      Alcotest.test_case "Parse skip" `Quick test_parse_skip;
      Alcotest.test_case "Parse labeled statement" `Quick
        test_parse_labeled_stmt;
      Alcotest.test_case "Parse thread parallel" `Quick
        test_parse_thread_parallel;
      Alcotest.test_case "Parse multiple statements" `Quick
        test_parse_multiple_statements;
      (* Configuration parsing tests *)
      Alcotest.test_case "Parse config name" `Quick test_parse_config_name;
      Alcotest.test_case "Parse config values" `Quick test_parse_config_values;
      Alcotest.test_case "Parse config defacto" `Quick test_parse_config_defacto;
      Alcotest.test_case "Parse config constraint" `Quick
        test_parse_config_constraint;
      Alcotest.test_case "Parse full config" `Quick test_parse_full_config;
      (* Assertion parsing tests *)
      Alcotest.test_case "Parse allow assertion" `Quick
        test_parse_assertion_allow;
      Alcotest.test_case "Parse forbid assertion" `Quick
        test_parse_assertion_forbid;
      Alcotest.test_case "Parse assertion with model" `Quick
        test_parse_assertion_with_model;
      (* Full litmus test parsing *)
      Alcotest.test_case "Parse message passing" `Quick
        test_parse_message_passing;
      Alcotest.test_case "Parse store buffer" `Quick test_parse_store_buffer;
      Alcotest.test_case "Parse empty litmus" `Quick test_parse_empty_litmus;
    ]
  )
