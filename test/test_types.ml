open Types

(** Test default options *)
let test_default_options () =
  Alcotest.(check bool)
    "dependencies default is true" true default_options.dependencies;
  Alcotest.(check bool)
    "just_structure default is false" false default_options.just_structure;
  Alcotest.(check bool)
    "exhaustive default is false" false default_options.exhaustive;
  Alcotest.(check bool)
    "forcerc11 default is false" false default_options.forcerc11;
  Alcotest.(check bool)
    "forceimm default is false" false default_options.forceimm;
  Alcotest.(check bool)
    "forcenocoh default is false" false default_options.forcenocoh

(** Test event_type_to_string *)
let test_event_type_to_string () =
  Alcotest.(check string) "Read converts to R" "R" (event_type_to_string Read);
  Alcotest.(check string) "Write converts to W" "W" (event_type_to_string Write);
  Alcotest.(check string) "Lock converts to L" "L" (event_type_to_string Lock);
  Alcotest.(check string)
    "Unlock converts to U" "U"
    (event_type_to_string Unlock);
  Alcotest.(check string) "Fence converts to F" "F" (event_type_to_string Fence);
  Alcotest.(check string) "Init converts to empty" "" (event_type_to_string Init);
  Alcotest.(check string)
    "Branch converts to empty" ""
    (event_type_to_string Branch);
  Alcotest.(check string) "Loop converts to empty" "" (event_type_to_string Loop);
  Alcotest.(check string)
    "Malloc converts to Alloc" "Alloc"
    (event_type_to_string Malloc);
  Alcotest.(check string)
    "Free converts to Free" "Free"
    (event_type_to_string Free);
  Alcotest.(check string) "RMW converts to empty" "" (event_type_to_string RMW);
  Alcotest.(check string) "CRMW converts to empty" "" (event_type_to_string CRMW)

(** Test mode_to_string *)
let test_mode_to_string () =
  Alcotest.(check string)
    "Relaxed converts to rlx" "rlx" (mode_to_string Relaxed);
  Alcotest.(check string)
    "Acquire converts to acq" "acq" (mode_to_string Acquire);
  Alcotest.(check string)
    "Release converts to rel" "rel" (mode_to_string Release);
  Alcotest.(check string) "SC converts to sc" "sc" (mode_to_string SC);
  Alcotest.(check string) "Normal converts to empty" "" (mode_to_string Normal);
  Alcotest.(check string)
    "Strong converts to strong" "strong" (mode_to_string Strong);
  Alcotest.(check string)
    "Nonatomic converts to na" "na" (mode_to_string Nonatomic)

(** Test mode_to_string_or *)
let test_mode_to_string_or () =
  Alcotest.(check string)
    "Relaxed converts to empty in _or" ""
    (mode_to_string_or Relaxed);
  Alcotest.(check string)
    "Acquire converts to acq in _or" "acq"
    (mode_to_string_or Acquire);
  Alcotest.(check string)
    "Release converts to rel in _or" "rel"
    (mode_to_string_or Release);
  Alcotest.(check string) "SC converts to sc in _or" "sc" (mode_to_string_or SC);
  Alcotest.(check string)
    "Normal converts to empty in _or" "" (mode_to_string_or Normal);
  Alcotest.(check string)
    "Strong converts to strong in _or" "strong" (mode_to_string_or Strong);
  Alcotest.(check string)
    "Nonatomic converts to na in _or" "na"
    (mode_to_string_or Nonatomic)

(** Test Unicode module *)
let test_unicode_symbols () =
  Alcotest.(check string) "wedge symbol" "\u{2227}" Unicode.wedge;
  Alcotest.(check string) "vee symbol" "\u{2228}" Unicode.vee;
  Alcotest.(check string) "emptyset symbol" "\u{2205}" Unicode.emptyset;
  Alcotest.(check string) "top symbol" "\u{22a4}" Unicode.top;
  Alcotest.(check string) "cap symbol" "\u{2229}" Unicode.cap;
  Alcotest.(check string) "cup symbol" "\u{222a}" Unicode.cup;
  Alcotest.(check string) "in symbol" "\u{2208}" Unicode.in_;
  Alcotest.(check string) "notin symbol" "\u{2209}" Unicode.notin;
  Alcotest.(check string) "perp symbol" "\u{22a5}" Unicode.perp

(** Test greek_alpha *)
let test_greek_alpha () =
  Alcotest.(check bool)
    "greek_alpha is not empty" true
    (String.length greek_alpha > 0);
  (* Greek alphabet should contain both lowercase and uppercase variants *)
  Alcotest.(check bool)
    "greek_alpha has reasonable length" true
    (String.length greek_alpha > 20)

(** Test zh_alpha *)
let test_zh_alpha () =
  Alcotest.(check bool) "zh_alpha is not empty" true (String.length zh_alpha > 0);
  Alcotest.(check int) "zh_alpha has expected length" 30 (String.length zh_alpha)

(** Test make_event *)
let test_make_event () =
  let evt = make_event Read 42 in
    Alcotest.(check int) "event label is 42" 42 evt.label;
    Alcotest.(check int) "event van is 42" 42 evt.van;
    Alcotest.(check bool) "event id is None" true (evt.id = None);
    Alcotest.(check bool) "event rval is None" true (evt.rval = None);
    Alcotest.(check bool) "event wval is None" true (evt.wval = None);
    Alcotest.(check bool) "event cond is None" true (evt.cond = None);
    Alcotest.(check bool) "event volatile is false" false evt.volatile;
    Alcotest.(check bool) "event strong is None" true (evt.strong = None);
    Alcotest.(check bool) "event lhs is None" true (evt.lhs = None);
    Alcotest.(check bool) "event rhs is None" true (evt.rhs = None);
    Alcotest.(check bool) "event pc is None" true (evt.pc = None);
    Alcotest.(check bool) "event hide is false" false evt.hide;
    Alcotest.(check bool) "event quot is None" true (evt.quot = None)

let test_make_event_types () =
  let read_evt = make_event Read 1 in
  let write_evt = make_event Write 2 in
  let fence_evt = make_event Fence 3 in
    Alcotest.(check string)
      "Read event type" "R"
      (event_type_to_string read_evt.typ);
    Alcotest.(check string)
      "Write event type" "W"
      (event_type_to_string write_evt.typ);
    Alcotest.(check string)
      "Fence event type" "F"
      (event_type_to_string fence_evt.typ)

(** Test make_func *)
let test_make_func_empty () =
  let f = make_func ~default:(fun () -> 0) () in
    Alcotest.(check int) "default value is 0" 0 (func_get f "nonexistent")

let test_make_func_add () =
  let f = make_func ~default:(fun () -> 0) () in
  let f' = func_add f "key1" 42 in
    Alcotest.(check int) "retrieved value is 42" 42 (func_get f' "key1")

let test_make_func_find () =
  let f = make_func ~default:(fun () -> 0) () in
  let _ = func_add f "key1" 100 in
    match func_find f "key1" with
    | Some v -> Alcotest.(check int) "found value is 100" 100 v
    | None -> Alcotest.fail "Expected to find value"

let test_make_func_find_none () =
  let f = make_func ~default:(fun () -> 0) () in
    match func_find f "nonexistent" with
    | Some _ -> Alcotest.fail "Expected None"
    | None -> Alcotest.(check bool) "returns None for missing key" true true

let test_make_func_replace () =
  let f = make_func ~default:(fun () -> 0) () in
  let _ = func_add f "key1" 42 in
  let _ = func_add f "key1" 99 in
    Alcotest.(check int) "replaced value is 99" 99 (func_get f "key1")

(** Test value_type construction *)
let test_value_types () =
  let num = VNumber (Z.of_int 42) in
  let sym = VSymbol "alpha" in
  let var = VVar "x" in
  let bool_val = VBoolean true in
    ( match num with
    | VNumber z ->
        Alcotest.(check bool) "VNumber created" true (Z.equal z (Z.of_int 42))
    | _ -> Alcotest.fail "Expected VNumber"
    );
    ( match sym with
    | VSymbol s -> Alcotest.(check string) "VSymbol created" "alpha" s
    | _ -> Alcotest.fail "Expected VSymbol"
    );
    ( match var with
    | VVar v -> Alcotest.(check string) "VVar created" "x" v
    | _ -> Alcotest.fail "Expected VVar"
    );
    match bool_val with
    | VBoolean b -> Alcotest.(check bool) "VBoolean created" true b
    | _ -> Alcotest.fail "Expected VBoolean"

(** Test expr construction *)
let test_expr_types () =
  let num_expr = ENum (Z.of_int 10) in
  let var_expr = EVar "y" in
    ( match num_expr with
    | ENum z ->
        Alcotest.(check bool) "ENum created" true (Z.equal z (Z.of_int 10))
    | _ -> Alcotest.fail "Expected ENum"
    );
    match var_expr with
    | EVar v -> Alcotest.(check string) "EVar created" "y" v
    | _ -> Alcotest.fail "Expected EVar"

let test_expr_binop () =
  let left = ENum (Z.of_int 5) in
  let right = ENum (Z.of_int 3) in
  let expr = EBinOp (left, "+", right) in
    match expr with
    | EBinOp (l, op, r) -> (
        Alcotest.(check string) "operator is +" "+" op;
        ( match l with
        | ENum z ->
            Alcotest.(check bool)
              "left operand is 5" true
              (Z.equal z (Z.of_int 5))
        | _ -> Alcotest.fail "Expected ENum for left operand"
        );
        match r with
        | ENum z ->
            Alcotest.(check bool)
              "right operand is 3" true
              (Z.equal z (Z.of_int 3))
        | _ -> Alcotest.fail "Expected ENum for right operand"
      )
    | _ -> Alcotest.fail "Expected EBinOp"

let suite =
  ( "Types",
    [
      Alcotest.test_case "Default options" `Quick test_default_options;
      Alcotest.test_case "Event type to string" `Quick test_event_type_to_string;
      Alcotest.test_case "Mode to string" `Quick test_mode_to_string;
      Alcotest.test_case "Mode to string or" `Quick test_mode_to_string_or;
      Alcotest.test_case "Unicode symbols" `Quick test_unicode_symbols;
      Alcotest.test_case "Greek alphabet" `Quick test_greek_alpha;
      Alcotest.test_case "Chinese numerals" `Quick test_zh_alpha;
      Alcotest.test_case "Make event" `Quick test_make_event;
      Alcotest.test_case "Make event types" `Quick test_make_event_types;
      Alcotest.test_case "Make func empty" `Quick test_make_func_empty;
      Alcotest.test_case "Make func add" `Quick test_make_func_add;
      Alcotest.test_case "Make func find" `Quick test_make_func_find;
      Alcotest.test_case "Make func find none" `Quick test_make_func_find_none;
      Alcotest.test_case "Make func replace" `Quick test_make_func_replace;
      Alcotest.test_case "Value types" `Quick test_value_types;
      Alcotest.test_case "Expr types" `Quick test_expr_types;
      Alcotest.test_case "Expr binop" `Quick test_expr_binop;
    ]
  )
