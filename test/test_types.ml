open Context
open Events
open Types
open Uset

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

(** Test Event.create *)
let test_make_event () =
  let evt = Event.create Read 42 () in
    Alcotest.(check int) "event label is 42" 42 evt.label;
    Alcotest.(check bool) "event id is None" true (evt.id = None);
    Alcotest.(check bool) "event rval is None" true (evt.rval = None);
    Alcotest.(check bool) "event wval is None" true (evt.wval = None);
    Alcotest.(check bool) "event volatile is false" false evt.volatile;
    Alcotest.(check bool) "event strong is None" true (evt.strong = None)

let test_make_event_types () =
  let read_evt = Event.create Read 1 () in
  let write_evt = Event.create Write 2 () in
  let fence_evt = Event.create Fence 3 () in
    Alcotest.(check string) "Read event type" "R" (show_event_type read_evt.typ);
    Alcotest.(check string)
      "Write event type" "W"
      (show_event_type write_evt.typ);
    Alcotest.(check string)
      "Fence event type" "F"
      (show_event_type fence_evt.typ)

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
