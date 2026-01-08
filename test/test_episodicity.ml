open Alcotest
open Context
open Episodicity
open Types

let make_ir_node stmt : ir_node =
  {
    stmt;
    annotations = { source_span = None; thread_ctx = None; loop_ctx = None };
  }

module TestRegisterCondition = struct
  let test_register_condition_met () =
    let loop_body =
      [
        RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
        RegisterStore { register = "r2"; expr = EVar "r1" };
      ]
      |> List.map make_ir_node
    in
    let { satisfied; violations } = check_register_accesses_in_loop loop_body in
      check bool "Condition met" true satisfied;
      check (list string) "No violations" [] violations

  let test_register_condition_write_after_read () =
    let loop_body =
      [
        RegisterStore { register = "r2"; expr = EVar "r1" };
        RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
      ]
      |> List.map make_ir_node
    in
    let { satisfied; violations } = check_register_accesses_in_loop loop_body in
      check bool "Condition violated" false satisfied;
      check int "one violation" 1 (List.length violations)

  let suite =
    [
      ("register condition met", `Quick, test_register_condition_met);
      ( "register condition write after read",
        `Quick,
        test_register_condition_write_after_read
      );
    ]
end

let suite = ("Episodicity", TestRegisterCondition.suite)
