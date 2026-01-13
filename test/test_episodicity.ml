open Alcotest
open Context
open Episodicity
open Events
open Eventstructures
open Lwt.Syntax
open Types
open Uset

let make_ir_node stmt : ir_node =
  {
    stmt;
    annotations = { source_span = None; thread_ctx = None; loop_ctx = None };
  }

(* Helper to create a dummy assign_info for memory operations *)
let make_assign_info ?(mode = Relaxed) ?(volatile = false) () : Ast.assign_info
    =
  { mode; volatile }

let make_load_info ?(mode = Relaxed) ?(volatile = false) () : Ast.assign_info =
  { mode; volatile }

module TestRegisterCondition = struct
  (* Type for test case specifications *)
  type test_case = {
    name : string;
    stmts : ir_stmt list;
    expected_satisfied : bool;
    expected_violation_count : int option; (* None means "don't check count" *)
    description : string;
  }

  (* Data provider: collection of all test cases *)
  let test_cases =
    [
      (* ========== Basic Cases ========== *)
      {
        name = "register condition met";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = EVar "r1" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Register written before read (valid)";
      };
      {
        name = "register condition write after read";
        stmts =
          [
            RegisterStore { register = "r2"; expr = EVar "r1" };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "Register read before write (violation)";
      };
      {
        name = "multiple reads before write";
        stmts =
          [
            RegisterStore { register = "r2"; expr = EVar "r1" };
            RegisterStore { register = "r3"; expr = EVar "r1" };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "Same register read multiple times before write";
      };
      {
        name = "empty loop";
        stmts = [];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Empty loop body has no violations";
      };
      {
        name = "only writes";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 2) };
            RegisterStore { register = "r3"; expr = ENum (Z.of_int 3) };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Only writes, no reads";
      };
      (* ========== Register Dependency Chains ========== *)
      {
        name = "register chain valid";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = EVar "r1" };
            RegisterStore { register = "r3"; expr = EVar "r2" };
            RegisterStore { register = "r4"; expr = EVar "r3" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Chain of register dependencies properly ordered";
      };
      {
        name = "multiple register chains";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 2) };
            RegisterStore { register = "r3"; expr = EVar "r1" };
            RegisterStore { register = "r4"; expr = EVar "r2" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Multiple independent register chains";
      };
      {
        name = "write read write";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = EVar "r1" };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 2) };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Register written, read, then written again";
      };
      (* ========== Expression Complexity ========== *)
      {
        name = "register in expression";
        stmts =
          [
            RegisterStore
              {
                register = "r2";
                expr = EBinOp (EVar "r1", "+", ENum (Z.of_int 1));
              };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 5) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "Register used in expression before initialization";
      };
      {
        name = "complex expression";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 2) };
            RegisterStore
              {
                register = "r3";
                expr =
                  EBinOp
                    (EBinOp (EVar "r1", "+", EVar "r2"), "*", ENum (Z.of_int 3));
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Complex nested expression with proper initialization";
      };
      {
        name = "self referential update";
        stmts =
          [
            RegisterStore
              {
                register = "r1";
                expr = EBinOp (EVar "r1", "+", ENum (Z.of_int 1));
              };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "Register references itself without initialization";
      };
      {
        name = "initialize then self update";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 0) };
            RegisterStore
              {
                register = "r1";
                expr = EBinOp (EVar "r1", "+", ENum (Z.of_int 1));
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Register initialized before self-referential update";
      };
      (* ========== Memory Operations ========== *)
      {
        name = "global load";
        stmts =
          [
            GlobalLoad
              { register = "r1"; global = "x"; load = make_load_info () };
            RegisterStore { register = "r2"; expr = EVar "r1" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "GlobalLoad writes to register, then register read";
      };
      {
        name = "deref load";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            DerefLoad
              { register = "r2"; address = EVar "r1"; load = make_load_info () };
            RegisterStore { register = "r3"; expr = EVar "r2" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "DerefLoad writes to register after reading address";
      };
      {
        name = "global store reads register";
        stmts =
          [
            GlobalStore
              { global = "x"; expr = EVar "r1"; assign = make_assign_info () };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "GlobalStore reads uninitialized register";
      };
      {
        name = "deref store reads registers";
        stmts =
          [
            DerefStore
              {
                address = EVar "r1";
                expr = EVar "r2";
                assign = make_assign_info ();
              };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
          ];
        expected_satisfied = false;
        expected_violation_count = None;
        (* At least 1, could be 2 *)
        description = "DerefStore reads from uninitialized registers";
      };
      {
        name = "deref store with initialized registers";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 42) };
            DerefStore
              {
                address = EVar "r1";
                expr = EVar "r2";
                assign = make_assign_info ();
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "DerefStore with properly initialized registers";
      };
      (* ========== Atomic Operations ========== *)
      {
        name = "cas operation";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r3"; expr = ENum (Z.of_int 2) };
            Cas
              {
                register = "r4";
                address = EVar "r1";
                expected = EVar "r2";
                desired = EVar "r3";
                load_mode = Relaxed;
                assign_mode = Relaxed;
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "CAS with all registers initialized";
      };
      {
        name = "fadd operation";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 5) };
            Fadd
              {
                register = "r3";
                address = EVar "r1";
                operand = EVar "r2";
                rmw_mode = "fetch_add";
                load_mode = Relaxed;
                assign_mode = Relaxed;
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "FADD with initialized registers";
      };
      (* ========== Control Flow ========== *)
      {
        name = "if condition reads register";
        stmts =
          [
            If
              {
                condition = EBinOp (EVar "r1", "=", ENum (Z.of_int 0));
                then_body =
                  [
                    make_ir_node
                      (RegisterStore
                         { register = "r2"; expr = ENum (Z.of_int 1) }
                      );
                  ];
                else_body = None;
              };
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 0) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "If condition reads uninitialized register";
      };
      {
        name = "if with initialized condition";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 0) };
            If
              {
                condition = EBinOp (EVar "r1", "=", ENum (Z.of_int 0));
                then_body =
                  [
                    make_ir_node
                      (RegisterStore
                         { register = "r2"; expr = ENum (Z.of_int 1) }
                      );
                  ];
                else_body =
                  Some
                    [
                      make_ir_node
                        (RegisterStore
                           { register = "r2"; expr = ENum (Z.of_int 2) }
                        );
                    ];
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "If with properly initialized condition register";
      };
      {
        name = "while condition reads register";
        stmts =
          [
            While
              {
                condition = EBinOp (EVar "r1", "<", ENum (Z.of_int 10));
                body =
                  [
                    make_ir_node
                      (RegisterStore
                         {
                           register = "r1";
                           expr = EBinOp (EVar "r1", "+", ENum (Z.of_int 1));
                         }
                      );
                  ];
              };
          ];
        expected_satisfied = false;
        expected_violation_count = None;
        (* Has violations *)
        description = "While condition reads uninitialized register";
      };
      {
        name = "do while with initialization";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 0) };
            Do
              {
                body =
                  [
                    make_ir_node
                      (RegisterStore
                         {
                           register = "r1";
                           expr = EBinOp (EVar "r1", "+", ENum (Z.of_int 1));
                         }
                      );
                  ];
                condition = EBinOp (EVar "r1", "<", ENum (Z.of_int 10));
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Do-while with register initialized before loop";
      };
      (* ========== Edge Cases ========== *)
      {
        name = "register used in multiple contexts";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            DerefLoad
              { register = "r2"; address = EVar "r1"; load = make_load_info () };
            GlobalStore
              { global = "x"; expr = EVar "r2"; assign = make_assign_info () };
            DerefStore
              {
                address = EVar "r1";
                expr = EVar "r2";
                assign = make_assign_info ();
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Register used across different operation types";
      };
      {
        name = "mixed valid and invalid";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            RegisterStore { register = "r2"; expr = EVar "r1" };
            (* Valid *)
            RegisterStore { register = "r3"; expr = EVar "r4" };
            (* Invalid: r4 not init *)
            RegisterStore { register = "r4"; expr = ENum (Z.of_int 2) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "Mix of valid and invalid register accesses";
      };
      {
        name = "register malloc";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            RegMalloc { register = "r2"; size = EVar "r1" };
            RegisterStore { register = "r3"; expr = EVar "r2" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "RegMalloc reads from and writes to registers";
      };
    ]

  (* Generic test function that uses test case data *)
  let run_test_case test_case () =
    let loop_body = List.map make_ir_node test_case.stmts in
    let { satisfied; violations } = check_register_accesses_in_loop loop_body in

    (* Check satisfied flag *)
    check bool
      (Printf.sprintf "%s - satisfied" test_case.name)
      test_case.expected_satisfied satisfied;

    (* Check violation count if specified *)
    match test_case.expected_violation_count with
    | Some expected_count ->
        check int
          (Printf.sprintf "%s - violation count" test_case.name)
          expected_count (List.length violations)
    | None ->
        (* Just verify violations exist when expected *)
        if not test_case.expected_satisfied then
          check bool
            (Printf.sprintf "%s - has violations" test_case.name)
            true
            (List.length violations > 0)

  (* Generate suite from test cases *)
  let suite =
    List.map (fun tc -> test_case tc.name `Quick (run_test_case tc)) test_cases
end

module TestWriteCondition = struct
  let test_mod_write_after_read () =
    let init = Event.create Init 0 () in
    let alloc = Event.create Malloc 1 ~rval:(VSymbol "一") () in
    let init_write =
      Event.create Write 2 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 0)) ()
    in
    let read = Event.create Read 3 ~loc:(ESymbol "一") ~rval:(VSymbol "α") () in
    let mod_write =
      Event.create Write 4 ~loc:(ESymbol "一")
        ~wval:(EBinOp (ESymbol "α", "+", ENum (Z.of_int 1)))
        ~rmod:Relaxed ()
    in
    let po =
      USet.of_list
        [
          (init.label, alloc.label);
          (alloc.label, init_write.label);
          (init_write.label, read.label);
          (read.label, mod_write.label);
        ]
    in
    let e_set =
      USet.of_list
        [
          init.label; alloc.label; init_write.label; read.label; mod_write.label;
        ]
    in
    let events = Hashtbl.create 5 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; alloc; init_write; read; mod_write ];
      let loop_indices = Hashtbl.create 0 in
        Hashtbl.add loop_indices read.label [ 0 ];
        Hashtbl.add loop_indices mod_write.label [ 0 ];
        let symbolic_structure =
          {
            e = e_set;
            events;
            po;
            po_iter = USet.create ();
            rmw = USet.create ();
            lo = USet.create ();
            restrict = Hashtbl.create 0;
            cas_groups = Hashtbl.create 0;
            pwg = [];
            branch_events = USet.create ();
            read_events = USet.of_list [ read.label ];
            write_events = USet.of_list [ init_write.label; mod_write.label ];
            rlx_read_events = USet.of_list [ read.label ];
            rlx_write_events = USet.of_list [ mod_write.label ];
            fence_events = USet.create ();
            malloc_events = USet.of_list [ alloc.label ];
            free_events = USet.create ();
            terminal_events = USet.create ();
            fj = USet.create ();
            p = Hashtbl.create 0;
            constraint_ = [];
            conflict = USet.create ();
            origin = Hashtbl.create 0;
            loop_indices;
            thread_index = Hashtbl.create 0;
          }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
          Hashtbl.add symbolic_source_spans alloc.label
            { start_line = 2; start_col = 1; end_line = 2; end_col = 10 };
          Hashtbl.add symbolic_source_spans init_write.label
            { start_line = 3; start_col = 1; end_line = 3; end_col = 10 };
          Hashtbl.add symbolic_source_spans read.label
            { start_line = 6; start_col = 1; end_line = 6; end_col = 10 };
          Hashtbl.add symbolic_source_spans mod_write.label
            { start_line = 7; start_col = 1; end_line = 7; end_col = 10 };
          let cache =
            {
              symbolic_structure;
              symbolic_source_spans;
              three_structure = SymbolicEventStructure.create ();
              three_source_spans = Hashtbl.create 0;
              three_executions = [];
            }
          in
            let* result = check_condition2_read_sources cache 0 in
              check bool "modifying write after read" false result.satisfied;
              Lwt.return_unit

  let suite =
    [
      test_case "WriteCondition.modifying_write_after_read" `Quick (fun () ->
          Lwt_main.run (test_mod_write_after_read ())
      );
    ]
end

let suite =
  ("Episodicity", TestRegisterCondition.suite @ TestWriteCondition.suite)
