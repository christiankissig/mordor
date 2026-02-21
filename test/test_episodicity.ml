open Alcotest
open Context
open Episodicity
open Events
open Eventstructures
open Forwarding
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
            RegisterStore { register = "r2"; expr = ENum (Z.of_int 5) };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 2;
        description = "DerefStore reads two uninitialized registers";
      };
      {
        name = "rmw operation";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 100) };
            Cas
              {
                register = "r2";
                address = EVar "r1";
                expected = ENum (Z.of_int 0);
                desired = ENum (Z.of_int 1);
                load_mode = Relaxed;
                assign_mode = Relaxed;
              };
            RegisterStore { register = "r3"; expr = EVar "r2" };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "RMW operation writes to register properly";
      };
      (* ========== Branching Structures ========== *)
      {
        name = "if then reads register in condition";
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
        expected_violation_count = None;
        description = "If condition reads uninitialized register";
      };
      {
        name = "if then else with initialized condition";
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
      (* ========== Nested Control Flow ========== *)
      {
        name = "nested if statements";
        stmts =
          [
            RegisterStore { register = "r1"; expr = ENum (Z.of_int 1) };
            If
              {
                condition = EBinOp (EVar "r1", "=", ENum (Z.of_int 1));
                then_body =
                  [
                    make_ir_node
                      (RegisterStore
                         { register = "r2"; expr = ENum (Z.of_int 2) }
                      );
                    make_ir_node
                      (If
                         {
                           condition = EBinOp (EVar "r2", "=", ENum (Z.of_int 2));
                           then_body =
                             [
                               make_ir_node
                                 (RegisterStore
                                    {
                                      register = "r3";
                                      expr = ENum (Z.of_int 3);
                                    }
                                 );
                             ];
                           else_body = None;
                         }
                      );
                  ];
                else_body = None;
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Nested if statements with proper initialization";
      };
      {
        name = "threads with independent register sets";
        stmts =
          [
            Threads
              {
                threads =
                  [
                    [
                      make_ir_node
                        (RegisterStore
                           { register = "r1"; expr = ENum (Z.of_int 1) }
                        );
                      make_ir_node
                        (RegisterStore { register = "r2"; expr = EVar "r1" });
                    ];
                    [
                      make_ir_node
                        (RegisterStore
                           { register = "r1"; expr = ENum (Z.of_int 2) }
                        );
                      make_ir_node
                        (RegisterStore { register = "r3"; expr = EVar "r1" });
                    ];
                  ];
              };
          ];
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Threads with independent register initialization";
      };
      {
        name = "threads with violation in one thread";
        stmts =
          [
            Threads
              {
                threads =
                  [
                    [
                      make_ir_node
                        (RegisterStore
                           { register = "r1"; expr = ENum (Z.of_int 1) }
                        );
                      make_ir_node
                        (RegisterStore { register = "r2"; expr = EVar "r1" });
                    ];
                    [
                      make_ir_node
                        (RegisterStore { register = "r3"; expr = EVar "r4" });
                      (* Violation *)
                      make_ir_node
                        (RegisterStore
                           { register = "r4"; expr = ENum (Z.of_int 2) }
                        );
                    ];
                  ];
              };
          ];
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "One thread has violation, other is valid";
      };
    ]

  (* Generic test function that uses test case data *)
  let run_test_case test_case () =
    let loop_body = List.map make_ir_node test_case.stmts in
    let { satisfied; violations } =
      RegisterCondition.check_register_accesses_in_loop loop_body
    in

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
  (* Type for test case specifications *)
  type write_test_case = {
    name : string;
    setup : unit -> episodicity_cache;
    expected_satisfied : bool;
    expected_violation_count : int option;
    description : string;
  }

  (* Helper to create a minimal symbolic event structure *)
  let create_base_structure () =
    let init = Event.create Init 0 () in
    let events = Hashtbl.create 10 in
      Hashtbl.add events init.label init;
      {
        (SymbolicEventStructure.create ()) with
        e = USet.of_list [ init.label ];
        events;
      }

  (* Test 1: Modifying write after read (VIOLATION) *)
  let test_mod_write_after_read_setup () =
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
        let loop_conditions = Hashtbl.create 0 in
          Hashtbl.add loop_conditions 0 (EBoolean true);
          (* while true *)
          let symbolic_structure =
            {
              (SymbolicEventStructure.create ()) with
              e = e_set;
              events;
              po;
              read_events = USet.of_list [ read.label ];
              write_events = USet.of_list [ init_write.label; mod_write.label ];
              rlx_read_events = USet.of_list [ read.label ];
              rlx_write_events = USet.of_list [ mod_write.label ];
              malloc_events = USet.of_list [ alloc.label ];
              loop_indices;
              loop_conditions;
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
            let symbolic_justifications = USet.create () in
            let symbolic_fwd_es_ctx =
              EventStructureContext.create symbolic_structure
            in
              {
                program = [];
                symbolic_structure;
                symbolic_source_spans;
                symbolic_justifications;
                symbolic_fwd_es_ctx;
              }

  (* Test 2: Same-iteration write before read (VALID) *)
  let test_same_iteration_write_setup () =
    let init = Event.create Init 0 () in
    let alloc = Event.create Malloc 1 ~rval:(VSymbol "一") () in
    let write =
      Event.create Write 2 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 42)) ()
    in
    let read = Event.create Read 3 ~loc:(ESymbol "一") ~rval:(VSymbol "α") () in
    let po =
      USet.of_list
        [
          (init.label, alloc.label);
          (alloc.label, write.label);
          (write.label, read.label);
        ]
    in
    let e_set =
      USet.of_list [ init.label; alloc.label; write.label; read.label ]
    in
    let events = Hashtbl.create 4 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; alloc; write; read ];
      let loop_indices = Hashtbl.create 0 in
        Hashtbl.add loop_indices write.label [ 0 ];
        Hashtbl.add loop_indices read.label [ 0 ];
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = e_set;
            events;
            po;
            read_events = USet.of_list [ read.label ];
            write_events = USet.of_list [ write.label ];
            rlx_read_events = USet.of_list [ read.label ];
            rlx_write_events = USet.of_list [ write.label ];
            malloc_events = USet.of_list [ alloc.label ];
            loop_indices;
          }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
        let symbolic_fwd_es_ctx =
          EventStructureContext.create symbolic_structure
        in
          {
            program = [];
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }

  (* Test 3: Multiple writes to same location, not sequenced (VIOLATION) *)
  let test_multiple_unordered_writes_setup () =
    let init = Event.create Init 0 () in
    let alloc = Event.create Malloc 1 ~rval:(VSymbol "一") () in
    let write1 =
      Event.create Write 2 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 1)) ()
    in
    let write2 =
      Event.create Write 3 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 2)) ()
    in
    let read = Event.create Read 4 ~loc:(ESymbol "一") ~rval:(VSymbol "α") () in
    let po =
      USet.of_list
        [
          (init.label, alloc.label);
          (alloc.label, write1.label);
          (* write2 is NOT sequenced before read *)
          (write1.label, read.label);
        ]
    in
    let e_set =
      USet.of_list
        [ init.label; alloc.label; write1.label; write2.label; read.label ]
    in
    let events = Hashtbl.create 5 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; alloc; write1; write2; read ];
      let loop_indices = Hashtbl.create 0 in
        Hashtbl.add loop_indices write1.label [ 0 ];
        Hashtbl.add loop_indices write2.label [ 0 ];
        Hashtbl.add loop_indices read.label [ 0 ];
        let loop_conditions = Hashtbl.create 0 in
          Hashtbl.add loop_conditions 0 (EBoolean true);
          (* while true *)
          let symbolic_structure =
            {
              (SymbolicEventStructure.create ()) with
              e = e_set;
              events;
              po;
              read_events = USet.of_list [ read.label ];
              write_events = USet.of_list [ write1.label; write2.label ];
              rlx_read_events = USet.of_list [ read.label ];
              rlx_write_events = USet.of_list [ write1.label; write2.label ];
              malloc_events = USet.of_list [ alloc.label ];
              loop_indices;
              loop_conditions;
            }
          in
          let symbolic_source_spans = Hashtbl.create 0 in
          let symbolic_justifications = USet.create () in
          let symbolic_fwd_es_ctx =
            EventStructureContext.create symbolic_structure
          in
            {
              program = [];
              symbolic_structure;
              symbolic_source_spans;
              symbolic_justifications;
              symbolic_fwd_es_ctx;
            }

  (* Test 4: Read-don't-modify RMW (VALID) *)
  let test_rdmw_valid_setup () =
    let init = Event.create Init 0 () in
    let alloc = Event.create Malloc 1 ~rval:(VSymbol "一") () in
    let init_write =
      Event.create Write 2 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 0)) ()
    in
    let read = Event.create Read 3 ~loc:(ESymbol "一") ~rval:(VSymbol "α") () in
    (* Read-don't-modify: write with same value as read *)
    let rdmw_write =
      Event.create Write 4 ~loc:(ESymbol "一") ~wval:(ESymbol "α") ~rmod:Relaxed
        ~is_rdmw:true ()
    in
    let po =
      USet.of_list
        [
          (init.label, alloc.label);
          (alloc.label, init_write.label);
          (init_write.label, read.label);
          (* rdmw_write is NOT sequenced after read *)
        ]
    in
    let e_set =
      USet.of_list
        [
          init.label;
          alloc.label;
          init_write.label;
          read.label;
          rdmw_write.label;
        ]
    in
    let events = Hashtbl.create 5 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; alloc; init_write; read; rdmw_write ];
      let loop_indices = Hashtbl.create 0 in
        Hashtbl.add loop_indices read.label [ 0 ];
        Hashtbl.add loop_indices rdmw_write.label [ 0 ];
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = e_set;
            events;
            po;
            read_events = USet.of_list [ read.label ];
            write_events = USet.of_list [ init_write.label; rdmw_write.label ];
            rlx_read_events = USet.of_list [ read.label ];
            rlx_write_events = USet.of_list [ rdmw_write.label ];
            malloc_events = USet.of_list [ alloc.label ];
            loop_indices;
          }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
        let symbolic_fwd_es_ctx =
          EventStructureContext.create symbolic_structure
        in
          {
            program = [];
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }

  (* Test 5: Empty loop (VALID) *)
  let test_empty_loop_setup () =
    let init = Event.create Init 0 () in
    let events = Hashtbl.create 1 in
      Hashtbl.add events init.label init;
      let symbolic_structure =
        {
          (SymbolicEventStructure.create ()) with
          e = USet.of_list [ init.label ];
          events;
          loop_indices = Hashtbl.create 0;
        }
      in
      let symbolic_source_spans = Hashtbl.create 0 in
      let symbolic_justifications = USet.create () in
      let symbolic_fwd_es_ctx =
        EventStructureContext.create symbolic_structure
      in
        {
          program = [];
          symbolic_structure;
          symbolic_source_spans;
          symbolic_justifications;
          symbolic_fwd_es_ctx;
        }

  let write_test_cases =
    [
      {
        name = "modifying write after read";
        setup = test_mod_write_after_read_setup;
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description =
          "Modifying write not sequenced before read in same iteration";
      };
      {
        name = "same iteration write before read";
        setup = test_same_iteration_write_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Write properly sequenced before read in same iteration";
      };
      {
        name = "multiple unordered writes";
        setup = test_multiple_unordered_writes_setup;
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description = "Multiple writes to same location, one not sequenced";
      };
      {
        name = "read dont modify RMW";
        setup = test_rdmw_valid_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Read-don't-modify RMW is valid even without sequencing";
      };
      {
        name = "empty loop";
        setup = test_empty_loop_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Empty loop has no violations";
      };
    ]

  let run_write_test_case test_case () =
    let cache = test_case.setup () in
      let* result = WriteCondition.check cache 0 in
        check bool
          (Printf.sprintf "%s - satisfied" test_case.name)
          test_case.expected_satisfied result.satisfied;
        ( match test_case.expected_violation_count with
        | Some expected_count ->
            check int
              (Printf.sprintf "%s - violation count" test_case.name)
              expected_count
              (List.length result.violations)
        | None ->
            if not test_case.expected_satisfied then
              check bool
                (Printf.sprintf "%s - has violations" test_case.name)
                true
                (List.length result.violations > 0)
        );
        Lwt.return_unit

  let suite =
    List.map
      (fun tc ->
        test_case tc.name `Quick (fun () ->
            Lwt_main.run ((run_write_test_case tc) ())
        )
      )
      write_test_cases
end

module TestBranchCondition = struct
  (* Type for test case specifications *)
  type branch_test_case = {
    name : string;
    setup : unit -> ir_node list * episodicity_cache;
    expected_satisfied : bool;
    expected_violation_count : int option;
    description : string;
  }

  (* Helper to create symbol origin table *)
  let create_origin_table entries =
    let tbl = Hashtbl.create 10 in
      List.iter (fun (sym, evt) -> Hashtbl.add tbl sym evt) entries;
      tbl

  (* Test 1: Branch constrains pre-loop symbol (VIOLATION) *)
  let test_branch_pre_loop_symbol_setup () =
    let init = Event.create Init 0 () in
    let pre_read =
      Event.create Read 1 ~loc:(ESymbol "x") ~rval:(VSymbol "α") ()
    in
    let branch =
      Event.create Branch 2
        ~cond:(EBinOp (ESymbol "α", "=", ENum (Z.of_int 1)))
        ()
    in
    let events = Hashtbl.create 3 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; pre_read; branch ];
      let loop_indices = Hashtbl.create 1 in
        Hashtbl.add loop_indices branch.label [ 0 ];
        let origin = create_origin_table [ ("α", pre_read.label) ] in
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = USet.of_list [ init.label; pre_read.label; branch.label ];
            events;
            branch_events = USet.of_list [ branch.label ];
            loop_indices;
            origin;
          }
        in
        let program =
          [
            make_ir_node
              (GlobalLoad
                 { register = "rtest"; global = "x"; load = make_load_info () }
              );
            make_ir_node
              (Do
                 {
                   body =
                     [
                       make_ir_node
                         (If
                            {
                              condition =
                                EBinOp (EVar "rtest", "=", ENum (Z.of_int 1));
                              then_body =
                                [
                                  make_ir_node
                                    (RegisterStore
                                       {
                                         register = "rtemp";
                                         expr = ENum (Z.of_int 1);
                                       }
                                    );
                                ];
                              else_body = None;
                            }
                         );
                     ];
                   condition = EBinOp (EVar "rtemp", "=", ENum (Z.of_int 0));
                 }
              );
          ]
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
        let symbolic_fwd_es_ctx =
          EventStructureContext.create symbolic_structure
        in
        let cache =
          {
            program;
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }
        in
          (program, cache)

  (* Test 2: Branch only uses in-loop symbols (VALID) *)
  let test_branch_in_loop_symbols_setup () =
    let init = Event.create Init 0 () in
    let loop_read =
      Event.create Read 1 ~loc:(ESymbol "一") ~rval:(VSymbol "β") ()
    in
    let branch =
      Event.create Branch 2
        ~cond:(EBinOp (ESymbol "β", "<", ENum (Z.of_int 10)))
        ()
    in
    let events = Hashtbl.create 3 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; loop_read; branch ];
      let loop_indices = Hashtbl.create 2 in
        Hashtbl.add loop_indices loop_read.label [ 0 ];
        Hashtbl.add loop_indices branch.label [ 0 ];
        let origin = create_origin_table [ ("β", loop_read.label) ] in
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = USet.of_list [ init.label; loop_read.label; branch.label ];
            events;
            branch_events = USet.of_list [ branch.label ];
            loop_indices;
            origin;
          }
        in
        let program =
          [
            make_ir_node
              (Do
                 {
                   body =
                     [
                       make_ir_node
                         (RegisterStore
                            { register = "ri"; expr = ENum (Z.of_int 0) }
                         );
                       make_ir_node
                         (If
                            {
                              condition =
                                EBinOp (EVar "ri", "<", ENum (Z.of_int 10));
                              then_body =
                                [
                                  make_ir_node
                                    (RegisterStore
                                       {
                                         register = "ri";
                                         expr =
                                           EBinOp
                                             (EVar "ri", "+", ENum (Z.of_int 1));
                                       }
                                    );
                                ];
                              else_body = None;
                            }
                         );
                     ];
                   condition = EBinOp (EVar "ri", "<", ENum (Z.of_int 5));
                 }
              );
          ]
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
        let symbolic_fwd_es_ctx =
          EventStructureContext.create symbolic_structure
        in
        let cache =
          {
            program;
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }
        in
          (program, cache)

  (* Test 3: Nested branches with pre-loop symbol (VIOLATION) *)
  let test_nested_branch_pre_loop_setup () =
    let init = Event.create Init 0 () in
    let pre_read =
      Event.create Read 1 ~loc:(ESymbol "x") ~rval:(VSymbol "α") ()
    in
    let outer_branch =
      Event.create Branch 2
        ~cond:(EBinOp (ESymbol "α", ">", ENum (Z.of_int 0)))
        ()
    in
    let inner_branch =
      Event.create Branch 3
        ~cond:(EBinOp (ESymbol "α", "=", ENum (Z.of_int 1)))
        ()
    in
    let events = Hashtbl.create 4 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; pre_read; outer_branch; inner_branch ];
      let loop_indices = Hashtbl.create 2 in
        Hashtbl.add loop_indices outer_branch.label [ 0 ];
        Hashtbl.add loop_indices inner_branch.label [ 0 ];
        let origin = create_origin_table [ ("α", pre_read.label) ] in
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e =
              USet.of_list
                [
                  init.label;
                  pre_read.label;
                  outer_branch.label;
                  inner_branch.label;
                ];
            events;
            branch_events =
              USet.of_list [ outer_branch.label; inner_branch.label ];
            loop_indices;
            origin;
          }
        in
        let program =
          [
            make_ir_node
              (GlobalLoad
                 { register = "rval"; global = "x"; load = make_load_info () }
              );
            make_ir_node
              (While
                 {
                   condition = EBinOp (EVar "ri", "<", ENum (Z.of_int 5));
                   body =
                     [
                       make_ir_node
                         (If
                            {
                              condition =
                                EBinOp (EVar "rval", ">", ENum (Z.of_int 0));
                              then_body =
                                [
                                  make_ir_node
                                    (If
                                       {
                                         condition =
                                           EBinOp
                                             ( EVar "rval",
                                               "=",
                                               ENum (Z.of_int 1)
                                             );
                                         then_body =
                                           [
                                             make_ir_node
                                               (RegisterStore
                                                  {
                                                    register = "ri";
                                                    expr = ENum (Z.of_int 10);
                                                  }
                                               );
                                           ];
                                         else_body = None;
                                       }
                                    );
                                ];
                              else_body = None;
                            }
                         );
                     ];
                 }
              );
          ]
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
        let symbolic_fwd_es_ctx =
          EventStructureContext.create symbolic_structure
        in
        let cache =
          {
            program;
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }
        in
          (program, cache)

  (* Test 4: Empty loop (VALID) *)
  let test_empty_loop_setup () =
    let init = Event.create Init 0 () in
    let events = Hashtbl.create 1 in
      Hashtbl.add events init.label init;
      let symbolic_structure =
        {
          (SymbolicEventStructure.create ()) with
          e = USet.of_list [ init.label ];
          events;
          loop_indices = Hashtbl.create 0;
        }
      in
      let program =
        [ make_ir_node (While { condition = EBoolean false; body = [] }) ]
      in
      let symbolic_source_spans = Hashtbl.create 0 in
      let symbolic_justifications = USet.create () in
      let symbolic_fwd_es_ctx =
        EventStructureContext.create symbolic_structure
      in
      let cache =
        {
          program;
          symbolic_structure;
          symbolic_source_spans;
          symbolic_justifications;
          symbolic_fwd_es_ctx;
        }
      in
        (program, cache)

  (* Test 5: Branch with no symbols (VALID) *)
  let test_branch_no_symbols_setup () =
    let init = Event.create Init 0 () in
    let branch = Event.create Branch 1 ~cond:(EBoolean true) () in
    let events = Hashtbl.create 2 in
      List.iter (fun e -> Hashtbl.add events e.label e) [ init; branch ];
      let loop_indices = Hashtbl.create 1 in
        Hashtbl.add loop_indices branch.label [ 0 ];
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = USet.of_list [ init.label; branch.label ];
            events;
            branch_events = USet.of_list [ branch.label ];
            loop_indices;
          }
        in
        let program =
          [
            make_ir_node
              (While
                 {
                   condition = EBoolean true;
                   body =
                     [
                       make_ir_node
                         (RegisterStore
                            { register = "r1"; expr = ENum (Z.of_int 1) }
                         );
                     ];
                 }
              );
          ]
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
        let symbolic_fwd_es_ctx =
          EventStructureContext.create symbolic_structure
        in
        let cache =
          {
            program;
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }
        in
          (program, cache)

  let branch_test_cases =
    [
      {
        name = "branch constrains pre-loop symbol";
        setup = test_branch_pre_loop_symbol_setup;
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description =
          "Branch condition constrains symbol read before loop (violation)";
      };
      {
        name = "branch uses in-loop symbols";
        setup = test_branch_in_loop_symbols_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Branch condition only uses symbols from within loop";
      };
      {
        name = "nested branches with pre-loop symbol";
        setup = test_nested_branch_pre_loop_setup;
        expected_satisfied = false;
        expected_violation_count = Some 2;
        description = "Nested branches both constrain pre-loop symbol";
      };
      {
        name = "empty loop";
        setup = test_empty_loop_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Empty loop has no branch violations";
      };
      {
        name = "branch with no symbols";
        setup = test_branch_no_symbols_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Branch with constant condition has no violations";
      };
    ]

  let run_branch_test_case test_case () =
    let _, cache = test_case.setup () in
      let* result = BranchCondition.check cache 0 in
        check bool
          (Printf.sprintf "%s - satisfied" test_case.name)
          test_case.expected_satisfied result.satisfied;
        ( match test_case.expected_violation_count with
        | Some expected_count ->
            check int
              (Printf.sprintf "%s - violation count" test_case.name)
              expected_count
              (List.length result.violations)
        | None ->
            if not test_case.expected_satisfied then
              check bool
                (Printf.sprintf "%s - has violations" test_case.name)
                true
                (List.length result.violations > 0)
        );
        Lwt.return_unit

  let suite =
    List.map
      (fun tc ->
        test_case tc.name `Quick (fun () ->
            Lwt_main.run ((run_branch_test_case tc) ())
        )
      )
      branch_test_cases
end

module TestEventOrdering = struct
  (* Type for test case specifications *)
  type ordering_test_case = {
    name : string;
    setup : unit -> episodicity_cache Lwt.t;
    expected_satisfied : bool;
    expected_violation_count : int option;
    description : string;
  }

  (* Helper to create proper ppo structure in forwarding context *)
  let create_ppo_structure ppo_pairs ppo_iter_pairs =
    let ppo_init = USet.create () in

    let ppo_loc_base = USet.create () in
    let ppo_base = USet.create () in
    let ppo_sync = USet.create () in
    let ppo_loc_base = USet.create () in
    let ppo_loc_eq = USet.create () in

    let ppo_iter_loc_base = USet.create () in
    let ppo_iter_base = USet.create () in
    let ppo_iter_sync = USet.create () in
    let ppo_iter_loc_base = USet.create () in
    let ppo_iter_loc_eq = USet.create () in

    USet.of_list ppo_pairs |> USet.inplace_union ppo_base |> ignore;
    USet.of_list ppo_iter_pairs |> USet.inplace_union ppo_iter_base |> ignore;

    {
      ppo_init;
      ppo_base;
      ppo_sync;
      ppo_loc_base;
      ppo_loc_eq;
      ppo_iter_loc_base;
      ppo_iter_base;
      ppo_iter_sync;
      ppo_iter_loc_eq;
    }

  (* Test 1: Proper ordering via ppo (VALID) *)
  let test_proper_ppo_ordering_setup () =
    let init = Event.create Init 0 () in
    let iter0_write =
      Event.create Write 1 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 0)) ()
    in
    let iter1_read =
      Event.create Read 2 ~loc:(ESymbol "一") ~rval:(VSymbol "α") ()
    in
    let events = Hashtbl.create 3 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; iter0_write; iter1_read ];
      let loop_indices = Hashtbl.create 2 in
        Hashtbl.add loop_indices iter0_write.label [ 0 ];
        Hashtbl.add loop_indices iter1_read.label [ 1 ];
        let po_iter = USet.of_list [ (iter0_write.label, iter1_read.label) ] in
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = USet.of_list [ init.label; iter0_write.label; iter1_read.label ];
            events;
            loop_indices;
            po_iter;
          }
        in
        let ppo =
          create_ppo_structure [] [ (iter0_write.label, iter1_read.label) ]
        in
        let symbolic_fwd_es_ctx =
          { (EventStructureContext.create symbolic_structure) with ppo }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
          Lwt.return
            {
              program = [];
              symbolic_structure;
              symbolic_source_spans;
              symbolic_justifications;
              symbolic_fwd_es_ctx;
            }

  (* Test 2: Missing ordering between iterations (VIOLATION) *)
  let test_missing_iteration_ordering_setup () =
    let init = Event.create Init 0 () in
    let iter0_write =
      Event.create Write 1 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 0)) ()
    in
    let iter1_write =
      Event.create Write 2 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 1)) ()
    in
    let events = Hashtbl.create 3 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; iter0_write; iter1_write ];
      let loop_indices = Hashtbl.create 2 in
        Hashtbl.add loop_indices iter0_write.label [ 0 ];
        Hashtbl.add loop_indices iter1_write.label [ 1 ];
        let po_iter = USet.of_list [ (iter0_write.label, iter1_write.label) ] in
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e =
              USet.of_list [ init.label; iter0_write.label; iter1_write.label ];
            events;
            loop_indices;
            po_iter;
          }
        in
        (* No ppo_iter ordering provided - violation *)
        let ppo = create_ppo_structure [] [] in
        let symbolic_fwd_es_ctx =
          { (EventStructureContext.create symbolic_structure) with ppo }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
          Lwt.return
            {
              program = [];
              symbolic_structure;
              symbolic_source_spans;
              symbolic_justifications;
              symbolic_fwd_es_ctx;
            }

  (* Test 3: Empty loop (VALID) *)
  let test_empty_loop_setup () =
    let init = Event.create Init 0 () in
    let events = Hashtbl.create 1 in
      Hashtbl.add events init.label init;
      let symbolic_structure =
        {
          (SymbolicEventStructure.create ()) with
          e = USet.of_list [ init.label ];
          events;
          loop_indices = Hashtbl.create 0;
        }
      in
      let ppo = create_ppo_structure [] [] in
      let symbolic_fwd_es_ctx =
        { (EventStructureContext.create symbolic_structure) with ppo }
      in
      let symbolic_source_spans = Hashtbl.create 0 in
      let symbolic_justifications = USet.create () in
        Lwt.return
          {
            program = [];
            symbolic_structure;
            symbolic_source_spans;
            symbolic_justifications;
            symbolic_fwd_es_ctx;
          }

  (* Test 4: Multiple events same iteration (VALID) *)
  let test_same_iteration_events_setup () =
    let init = Event.create Init 0 () in
    let write1 =
      Event.create Write 1 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 0)) ()
    in
    let write2 =
      Event.create Write 2 ~loc:(ESymbol "二") ~wval:(ENum (Z.of_int 0)) ()
    in
    let events = Hashtbl.create 3 in
      List.iter (fun e -> Hashtbl.add events e.label e) [ init; write1; write2 ];
      let loop_indices = Hashtbl.create 2 in
        Hashtbl.add loop_indices write1.label [ 0 ];
        Hashtbl.add loop_indices write2.label [ 0 ];
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e = USet.of_list [ init.label; write1.label; write2.label ];
            events;
            loop_indices;
            po_iter = USet.create ();
          }
        in
        let ppo = create_ppo_structure [] [] in
        let symbolic_fwd_es_ctx =
          { (EventStructureContext.create symbolic_structure) with ppo }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
          Lwt.return
            {
              program = [];
              symbolic_structure;
              symbolic_source_spans;
              symbolic_justifications;
              symbolic_fwd_es_ctx;
            }

  (* Test 5: Chain of iterations (VALID) *)
  let test_iteration_chain_setup () =
    let init = Event.create Init 0 () in
    let iter0 =
      Event.create Write 1 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 0)) ()
    in
    let iter1 =
      Event.create Write 2 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 1)) ()
    in
    let iter2 =
      Event.create Write 3 ~loc:(ESymbol "一") ~wval:(ENum (Z.of_int 2)) ()
    in
    let events = Hashtbl.create 4 in
      List.iter
        (fun e -> Hashtbl.add events e.label e)
        [ init; iter0; iter1; iter2 ];
      let loop_indices = Hashtbl.create 3 in
        Hashtbl.add loop_indices iter0.label [ 0 ];
        Hashtbl.add loop_indices iter1.label [ 1 ];
        Hashtbl.add loop_indices iter2.label [ 2 ];
        let po_iter =
          USet.of_list
            [ (iter0.label, iter1.label); (iter1.label, iter2.label) ]
        in
        let symbolic_structure =
          {
            (SymbolicEventStructure.create ()) with
            e =
              USet.of_list [ init.label; iter0.label; iter1.label; iter2.label ];
            events;
            loop_indices;
            po_iter;
          }
        in
        (* Provide ppo_iter for all transitions *)
        let ppo =
          create_ppo_structure []
            [ (iter0.label, iter1.label); (iter1.label, iter2.label) ]
        in
        let symbolic_fwd_es_ctx =
          { (EventStructureContext.create symbolic_structure) with ppo }
        in
        let symbolic_source_spans = Hashtbl.create 0 in
        let symbolic_justifications = USet.create () in
          Lwt.return
            {
              program = [];
              symbolic_structure;
              symbolic_source_spans;
              symbolic_justifications;
              symbolic_fwd_es_ctx;
            }

  let ordering_test_cases =
    [
      {
        name = "proper ppo ordering";
        setup = test_proper_ppo_ordering_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Events properly ordered via ppo between iterations";
      };
      {
        name = "missing iteration ordering";
        setup = test_missing_iteration_ordering_setup;
        expected_satisfied = false;
        expected_violation_count = Some 1;
        description =
          "Events from different iterations not properly ordered (violation)";
      };
      {
        name = "empty loop";
        setup = test_empty_loop_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Empty loop has no ordering violations";
      };
      {
        name = "same iteration events";
        setup = test_same_iteration_events_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Multiple events in same iteration don't need ordering";
      };
      {
        name = "iteration chain";
        setup = test_iteration_chain_setup;
        expected_satisfied = true;
        expected_violation_count = Some 0;
        description = "Chain of iterations properly ordered via ppo";
      };
    ]

  let run_ordering_test_case test_case () =
    let* cache = test_case.setup () in
      let* result = EventsCondition.check cache 0 in
        check bool
          (Printf.sprintf "%s - satisfied" test_case.name)
          test_case.expected_satisfied result.satisfied;
        ( match test_case.expected_violation_count with
        | Some expected_count ->
            check int
              (Printf.sprintf "%s - violation count" test_case.name)
              expected_count
              (List.length result.violations)
        | None ->
            if not test_case.expected_satisfied then
              check bool
                (Printf.sprintf "%s - has violations" test_case.name)
                true
                (List.length result.violations > 0)
        );
        Lwt.return_unit

  let suite =
    List.map
      (fun tc ->
        test_case tc.name `Quick (fun () ->
            Lwt_main.run ((run_ordering_test_case tc) ())
        )
      )
      ordering_test_cases
end

module TestBisection = struct
  (** Helpers to build minimal symbolic event structures for bisection tests.

      loop_indices uses the full prefix-closed path convention: e.g. [1; 2; 3]
      means the event is nested inside loop 1 → loop 2 → loop 3. *)

  (** Build a structure where all events are directly in [loop_id] with no
      further nesting (loop_indices = [[loop_id]] for every event). *)
  let make_flat_structure loop_id event_labels po_pairs =
    let e = USet.of_list event_labels in
    let loop_indices = Hashtbl.create (List.length event_labels) in
      List.iter
        (fun lbl -> Hashtbl.add loop_indices lbl [ loop_id ])
        event_labels;
      let po = USet.of_list po_pairs in
        { (SymbolicEventStructure.create ()) with e; loop_indices; po }

  (** Build a structure where events may have arbitrarily long loop index paths.
      [assignments] is [(event_label, path)] list. *)
  let make_nested_structure event_labels path_assignments po_pairs =
    let e = USet.of_list event_labels in
    let loop_indices = Hashtbl.create (List.length event_labels) in
      List.iter
        (fun (lbl, path) -> Hashtbl.add loop_indices lbl path)
        path_assignments;
      let po = USet.of_list po_pairs in
        { (SymbolicEventStructure.create ()) with e; loop_indices; po }

  (* ------------------------------------------------------------------ *)
  (* Tests for bisect_loop                                               *)
  (* ------------------------------------------------------------------ *)

  (** bisect_loop should remove (left × right) from po and add (right × left).
  *)
  let test_bisect_loop_reverses_po () =
    (* Events 1 and 2 are both in loop 0, po has 1 → 2 *)
    let structure = make_flat_structure 0 [ 1; 2 ] [ (1, 2) ] in
    let left = USet.of_list [ 1 ] in
    let right = USet.of_list [ 2 ] in
    let result = Bisection.bisect_loop structure 0 left right in
      (* After bisection: (1,2) removed, (2,1) added *)
      check bool "bisect removes left→right" false (USet.mem result.po (1, 2));
      check bool "bisect adds right→left" true (USet.mem result.po (2, 1))

  let test_bisect_loop_no_cross_po () =
    (* bisect_loop always adds the full right×left cross product to po,
       regardless of whether any left→right edges existed before.
       With left={1,2} and right={3}: (3,1) and (3,2) will be added.
       The intra-left edge (1,2) must be preserved unchanged. *)
    let structure = make_flat_structure 0 [ 1; 2; 3 ] [ (1, 2) ] in
    let left = USet.of_list [ 1; 2 ] in
    let right = USet.of_list [ 3 ] in
    let result = Bisection.bisect_loop structure 0 left right in
      check bool "intra-left edge preserved" true (USet.mem result.po (1, 2));
      check bool "right→left edge (3,1) added" true (USet.mem result.po (3, 1));
      check bool "right→left edge (3,2) added" true (USet.mem result.po (3, 2));
      check bool "no left→right for (1,3)" false (USet.mem result.po (1, 3));
      check bool "no left→right for (2,3)" false (USet.mem result.po (2, 3))

  (* ------------------------------------------------------------------ *)
  (* Tests for all_bisections — flat (no nesting)                        *)
  (* ------------------------------------------------------------------ *)

  let test_all_bisections_empty_loop () =
    (* No events in loop → only the ({},{}) bisection *)
    let structure = make_flat_structure 0 [] [] in
    let bisections = Bisection.all_bisections structure 0 in
      check int "one bisection for empty loop" 1 (List.length bisections);
      let l, r = List.hd bisections in
        check bool "left empty" true (USet.is_empty l);
        check bool "right empty" true (USet.is_empty r)

  let test_all_bisections_single_event () =
    (* One event in loop → two subsets: {},{e} and {e},{} — both valid
       since no po constraint can be violated with a single event *)
    let structure = make_flat_structure 0 [ 1 ] [] in
    let bisections = Bisection.all_bisections structure 0 in
      check int "two bisections for single event" 2 (List.length bisections)

  let test_all_bisections_po_constraint () =
    (* Events 1 and 2 with po 1→2.
       {},{1,2}:           cross empty → VALID
       {1,2},{}:           cross empty → VALID
       {left={1},right={2}}: cross(left,right) = {(1,2)} ⊆ po → VALID
       {left={2},right={1}}: cross(left,right) = {(2,1)} ⊄ po → INVALID
       Expected: 3 valid bisections. *)
    let structure = make_flat_structure 0 [ 1; 2 ] [ (1, 2) ] in
    let bisections = Bisection.all_bisections structure 0 in
      check int "three bisections valid with po 1→2" 3 (List.length bisections);
      (* The invalid partition (left={2}, right={1}) must not appear *)
      let invalid_present =
        List.exists (fun (l, r) -> USet.mem l 2 && USet.mem r 1) bisections
      in
        check bool "left={2},right={1} absent" false invalid_present

  let test_all_bisections_no_po_filters_partition () =
    (* Events 1 and 2 with no po.
       {left={1}, right={2}}: cross(left,right) = {(1,2)} ⊄ po → INVALID
       {left={2}, right={1}}: cross(left,right) = {(2,1)} ⊄ po → INVALID
       {},{1,2} and {1,2},{}: cross is empty → VALID
       Expected: 2 valid bisections *)
    let structure = make_flat_structure 0 [ 1; 2 ] [] in
    let bisections = Bisection.all_bisections structure 0 in
      check int "two bisections when no po" 2 (List.length bisections);
      List.iter
        (fun (l, r) ->
          check bool "one side empty" true (USet.is_empty l || USet.is_empty r)
        )
        bisections

  (* ------------------------------------------------------------------ *)
  (* Tests for all_bisections — nested-loop sub-group constraint         *)
  (* ------------------------------------------------------------------ *)

  (** Scenario from the spec:
      loop_id = 2
      Events:
        e1 → path [1;2;3]     (in sub-loop 3)
        e2 → path [1;2;3;4]   (in sub-loop 3 → 4, child of 3 under 2 is 3)
        e3 → path [1;2;3;5]   (in sub-loop 3 → 5, child of 3 under 2 is 3)
        e4 → path [1;2;6]     (in sub-loop 6)
      po: none (simplifies bisection logic)

      Valid bisection: {e1,e2,e3} left, {e4} right — sub-loop 3 all-left, 6 all-right.
      Invalid: {e2} left, {e1,e3,e4} right — e2 and e1 both in sub-loop 3, split.
      Invalid: {e1,e2,e4} left, {e3} right — e1,e2,e3 in sub-loop 3, e3 on right. *)

  let test_nested_loops_valid_bisection () =
    (* loop_id = 2, events:
         e1 [1;2;3], e2 [1;2;3;4], e3 [1;2;3;5]  — all in sub-loop group 3
         e4 [1;2;6]                                — sub-loop group 6
       For the partition left={e1,e2,e3}, right={e4} to survive the po filter
       we need cross(left,right) = {(1,4),(2,4),(3,4)} ⊆ po. *)
    let structure =
      make_nested_structure [ 1; 2; 3; 4 ]
        [
          (1, [ 1; 2; 3 ]);
          (2, [ 1; 2; 3; 4 ]);
          (3, [ 1; 2; 3; 5 ]);
          (4, [ 1; 2; 6 ]);
        ]
        [ (1, 4); (2, 4); (3, 4) ]
      (* po: sub-loop-3 events before sub-loop-6 event *)
    in
    let bisections = Bisection.all_bisections structure 2 in
    let left_123_right_4 =
      List.exists
        (fun (l, r) ->
          USet.equal l (USet.of_list [ 1; 2; 3 ])
          && USet.equal r (USet.of_list [ 4 ])
        )
        bisections
    in
      check bool "sub-loop 3 all-left, sub-loop 6 all-right is valid" true
        left_123_right_4

  let test_nested_loops_invalid_split_sub_loop () =
    (* e1 path [1;2;3], e2 path [1;2;3;4]: both child=3 under loop 2.
       Splitting them across sides is invalid. *)
    let structure =
      make_nested_structure [ 1; 2 ]
        [ (1, [ 1; 2; 3 ]); (2, [ 1; 2; 3; 4 ]) ]
        [] (* no po — we want to isolate the sub-loop constraint *)
    in
    let bisections = Bisection.all_bisections structure 2 in
    (* The partition ({e1},{e2}) and ({e2},{e1}) should be absent *)
    let split_found =
      List.exists
        (fun (l, r) ->
          (USet.mem l 1 && USet.mem r 2) || (USet.mem l 2 && USet.mem r 1)
        )
        bisections
    in
      check bool "splitting events in same sub-loop is invalid" false
        split_found

  let test_nested_loops_different_sub_loops_can_split () =
    (* e1 path [1;2;3], e2 path [1;2;4]: different child loops → can be split *)
    let structure =
      make_nested_structure [ 1; 2 ]
        [ (1, [ 1; 2; 3 ]); (2, [ 1; 2; 4 ]) ]
        [ (1, 2) ]
      (* po 1→2 to allow left={1},right={2} *)
    in
    let bisections = Bisection.all_bisections structure 2 in
    let split_found =
      List.exists (fun (l, r) -> USet.mem l 1 && USet.mem r 2) bisections
    in
      check bool "events in different sub-loops may be split" true split_found

  let test_nested_direct_and_nested_events () =
    (* e1 directly in loop 2 (path [2]), e2 in sub-loop 3 (path [2;3]).
       child_loop_of e1 loop 2 = None; child_loop_of e2 loop 2 = Some 3.
       Since they have different keys (None vs Some 3) they can be on different sides. *)
    let structure =
      make_nested_structure [ 1; 2 ] [ (1, [ 2 ]); (2, [ 2; 3 ]) ] [ (1, 2) ]
      (* po 1→2 *)
    in
    let bisections = Bisection.all_bisections structure 2 in
    let split_found =
      List.exists (fun (l, r) -> USet.mem l 1 && USet.mem r 2) bisections
    in
      check bool "direct-in-loop and sub-loop events may be split" true
        split_found

  let test_nested_same_group_none_not_split () =
    (* Two events directly in loop 2 (path [2] each) have no child loop.
       The nesting constraint does NOT apply to them — only the po filter does.
       With no po edges, cross(left,right) is not a subset of po, so neither
       single-event partition passes the po filter. Only the trivial all-left
       and all-right partitions are valid. *)
    let structure =
      make_nested_structure [ 1; 2 ] [ (1, [ 2 ]); (2, [ 2 ]) ] [] (* no po *)
    in
    let bisections = Bisection.all_bisections structure 2 in
    (* Neither ({1},{2}) nor ({2},{1}) should pass the po filter *)
    let split_found =
      List.exists
        (fun (l, r) ->
          (USet.mem l 1 && USet.mem r 2) || (USet.mem l 2 && USet.mem r 1)
        )
        bisections
    in
      check bool "direct-in-loop events blocked by po filter (not nesting)"
        false split_found;
      check int "only trivial bisections pass" 2 (List.length bisections)

  let test_complex_nested_scenario () =
    (* Full example from spec:
       e1 [1;2;3], e2 [1;2;3;4], e3 [1;2;3;5] all have child=3 under loop 2.
       e4 [1;2;6] has child=6 under loop 2.
       Bisection ({e1,e2,e3},{e4}) VALID; ({e2},{e1,e3,e4}) INVALID. *)
    let structure =
      make_nested_structure [ 1; 2; 3; 4 ]
        [
          (1, [ 1; 2; 3 ]);
          (2, [ 1; 2; 3; 4 ]);
          (3, [ 1; 2; 3; 5 ]);
          (4, [ 1; 2; 6 ]);
        ]
        (* Need po edges for non-trivial left/right to satisfy po filter.
         Add 1→4 to allow {e1,e2,e3}→left, e4→right *)
        [ (1, 4); (2, 4); (3, 4) ]
    in
    let bisections = Bisection.all_bisections structure 2 in
    let left_e123_right_e4 =
      List.exists
        (fun (l, r) ->
          USet.equal l (USet.of_list [ 1; 2; 3 ])
          && USet.equal r (USet.of_list [ 4 ])
        )
        bisections
    in
    let invalid_e2_left_others_right =
      List.exists (fun (l, r) -> USet.mem l 2 && USet.mem r 1) bisections
    in
      check bool "valid bisection: sub-loop-3 all-left, sub-loop-6 all-right"
        true left_e123_right_e4;
      check bool "invalid bisection: e1 and e2 (both sub-loop 3) split" false
        invalid_e2_left_others_right

  let test_nested_same_group_none_can_split_with_po () =
    (* Two events directly in loop 2 (path [2] each) — no child loop constraint.
       With po edge (1,2), the partition left={1},right={2} passes both filters. *)
    let structure =
      make_nested_structure [ 1; 2 ] [ (1, [ 2 ]); (2, [ 2 ]) ] [ (1, 2) ]
    in
    let bisections = Bisection.all_bisections structure 2 in
    let split_found =
      List.exists (fun (l, r) -> USet.mem l 1 && USet.mem r 2) bisections
    in
      check bool "direct-in-loop events can split when po permits" true
        split_found

  let suite =
    [
      test_case "bisect_loop reverses po edge" `Quick
        test_bisect_loop_reverses_po;
      test_case "bisect_loop always adds right×left" `Quick
        test_bisect_loop_no_cross_po;
      test_case "all_bisections empty loop" `Quick
        test_all_bisections_empty_loop;
      test_case "all_bisections single event" `Quick
        test_all_bisections_single_event;
      test_case "all_bisections with po constraint" `Quick
        test_all_bisections_po_constraint;
      test_case "all_bisections no po filters partition" `Quick
        test_all_bisections_no_po_filters_partition;
      test_case "nested: valid sub-loop bisection" `Quick
        test_nested_loops_valid_bisection;
      test_case "nested: split sub-loop invalid" `Quick
        test_nested_loops_invalid_split_sub_loop;
      test_case "nested: different sub-loops can split" `Quick
        test_nested_loops_different_sub_loops_can_split;
      test_case "nested: direct and sub-loop can split" `Quick
        test_nested_direct_and_nested_events;
      test_case "nested: direct events blocked by po not nesting" `Quick
        test_nested_same_group_none_not_split;
      test_case "nested: direct events can split with po" `Quick
        test_nested_same_group_none_can_split_with_po;
      test_case "nested: complex multi-group scenario" `Quick
        test_complex_nested_scenario;
    ]
end

let suite =
  ( "Episodicity",
    TestRegisterCondition.suite
    @ TestWriteCondition.suite
    @ TestBranchCondition.suite
    @ TestEventOrdering.suite
    @ TestBisection.suite
  )
