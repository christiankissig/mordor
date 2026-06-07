open Alcotest

(** Tests for the Isabelle interchange export ([isa] output mode), against the
    contract in [docs/MORDOR_ISA_FORMAT.md]. These exercise the pure structural
    rendering (program → init/threads/commands) plus the expression and order
    grammars; the futures part (which needs the solver pipeline) is covered by
    the integration / CLI tests. *)

let uaf_bug_src =
  {|rC := malloc(1);
*rC := 0;
rcu := malloc(1);
*rcu := 1;
{
  rtemp := *rcu;
  if (rtemp = 0) {
    free(rC);
  }
}
|||
{
  rv := *rC;
  *rcu := 0;
}|}

(** Parse a source string and stash the IR program in a fresh context. *)
let ctx_of_src ?(name = "fixture") src =
  let ir = Parse.parse_and_convert_litmus ~validate_ast:(fun _ -> ()) src in
  let ctx =
    Context.make_context Context.default_options ~output_mode:Context.Isa
      ~num_threads:1 ()
  in
    ctx.litmus_name <- name;
    ctx.program_stmts <- Some ir.program;
    ctx

let doc_of_src ?name src =
  Isa_export.build_document (ctx_of_src ?name src)

(* JSON navigation helpers. *)
let field k = function
  | `Assoc l -> List.assoc k l
  | _ -> failf "expected object when looking up %s" k

let as_list = function
  | `List l -> l
  | _ -> fail "expected JSON list"

let as_string = function
  | `String s -> s
  | _ -> fail "expected JSON string"

let op_of instr = field "command" instr |> field "op" |> as_string
let label_of instr = field "label" instr |> as_string

(** The header carries the schema version, program name, and order vocabulary. *)
let test_header () =
  let d = doc_of_src ~name:"uaf-bug.lit" uaf_bug_src in
    check string "format_version" "0.1"
      (field "format_version" d |> as_string);
    check string "program" "uaf-bug.lit" (field "program" d |> as_string);
    check (list string) "orders"
      [ "rlx"; "acq"; "rel"; "acq_rel"; "sc" ]
      (field "orders" d |> as_list |> List.map as_string)

(** init holds the four setup instructions, labelled g.1..g.4 in order. *)
let test_init () =
  let d = doc_of_src uaf_bug_src in
  let init = field "init" d |> as_list in
    check int "init count" 4 (List.length init);
    check (list string) "init labels"
      [ "g.1"; "g.2"; "g.3"; "g.4" ]
      (List.map label_of init);
    check (list string) "init ops"
      [ "Alloc"; "WritePtr"; "Alloc"; "WritePtr" ]
      (List.map op_of init)

(** threads expose tid-indexed bodies; the If keeps its then-branch nested and
    the per-thread seq counter flows into it (t0.1, t0.2 = If, t0.3 = free). *)
let test_threads_and_control_flow () =
  let d = doc_of_src uaf_bug_src in
  let threads = field "threads" d |> as_list in
    check int "thread count" 2 (List.length threads);
    let t0 = List.nth threads 0 in
      check int "tid 0" 0 (field "tid" t0 |> Yojson.Safe.Util.to_int);
      let body = field "body" t0 |> as_list in
        check (list string) "t0 labels" [ "t0.1"; "t0.2" ]
          (List.map label_of body);
        let if_instr = List.nth body 1 in
          check string "t0.2 is If" "If" (op_of if_instr);
          let then_b = field "command" if_instr |> field "then" |> as_list in
            check (list string) "nested then label" [ "t0.3" ]
              (List.map label_of then_b);
            check string "nested op" "Free" (op_of (List.hd then_b))

(** Each instruction carries the static event signature from the grammar. *)
let test_event_signatures () =
  let d = doc_of_src uaf_bug_src in
  let events instr =
    field "events" instr |> as_list
    |> List.map (fun e -> field "type" e |> as_string)
  in
  let init = field "init" d |> as_list in
    check (list string) "Alloc events" [ "Alloc" ] (events (List.hd init));
    let t1 = field "threads" d |> as_list |> fun l -> List.nth l 1 in
    let body = field "body" t1 |> as_list in
      check (list string) "ReadPtr events" [ "R" ] (events (List.hd body))

(** With no structure/executions in context, futures is present but empty. *)
let test_futures_empty_without_pipeline () =
  let d = doc_of_src uaf_bug_src in
    check int "empty futures" 0 (field "futures" d |> as_list |> List.length)

(** order_string maps the internal modes to the spec vocabulary. *)
let test_order_string () =
  check string "rlx" "rlx" (Isa_export.order_string Types.Relaxed);
  check string "acq" "acq" (Isa_export.order_string Types.Acquire);
  check string "rel" "rel" (Isa_export.order_string Types.Release);
  check string "acq_rel" "acq_rel"
    (Isa_export.order_string Types.ReleaseAcquire);
  check string "sc" "sc" (Isa_export.order_string Types.SC)

(** expr_json renders the documented expression grammar. *)
let test_expr_json () =
  let open Types in
  check bool "int" true
    (Isa_export.expr_json (ENum (Z.of_int 7))
    = `Assoc [ ("int", `Intlit "7") ]);
  check bool "reg" true
    (Isa_export.expr_json (EVar "r1") = `Assoc [ ("reg", `String "r1") ]);
  check bool "eq" true
    (Isa_export.expr_json (EBinOp (EVar "r", "=", ENum Z.zero))
    = `Assoc
        [ ("eq", `List [ `Assoc [ ("reg", `String "r") ];
                         `Assoc [ ("int", `Intlit "0") ] ]) ])

(** The whole document round-trips as valid JSON. *)
let test_valid_json () =
  let content = Isa_export.to_string (ctx_of_src uaf_bug_src) in
  match Yojson.Safe.from_string content with
  | `Assoc fields ->
      List.iter
        (fun k ->
          check bool ("has " ^ k) true (List.mem_assoc k fields))
        [ "format_version"; "program"; "orders"; "init"; "threads"; "futures" ]
  | _ -> fail "expected JSON object at top level"

let suite =
  ( "IsaExport",
    [
      ("header", `Quick, test_header);
      ("init instructions", `Quick, test_init);
      ("threads and control flow", `Quick, test_threads_and_control_flow);
      ("event signatures", `Quick, test_event_signatures);
      ("futures empty without pipeline", `Quick, test_futures_empty_without_pipeline);
      ("order_string", `Quick, test_order_string);
      ("expr_json", `Quick, test_expr_json);
      ("valid json", `Quick, test_valid_json);
    ]
  )
