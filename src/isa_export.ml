(** {1 Isabelle Interchange Export ([isa] output mode)}

    Serialises a litmus test and its computed futures into the versioned
    structured JSON described in [docs/MORDOR_ISA_FORMAT.md] (the
    [rcu-c11-opsem] interchange contract, v0.1). The document carries the
    rolled program (control flow preserved) split into [init] setup and
    per-thread [threads], plus the [futures] [(ppo ∪ dp)] edges rendered over
    stable event-labels.

    The repo-side renderer ([scripts/generate_phi.py]) turns this JSON into
    Isabelle source; mordor stays Isabelle-agnostic and only emits the schema.

    Label model (§2 of the spec):
    - instruction-label = ["t<tid>.<seq>"] for threads, ["g.<seq>"] for init
      setup, stable per source instruction (1-based pre-order [seq] per thread).
    - event-label = ["<instruction-label>[@<loop-id>:<iter>...]#<k>"], [k] the
      0-based event index within the instruction (RMWs share one
      instruction-label across their sub-events). *)

open Context
open Ir
open Types

(** The schema version emitted in every document. *)
let format_version = "0.1"

(** Memory orders advertised in the document header. *)
let orders = [ "rlx"; "acq"; "rel"; "acq_rel"; "sc" ]

(** Map an internal {!Types.mode} to its spec order string. *)
let order_string (m : mode) : string =
  match m with
  | Relaxed | Normal -> "rlx"
  | Acquire -> "acq"
  | Release -> "rel"
  | ReleaseAcquire -> "acq_rel"
  | SC | Strong -> "sc"
  | Nonatomic -> "na"
  | Consume -> "con"

let order_json (m : mode) : Yojson.Safe.t = `String (order_string m)

(** Map a binary operator to its expression-grammar key (§3). *)
let binop_key (op : string) : string =
  match op with
  | "=" | "==" -> "eq"
  | "!=" | "<>" -> "neq"
  | "<" -> "lt"
  | ">" -> "gt"
  | "<=" -> "le"
  | ">=" -> "ge"
  | "+" -> "add"
  | "-" -> "sub"
  | "*" -> "mul"
  | "/" -> "div"
  | "%" -> "mod"
  | "&&" -> "and"
  | "||" -> "or"
  | "&" -> "band"
  | "|" -> "bor"
  | "^" -> "bxor"
  | "," -> "tuple"
  | other -> other

(** Render an {!Types.expr} into the spec's expression grammar (§3). *)
let rec expr_json (e : expr) : Yojson.Safe.t =
  match e with
  | ENum n -> `Assoc [ ("int", `Intlit (Z.to_string n)) ]
  | EVar v -> `Assoc [ ("reg", `String v) ]
  | ESymbol s -> `Assoc [ ("sym", `String s) ]
  | EBoolean b -> `Assoc [ ("bool", `Bool b) ]
  | EUnOp (op, e1) ->
      let key =
        match op with
        | "!" | "not" -> "not"
        | "-" -> "neg"
        | other -> other
      in
        `Assoc [ (key, expr_json e1) ]
  | EOr es -> `Assoc [ ("or", `List (List.map expr_json es)) ]
  | EBinOp (e1, op, e2) ->
      `Assoc [ (binop_key op, `List [ expr_json e1; expr_json e2 ]) ]

(** Static event signature of an instruction: pairs of [(k, type)] in event
    order. RMWs expose all sub-events (a failing CAS simply never produces its
    [W] at runtime, so that label is just never referenced). *)
type instr_info = {
  label : string;
  events : (int * string) list;
  loops : int list;
}

(** Build the [command] object and static event signature for a leaf
    statement. Returns [None] for statements that produce no digest
    instruction (e.g. [Skip], or control flow handled by the caller). *)
let command_and_events (stmt : ir_node_ann ir_stmt) :
    (Yojson.Safe.t * (int * string) list) option =
  let op name fields = `Assoc (("op", `String name) :: fields) in
    match stmt with
    | RegisterStore { register; expr } ->
        Some
          ( op "Set" [ ("dst", `String register); ("expr", expr_json expr) ],
            [] )
    | RegisterRefAssign { register; global } ->
        Some
          ( op "ReadRef" [ ("dst", `String register); ("var", `String global) ],
            [] )
    | GlobalLoad { register; global; load } ->
        Some
          ( op "ReadVar"
              [
                ("order", order_json load.mode);
                ("dst", `String register);
                ("var", `String global);
              ],
            [ (0, "R") ] )
    | GlobalStore { global; expr; assign } ->
        Some
          ( op "WriteVar"
              [
                ("order", order_json assign.mode);
                ("var", `String global);
                ("val", expr_json expr);
              ],
            [ (0, "W") ] )
    | DerefLoad { register; address; load } ->
        Some
          ( op "ReadPtr"
              [
                ("order", order_json load.mode);
                ("dst", `String register);
                ("ptr", expr_json address);
              ],
            [ (0, "R") ] )
    | DerefStore { address; expr; assign } ->
        Some
          ( op "WritePtr"
              [
                ("order", order_json assign.mode);
                ("ptr", expr_json address);
                ("val", expr_json expr);
              ],
            [ (0, "W") ] )
    | Fadd { register; address; operand; rmw_mode; load_mode; assign_mode } ->
        Some
          ( op "Faa"
              [
                ("order_r", order_json load_mode);
                ("order_w", order_json assign_mode);
                ("dst", `String register);
                ("loc", expr_json address);
                ("addend", expr_json operand);
                ("rmw_op", `String rmw_mode);
              ],
            [ (0, "R"); (1, "W") ] )
    | Cas { register; address; expected; desired; load_mode; assign_mode } ->
        Some
          ( op "Cas"
              [
                ("order_r", order_json load_mode);
                ("order_w", order_json assign_mode);
                ("dst", `String register);
                ("loc", expr_json address);
                ("expected", expr_json expected);
                ("new", expr_json desired);
                ("rmw_op", `String "cas");
              ],
            [ (0, "R"); (1, "Branch"); (2, "W") ] )
    | RegMalloc { register; size } ->
        Some
          ( op "Alloc" [ ("dst", `String register); ("size", expr_json size) ],
            [ (0, "Alloc") ] )
    | GlobalMalloc { global; size } ->
        Some
          ( op "Alloc" [ ("dst", `String global); ("size", expr_json size) ],
            [ (0, "Alloc") ] )
    | Free { register } ->
        Some (op "Free" [ ("ptr", `String register) ], [ (0, "Dealloc") ])
    | Fence { mode } ->
        Some (op "Fence" [ ("order", order_json mode) ], [ (0, "Fence") ])
    | Lock { global } ->
        Some
          ( op "Lock"
              [
                ( "var",
                  match global with
                  | Some g -> `String g
                  | None -> `Null );
              ],
            [ (0, "Lock") ] )
    | Unlock { global } ->
        Some
          ( op "Unlock"
              [
                ( "var",
                  match global with
                  | Some g -> `String g
                  | None -> `Null );
              ],
            [ (0, "Unlock") ] )
    | Skip -> None
    (* Control flow and thread spawns are handled by the structural emitter. *)
    | If _ | While _ | Do _ | Labeled _ | Threads _ -> None

let loops_of (ann : ir_node_ann) : int list =
  match ann.loop_ctx with
  | Some lc -> lc.loops
  | None -> []

let loc_json (ann : ir_node_ann) : Yojson.Safe.t =
  match ann.source_span with
  | Some s -> `List [ `Int s.start_line; `Int s.start_col ]
  | None -> `Null

let events_json (events : (int * string) list) : Yojson.Safe.t =
  `List
    (List.map
       (fun (k, t) -> `Assoc [ ("k", `Int k); ("type", `String t) ])
       events
    )

(** Assemble one instruction object. *)
let instr_obj (label : string) (ann : ir_node_ann) (loops : int list)
    (command : Yojson.Safe.t) (events : (int * string) list) : Yojson.Safe.t =
  `Assoc
    [
      ("label", `String label);
      ("loc", loc_json ann);
      ("loops", `List (List.map (fun i -> `Int i) loops));
      ("command", command);
      ("events", events_json events);
    ]

(** Record an instruction in the span → info table used to render event-labels
    in [futures]. Keyed by [(start_line, start_col)] of the source span. *)
let record (tbl : (int * int, instr_info) Hashtbl.t) (ann : ir_node_ann)
    (label : string) (events : (int * string) list) (loops : int list) : unit =
  match ann.source_span with
  | Some s ->
      Hashtbl.replace tbl (s.start_line, s.start_col) { label; events; loops }
  | None -> ()

(** Emit a single IR node (and any nested control flow), bumping the per-thread
    [seq] counter in pre-order and recording instructions in [tbl].

    @return the list of instruction objects produced (usually a singleton, but
            empty for [Skip] and pass-through nodes). *)
let rec emit_node ~prefix ~(seq : int ref) ~tbl (node : ir_node_ann ir_node) :
    Yojson.Safe.t list =
  let ann = node.annotations in
  let next_label () =
    incr seq;
    Printf.sprintf "%s.%d" prefix !seq
  in
    match node.stmt with
    | Labeled { stmt = inner; _ } -> emit_node ~prefix ~seq ~tbl inner
    | Skip -> []
    | If { condition; then_body; else_body } ->
        let label = next_label () in
        let loops = loops_of ann in
        let events = [ (0, "Branch") ] in
          record tbl ann label events loops;
          let then_j =
            List.concat_map (emit_node ~prefix ~seq ~tbl) then_body
          in
          let else_j =
            match else_body with
            | Some b -> List.concat_map (emit_node ~prefix ~seq ~tbl) b
            | None -> []
          in
          let command =
            `Assoc
              [
                ("op", `String "If");
                ("cond", expr_json condition);
                ("then", `List then_j);
                ("else", `List else_j);
              ]
          in
            [ instr_obj label ann loops command events ]
    | While { condition; body } ->
        let label = next_label () in
        let loops = loops_of ann in
        let events = [ (0, "Branch") ] in
          record tbl ann label events loops;
          let body_j = List.concat_map (emit_node ~prefix ~seq ~tbl) body in
          let loop_id =
            match ann.loop_ctx with
            | Some lc -> lc.lid
            | None -> -1
          in
          let command =
            `Assoc
              [
                ("op", `String "While");
                ("cond", expr_json condition);
                ("body", `List body_j);
                ("loop_id", `Int loop_id);
              ]
          in
            [ instr_obj label ann loops command events ]
    | Do { body; condition } ->
        let label = next_label () in
        let loops = loops_of ann in
        let events = [ (0, "Branch") ] in
          record tbl ann label events loops;
          let body_j = List.concat_map (emit_node ~prefix ~seq ~tbl) body in
          let loop_id =
            match ann.loop_ctx with
            | Some lc -> lc.lid
            | None -> -1
          in
          let command =
            `Assoc
              [
                ("op", `String "Do");
                ("cond", expr_json condition);
                ("body", `List body_j);
                ("loop_id", `Int loop_id);
              ]
          in
            [ instr_obj label ann loops command events ]
    | stmt -> (
        match command_and_events stmt with
        | None -> []
        | Some (command, events) ->
            let label = next_label () in
            let loops = loops_of ann in
              record tbl ann label events loops;
              [ instr_obj label ann loops command events ]
      )

(** Split the top-level program into [init] setup nodes and the thread blocks,
    emitting both. Top-level non-[Threads] nodes are init; the [Threads] node's
    thread bodies become [threads] (tid = list index). *)
let emit_program ~tbl (program : ir_node_ann ir_node list) :
    Yojson.Safe.t * Yojson.Safe.t =
  let init_seq = ref 0 in
  let init_acc = ref [] in
  let thread_blocks = ref [] in
    List.iter
      (fun (node : ir_node_ann ir_node) ->
        match node.stmt with
        | Threads { threads } -> thread_blocks := !thread_blocks @ threads
        | _ ->
            init_acc :=
              !init_acc @ emit_node ~prefix:"g" ~seq:init_seq ~tbl node
      )
      program;
    let threads_json =
      List.mapi
        (fun tid body ->
          let seq = ref 0 in
          let prefix = Printf.sprintf "t%d" tid in
          let body_json =
            List.concat_map (emit_node ~prefix ~seq ~tbl) body
          in
            `Assoc [ ("tid", `Int tid); ("body", `List body_json) ]
        )
        !thread_blocks
    in
      (`List !init_acc, `List threads_json)

(** Iteration suffix ["@<loop-id>:<iter>..."] for an event inside loops.
    Zips the instruction's loop ids with the event's per-loop iteration
    counts (best-effort; not exercised by the loop-free UAF fixture). *)
let iter_suffix (loops : int list) (iters : int list) : string =
  let n = min (List.length loops) (List.length iters) in
  let rec take k = function
    | x :: xs when k > 0 -> x :: take (k - 1) xs
    | _ -> []
  in
  let loops = take n loops and iters = take n iters in
    String.concat ""
      (List.map2 (fun lid it -> Printf.sprintf "@%d:%d" lid it) loops iters)

(** Build a map from runtime event id to its event-label, using the per-event
    source spans and loop iterations recorded during interpretation.

    Events are grouped by [(span, iteration)] — i.e. one instruction in one
    loop iteration — sorted by id, and assigned [k] by position (so an RMW's
    [R;Branch;W] sub-events, created in that order, get [#0;#1;#2]). Events
    without a recorded span (init/terminal markers, §4) are left unmapped and
    their edges are dropped. *)
let build_event_labels (ctx : mordor_ctx)
    (tbl : (int * int, instr_info) Hashtbl.t) : (int, string) Hashtbl.t =
  let evlabels = Hashtbl.create 64 in
    match (ctx.structure, ctx.source_spans) with
    | Some structure, Some spans ->
        let groups : ((int * int) * int list, int list) Hashtbl.t =
          Hashtbl.create 64
        in
          Hashtbl.iter
            (fun (eid : int) (span : source_span) ->
              let key = (span.start_line, span.start_col) in
                if Hashtbl.mem tbl key then begin
                  let iters =
                    match Hashtbl.find_opt structure.loop_indices eid with
                    | Some l -> l
                    | None -> []
                  in
                  let gk = (key, iters) in
                  let cur =
                    match Hashtbl.find_opt groups gk with
                    | Some l -> l
                    | None -> []
                  in
                    Hashtbl.replace groups gk (eid :: cur)
                end
            )
            spans;
          Hashtbl.iter
            (fun ((key, iters) : (int * int) * int list) (eids : int list) ->
              let info = Hashtbl.find tbl key in
              let sorted = List.sort compare eids in
              let suffix = iter_suffix info.loops iters in
                List.iteri
                  (fun k eid ->
                    Hashtbl.replace evlabels eid
                      (Printf.sprintf "%s%s#%d" info.label suffix k)
                  )
                  sorted
            )
            groups;
          evlabels
    | _ -> evlabels

(** Render the [futures] array: one entry per execution, its [(ppo ∪ dp)]
    edges (restricted to the execution's events, identity omitted) rendered
    over event-labels. Edges touching an unmapped event are dropped. *)
let futures_json (ctx : mordor_ctx) (evlabels : (int, string) Hashtbl.t) :
    Yojson.Safe.t =
  match ctx.executions with
  | None -> `List []
  | Some execs ->
      let exec_list =
        Uset.USet.values execs
        |> List.sort (fun (a : symbolic_execution) b -> compare a.id b.id)
      in
      let entry (exec : symbolic_execution) : Yojson.Safe.t =
        let rel = Uset.USet.union exec.dp exec.ppo in
        let edges =
          Uset.USet.values rel
          |> List.filter_map (fun (a, b) ->
              if
                a = b
                || (not (Uset.USet.mem exec.e a))
                || not (Uset.USet.mem exec.e b)
              then None
              else
                match
                  (Hashtbl.find_opt evlabels a, Hashtbl.find_opt evlabels b)
                with
                | Some la, Some lb -> Some (la, lb)
                | _ -> None
          )
          |> List.sort_uniq compare
        in
          `Assoc
            [
              ("execution", `Int exec.id);
              ( "edges",
                `List
                  (List.map
                     (fun (a, b) -> `List [ `String a; `String b ])
                     edges
                  )
              );
            ]
      in
        `List (List.map entry exec_list)

(** Build the complete interchange document for the current context. *)
let build_document (ctx : mordor_ctx) : Yojson.Safe.t =
  let program =
    match ctx.program_stmts with
    | Some p -> p
    | None -> []
  in
  let tbl : (int * int, instr_info) Hashtbl.t = Hashtbl.create 64 in
  let init_json, threads_json = emit_program ~tbl program in
  let evlabels = build_event_labels ctx tbl in
  let futures = futures_json ctx evlabels in
    `Assoc
      [
        ("format_version", `String format_version);
        ("program", `String ctx.litmus_name);
        ("orders", `List (List.map (fun s -> `String s) orders));
        ("init", init_json);
        ("threads", threads_json);
        ("futures", futures);
      ]

(** Serialise the document to a pretty-printed JSON string. *)
let to_string (ctx : mordor_ctx) : string =
  Yojson.Safe.pretty_to_string (build_document ctx)

(** Write the interchange document to the context's configured output
    (["stdout"] or a file path), recording it in [ctx.output]. *)
let emit (ctx : mordor_ctx) : unit =
  let content = to_string ctx in
    ctx.output <- Some content;
    match ctx.output_file with
    | "stdout" ->
        print_string content;
        print_newline ();
        flush stdout
    | path ->
        let oc = open_out path in
          output_string oc content;
          close_out oc;
          Logs_safe.info (fun m -> m "Isabelle interchange JSON written to %s" path)
