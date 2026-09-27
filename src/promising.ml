(** {1 Promising Semantics}

    The executions of a litmus program under the promising semantics, version
    1.0 (Kang, Hur, Lahav, Vafeiadis and Dreyer, {i A Promising Semantics for
    Relaxed-Memory Concurrency}, POPL 2017) or version 2.0 (Lee, Cho, Podkopaev,
    Chakraborty, Hur, Lahav and Vafeiadis, {i Promising 2.0: Global
    Optimizations in Relaxed Memory Concurrency}, PLDI 2020).

    Promising semantics is operational, so this module does not go through
    justifications and dependencies as sMRD does. It explores the program's
    machine states explicitly: a memory of messages, each occupying a timestamp
    interval [(from, to]] of its location and carrying a message view; per
    thread a register file and the views [cur], [acq] and [rel]; the global SC
    view; and each thread's outstanding promises. Every final state the
    exploration reaches is one outcome, and each distinct outcome becomes one
    {!Types.symbolic_execution} whose [final_env] holds the concrete final value
    of every register and of every memory location. That is the field
    {!Assertion} evaluates [allow]/[forbid] conditions over, so
    {!step_calculate_executions} can stand in the pipeline where
    [Elaborations.step_generate_justifications] and
    [Executions.step_calculate_dependencies] do.

    {2 The two versions}

    A thread may promise a write before it is reached in program order, and
    other threads may read the promise. After every step of a thread with
    outstanding promises the thread has to be {i consistent}: running alone it
    can fulfil all of them. The versions differ in what "alone" means.

    - {b PS1.0} certifies against every future memory: whatever messages the
      other threads might still add.
    - {b PS2.0} certifies against one memory, the {i capped} memory: every gap
      between adjacent messages reserved, so that nothing can be written into
      it and no update can read the message before it; and a cap message after
      each location's last message, carrying that message's value and the
      maximal view. A thread may also reserve the slot after a message
      ({i reserve}) and give it back ({i cancel}), so that an update reading an
      older message can certify a promise.

    PS1.0's quantification is computed through the PLDI 2020 paper's Remark 2:
    it is equivalent to certifying against every capped memory whose cap
    messages hold arbitrary values. The values range over a finite domain --
    those in memory, in the certifying thread's registers and code, 0 and 1,
    and one value none of those is -- which the program cannot tell apart from
    the rest. It is certification against every assignment of those values to
    the locations in memory, and so costs that many certifications.

    {2 Scope}

    What is modelled and what is not, beyond the two papers' own restrictions:

    - Views are single timemaps. PS keeps separate plain and relaxed views for
      non-atomic accesses; here non-atomic, [Normal] and [Strong] accesses are
      relaxed ones. PS2.0's non-atomic "undefined value" semantics is not
      modelled.
    - SC accesses, which neither paper has, are acquire reads and release
      writes. SC fences are as in the papers.
    - A promise carries the view [rel(x) ⊔ {x ↦ t}] and is fulfilled by a
      relaxed write whose message view is no larger. A thread cannot perform a
      release write to [x] while it has promises on [x], nor a release, acq-rel
      or SC fence while it has any. Promises are never split or lowered; their
      values are restricted to those the thread can write when running alone,
      which certification requires anyway.
    - Timestamps are rationals. A fresh write is placed in the middle of a gap,
      never attached to its predecessor, which only ever leaves more behaviour
      open; an update is attached to the message it reads. States are compared
      up to the order of timestamps per location.
    - Loops are bounded as the step-counter interpreter bounds them: at most
      [step_counter] iterations per loop, or a shared budget per thread under
      the global step counter. Symbolic loop semantics is not supported.
    - [free] and allocation only name fresh locations: promising semantics has
      no use-after-free. A dereference of something that is not an address, or
      a division by zero, aborts the run, as PS2.0's [abort] does (section
      4.3), if the thread is promise-consistent -- its view below each of its
      outstanding promises -- and is discarded, with a warning, if not. An
      aborted run becomes an execution with [aborted] set: {!Assertion}
      reports it as undefined behaviour, and it witnesses no outcome, having no
      final state. PS2.0 lets an abort certify promises, as it stands for any
      behaviour; a thread that can abort may then promise any value of the
      finite domain PS1.0's caps use, to any location it stores to, and never
      more promises than it has writes left. PS1.0 defines no undefined
      behaviour, so there an abort is reported but certifies nothing.
    - An execution is an outcome. When an assertion asks about [.rf], [.co],
      [.rmw] or [.po], it is also the event graph behind it, in the labels of
      the event structure {!Interpret} built (see {!tracker}): [rf] which
      message each read took -- a read of an initial value has no edge, as
      under sMRD -- and [co] the order of timestamps per location. [.dp] and
      [.ppo] are sMRD's and are refused, as is a refinement chain; header
      constraints on symbolic values are ignored with a warning.
    - Nested parallel composition is supported when a thread consists of
      nothing but the nested block, which is then flattened into its parent's
      threads; and at the top level, where the forking thread waits for the
      threads it forked. Registers are joined back in thread order, a later
      thread's assignment winning.

    The exploration is exhaustive and exact within these bounds, and it is
    exponential: it is meant for litmus-sized programs. *)

open Context
open Types
open Uset

(** The promising semantics to compute. *)
type version = PS1 | PS2

let show_version = function
  | PS1 -> "PS1.0"
  | PS2 -> "PS2.0"

(** A program this module cannot interpret, with the reason. *)
exception Unsupported of string

let unsupported fmt = Printf.ksprintf (fun s -> raise (Unsupported s)) fmt

(** Raised by a step with undefined behaviour -- a dereference of something
    that is not an address, a division by zero. The thread aborts there: see
    {!Abort}. *)
exception Stuck of string

(** How many aborts were discarded, and on what, for the log: those of a thread
    that could not abort, not being promise-consistent. *)
let stuck_paths : (string, int) Hashtbl.t = Hashtbl.create 4

let stuck fmt = Printf.ksprintf (fun s -> raise (Stuck s)) fmt

let note_stuck what =
  Hashtbl.replace stuck_paths what
    (1 + Option.value (Hashtbl.find_opt stuck_paths what) ~default:0)

(** {1 Values, Locations and Views} *)

(** A concrete value: an integer, or an address -- a base location and an
    offset into it. [&x] is [Ptr ("x", 0)]. *)
module Val = struct
  type t = Int of Z.t | Ptr of string * Z.t

  let zero = Int Z.zero
  let of_bool b = Int (if b then Z.one else Z.zero)

  let truthy = function
    | Int z -> not (Z.equal z Z.zero)
    | Ptr _ -> true

  let equal a b =
    match (a, b) with
    | Int x, Int y -> Z.equal x y
    | Ptr (g, o), Ptr (h, p) -> String.equal g h && Z.equal o p
    | _ -> false

  let to_string = function
    | Int z -> Z.to_string z
    | Ptr (g, o) when Z.equal o Z.zero -> "&" ^ g
    | Ptr (g, o) -> Printf.sprintf "&%s+%s" g (Z.to_string o)

  (** The value as the expression {!Assertion} compares: an integer, or the
      address in the form the parser gives [&x]. *)
  let to_expr = function
    | Int z -> ENum z
    | Ptr (g, o) when Z.equal o Z.zero -> EVar g
    | Ptr (g, o) -> EBinOp (EVar g, "+", ENum o)
end

(** A memory location: a base and an offset. A global [x] is [("x", 0)]. *)
module Loc = struct
  type t = string * Z.t

  let compare (g, o) (h, p) =
    let c = String.compare g h in
      if c <> 0 then c else Z.compare o p

  let to_string (g, o) =
    if Z.equal o Z.zero then g else Printf.sprintf "%s[%s]" g (Z.to_string o)

  let of_value = function
    | Val.Ptr (g, o) -> (g, o)
    | Val.Int z -> stuck "a dereference of the integer %s" (Z.to_string z)
end

module LocMap = Map.Make (Loc)
module SMap = Map.Make (String)

(** A view: a timestamp per location, [0] where absent. Zero entries are never
    stored, so equal views have equal bindings. *)
module View = struct
  type t = Q.t LocMap.t

  let bot : t = LocMap.empty
  let get (v : t) l = Option.value (LocMap.find_opt l v) ~default:Q.zero
  let single l t : t = if Q.equal t Q.zero then bot else LocMap.singleton l t
  let join (a : t) (b : t) : t = LocMap.union (fun _ x y -> Some (Q.max x y)) a b
  let le (a : t) (b : t) = LocMap.for_all (fun l t -> Q.leq t (get b l)) a
end

(** {1 Expressions} *)

(** Registers are [r] followed by at least one alphanumeric, as the lexer reads
    them; any other variable in an expression is a global, standing for its
    address. *)
let is_register v = String.length v > 1 && v.[0] = 'r'

let rec eval regs (e : expr) : Val.t =
  match e with
  | ENum z -> Val.Int z
  | EBoolean b -> Val.of_bool b
  | EVar v when is_register v ->
      (* An unassigned register reads as 0, as a C local initialised to 0. *)
      Option.value (SMap.find_opt v regs) ~default:Val.zero
  | EVar v when String.length v > 0 && v.[0] = '.' ->
      unsupported "the relation %s in a program expression" v
  | EVar g -> Val.Ptr (g, Z.zero)
  | ESymbol s -> unsupported "the symbol %s in a program expression" s
  | EUnOp ("!", e) -> Val.of_bool (not (Val.truthy (eval regs e)))
  | EUnOp ("-", e) -> (
      match eval regs e with
      | Val.Int z -> Val.Int (Z.neg z)
      | v -> unsupported "negation of %s" (Val.to_string v)
    )
  | EUnOp (op, _) -> unsupported "the unary operator %s" op
  | EOr es -> Val.of_bool (List.exists (fun e -> Val.truthy (eval regs e)) es)
  | EBinOp (l, "&&", r) ->
      Val.of_bool (Val.truthy (eval regs l) && Val.truthy (eval regs r))
  | EBinOp (l, "||", r) ->
      Val.of_bool (Val.truthy (eval regs l) || Val.truthy (eval regs r))
  | EBinOp (l, op, r) -> binop op (eval regs l) (eval regs r)

and binop op a b =
  let open Val in
  let cmp f x y = of_bool (f (Z.compare x y) 0) in
    match (op, a, b) with
    | "+", Int x, Int y -> Int (Z.add x y)
    | "+", Ptr (g, o), Int y | "+", Int y, Ptr (g, o) -> Ptr (g, Z.add o y)
    | "-", Int x, Int y -> Int (Z.sub x y)
    | "-", Ptr (g, o), Int y -> Ptr (g, Z.sub o y)
    | "-", Ptr (g, o), Ptr (h, p) when String.equal g h -> Int (Z.sub o p)
    | "*", Int x, Int y -> Int (Z.mul x y)
    | "/", Int x, Int y when not (Z.equal y Z.zero) -> Int (Z.div x y)
    | "%", Int x, Int y when not (Z.equal y Z.zero) -> Int (Z.rem x y)
    | ("/" | "%"), Int _, Int _ -> stuck "a division by zero"
    | "&", Int x, Int y -> Int (Z.logand x y)
    | "|", Int x, Int y -> Int (Z.logor x y)
    | "^", Int x, Int y -> Int (Z.logxor x y)
    | "<<", Int x, Int y -> Int (Z.shift_left x (Z.to_int y))
    | ">>", Int x, Int y -> Int (Z.shift_right x (Z.to_int y))
    | "=", _, _ -> of_bool (equal a b)
    | "!=", _, _ -> of_bool (not (equal a b))
    | "<", Int x, Int y -> cmp ( < ) x y
    | ">", Int x, Int y -> cmp ( > ) x y
    | "<=", Int x, Int y -> cmp ( <= ) x y
    | ">=", Int x, Int y -> cmp ( >= ) x y
    | ("<" | ">" | "<=" | ">="), Ptr (g, o), Ptr (h, p) when String.equal g h
      ->
        binop op (Int o) (Int p)
    | "=>", _, _ -> of_bool ((not (truthy a)) || truthy b)
    | _ ->
        unsupported "the operator %s on %s and %s" op (to_string a)
          (to_string b)

(** {1 Memory} *)

(** Which write event of the event structure a message is: known for a write,
    pending for a promise until it is fulfilled. Only recorded when the
    relations are tracked (see {!tracker}). *)
type src = Label of int | Pending of string

type kind =
  | Msg  (** A message: a write, or a fulfilled promise. *)
  | Promise of int  (** A thread's outstanding promise. *)
  | Reserve of int
      (** PS2.0: a thread's reservation of the timestamps after a message. The
          capped memory's own reservations belong to thread [-1]. *)

type cell = {
  from : Q.t;
  to_ : Q.t;
  value : Val.t;  (** Meaningless for a reservation. *)
  view : View.t;  (** The message view. *)
  kind : kind;
  src : src option;  (** The write this message is, when tracked. *)
}

(** A location's cells, in timestamp order, or [dflt] for a location nothing
    has been written to. [dflt] is the initialisation message, and in capped
    memory its cap too. *)
type memory = {
  locs : cell list LocMap.t;
  dflt : cell list;
  resolved : (string * int) list;
      (** The write event each fulfilled promise turned out to be, sorted:
          what a read of the promise read from. *)
}

let init_cell =
  {
    from = Q.zero;
    to_ = Q.zero;
    value = Val.zero;
    view = View.bot;
    kind = Msg;
    src = None;
  }

let empty_memory = { locs = LocMap.empty; dflt = [ init_cell ]; resolved = [] }

let cells mem l =
  Option.value (LocMap.find_opt l mem.locs) ~default:mem.dflt

let by_ts a b = Q.compare a.to_ b.to_

let insert mem l c =
  { mem with locs = LocMap.add l (List.sort by_ts (c :: cells mem l)) mem.locs }

(** [replace mem l old c] puts [c] in the place of [old]; a location's cells
    have distinct [to_]. *)
let replace mem l old c =
  {
    mem with
    locs =
      LocMap.add l
        (List.map (fun d -> if Q.equal d.to_ old.to_ then c else d) (cells mem l))
        mem.locs;
  }

let remove mem l old =
  {
    mem with
    locs =
      LocMap.add l
        (List.filter (fun d -> not (Q.equal d.to_ old.to_)) (cells mem l))
        mem.locs;
  }

(** A thread may read a message, and another thread's promise -- that is the
    point of promises -- but not its own promise, whose timestamp it could then
    never fulfil at, nor a reservation. *)
let readable_by tid c =
  match c.kind with
  | Msg -> true
  | Promise t -> t <> tid
  | Reserve _ -> false

let has_promises mem tid =
  LocMap.exists
    (fun _ cs -> List.exists (fun c -> c.kind = Promise tid) cs)
    mem.locs

(** The cell attached right after timestamp [t], if one is. *)
let slot cs t = List.find_opt (fun d -> Q.equal d.from t && Q.gt d.to_ t) cs

(** The end of an interval attached after [t]: halfway to the next cell. *)
let attach_to cs t =
  match List.find_opt (fun d -> Q.gt d.to_ t) cs with
  | Some n -> Q.add t (Q.div (Q.sub n.from t) (Q.of_int 2))
  | None -> Q.add t Q.one

(** The free gaps of a location lying above timestamp [b], lowest first. The
    last is unbounded. *)
let gaps cs b =
  let rec go acc = function
    | a :: (n :: _ as rest) ->
        let acc =
          if Q.lt a.to_ n.from && Q.geq a.to_ b then (a.to_, Some n.from) :: acc
          else acc
        in
          go acc rest
    | [ last ] -> (Q.max last.to_ b, None) :: acc
    | [] -> acc
  in
    List.rev (go [] cs)

(** An interval in the middle of a gap, attached to neither neighbour. *)
let place (lo, hi) =
  match hi with
  | Some h ->
      let third = Q.div (Q.sub h lo) (Q.of_int 3) in
        (Q.add lo third, Q.add lo (Q.mul third (Q.of_int 2)))
  | None -> (Q.add lo Q.one, Q.add lo (Q.of_int 2))

(** {1 Threads} *)

(** What a thread has left to run. [Iterate] is a loop under the per-loop step
    counter, with the iterations it may still make. *)
type item =
  | Stmt of ir_node
  | Iterate of { condition : expr; body : ir_node list; left : int }

(** How loops are bounded: per loop, or by a budget each thread spends. *)
type loops = PerLoop of int | Global

type thread = {
  name : string;  (** Names the locations the thread allocates. *)
  code : item list;
  regs : Val.t SMap.t;
  written : string list;
      (** The registers this thread assigned, sorted: what it contributes when
          joined back into the thread that forked it. *)
  cur : View.t;
  acq : View.t;
  rel_all : View.t;  (** The release view of every location ... *)
  rel : View.t LocMap.t;  (** ... joined with this, per location. *)
  budget : int;  (** Loop iterations left under the global step counter. *)
  allocs : int;
  (* What {!tracker} records, when the relations are tracked; constant
     otherwise. *)
  last : int option;  (** The event this thread's last access was. *)
  binds : (string * expr) list;
      (** The value each symbol of a read so far took, sorted: what decides
          which branch's copy of an event a later access is. *)
  rf_log : (src * int) list;  (** Each read, with what it read from. *)
  rmw_log : (int * int) list;  (** Each update, its read and its write. *)
  mapped : int list;  (** Every event an access was, sorted. *)
  promised : int;  (** Promises made, to name the next one. *)
}

let rel_of th l =
  match LocMap.find_opt l th.rel with
  | Some v -> View.join th.rel_all v
  | None -> th.rel_all

let set_reg th r v =
  {
    th with
    regs = SMap.add r v th.regs;
    written =
      (if List.mem r th.written then th.written
       else List.sort String.compare (r :: th.written));
  }

let stmts nodes = List.map (fun n -> Stmt n) nodes

let is_acq = function
  | Acquire | ReleaseAcquire | SC | Consume -> true
  | _ -> false

let is_rel = function
  | Release | ReleaseAcquire | SC -> true
  | _ -> false

let fresh_alloc th =
  let base = Printf.sprintf "alloc.%s.%d" th.name th.allocs in
    ({ th with allocs = th.allocs + 1 }, Val.Ptr (base, Z.zero))

(** [normalize ~loops th] runs [th]'s thread-local statements -- register
    assignments, branches, loop unrolling, allocation into a register -- up to
    its next memory access. They commute with every other thread's steps, so
    running them eagerly loses no behaviour and saves interleavings. *)
let rec normalize ~loops th =
  match th.code with
  | [] -> th
  | Iterate { condition; body; left } :: rest ->
      if left > 0 && Val.truthy (eval th.regs condition) then
        normalize ~loops
          {
            th with
            code =
              stmts body @ (Iterate { condition; body; left = left - 1 } :: rest);
          }
      else normalize ~loops { th with code = rest }
  | Stmt node :: rest -> (
      let next = { th with code = rest } in
        match node.Ir.stmt with
        | Ir.Skip | Ir.Free _ -> normalize ~loops next
        | Ir.Labeled { stmt; _ } ->
            normalize ~loops { th with code = Stmt stmt :: rest }
        | Ir.RegisterStore { register; expr } ->
            normalize ~loops (set_reg next register (eval th.regs expr))
        | Ir.RegisterRefAssign { register; global } ->
            normalize ~loops (set_reg next register (Val.Ptr (global, Z.zero)))
        | Ir.RegMalloc { register; _ } ->
            let next, p = fresh_alloc next in
              normalize ~loops (set_reg next register p)
        | Ir.If { condition; then_body; else_body } ->
            let branch =
              if Val.truthy (eval th.regs condition) then then_body
              else Option.value else_body ~default:[]
            in
              normalize ~loops { th with code = stmts branch @ rest }
        | Ir.While { condition; body } -> (
            match loops with
            | PerLoop k ->
                normalize ~loops
                  { th with code = Iterate { condition; body; left = k } :: rest }
            | Global ->
                (* As the interpreter's global step counter: each unrolling
                   spends one, and the one that exhausts the budget ends the
                   thread there. *)
                let budget = th.budget - 1 in
                  if budget <= 0 then { th with code = []; budget }
                  else
                    let again =
                      Ir.If { condition; then_body = body @ [ node ]; else_body = None }
                    in
                      normalize ~loops
                        {
                          th with
                          budget;
                          code = Stmt { node with Ir.stmt = again } :: rest;
                        }
          )
        | Ir.Do { body; condition } -> (
            match loops with
            | PerLoop k ->
                normalize ~loops
                  {
                    th with
                    code =
                      stmts body
                      @ (Iterate { condition; body; left = k - 1 } :: rest);
                  }
            | Global ->
                let budget = th.budget - 1 in
                  if budget <= 0 then { th with code = []; budget }
                  else
                    let again =
                      Ir.If { condition; then_body = [ node ]; else_body = None }
                    in
                      normalize ~loops
                        {
                          th with
                          budget;
                          code =
                            stmts body @ (Stmt { node with Ir.stmt = again } :: rest);
                        }
          )
        | _ -> th
    )

(** [locations ~stores th mem] are the locations [th]'s remaining updates --
    and with [stores], its stores too -- could address. An address the
    registers do not determine yet -- a pointer loaded later -- could be any
    location [mem] has. *)
let locations ~stores th mem =
  let unknown = ref false in
  (* The references the rest of the code takes, [r := &x]: an address held in
     such a register is known before the assignment is reached. *)
  let rec refs acc nodes = List.fold_left ref_of acc nodes
  and ref_of acc (node : ir_node) =
    match node.Ir.stmt with
    | Ir.RegisterRefAssign { register; global } ->
        SMap.add register (Val.Ptr (global, Z.zero)) acc
    | Ir.If { then_body; else_body; _ } ->
        refs (refs acc then_body) (Option.value else_body ~default:[])
    | Ir.While { body; _ } | Ir.Do { body; _ } -> refs acc body
    | Ir.Labeled { stmt; _ } -> ref_of acc stmt
    | _ -> acc
  in
  let ahead =
    List.fold_left
      (fun acc -> function
        | Stmt n -> ref_of acc n
        | Iterate { body; _ } -> refs acc body
        )
      th.regs th.code
  in
  let rec of_nodes acc nodes = List.fold_left of_node acc nodes
  and of_node acc (node : ir_node) =
    let addr e =
      let resolve regs =
        match eval regs e with
        | Val.Ptr (g, o) -> Some (g, o)
        | Val.Int _ | (exception Unsupported _) | (exception Stuck _) -> None
      in
        match (resolve th.regs, resolve ahead) with
        | None, None ->
            unknown := true;
            acc
        | a, b -> List.filter_map Fun.id [ a; b ] @ acc
    in
      match node.Ir.stmt with
      | Ir.Cas { address; _ } | Ir.Fadd { address; _ } -> addr address
      | Ir.Lock { global } -> (Option.value global ~default:"lock", Z.zero) :: acc
      | (Ir.GlobalStore { global; _ } | Ir.GlobalMalloc { global; _ }) when stores
        ->
          (global, Z.zero) :: acc
      | Ir.DerefStore { address; _ } when stores -> addr address
      | Ir.Unlock { global } when stores ->
          (Option.value global ~default:"lock", Z.zero) :: acc
      | Ir.If { then_body; else_body; _ } ->
          of_nodes (of_nodes acc then_body) (Option.value else_body ~default:[])
      | Ir.While { body; _ } | Ir.Do { body; _ } -> of_nodes acc body
      | Ir.Labeled { stmt; _ } -> of_node acc stmt
      | _ -> acc
  in
  let known =
    List.fold_left
      (fun acc -> function
        | Stmt n -> of_node acc n
        | Iterate { body; _ } -> of_nodes acc body
        )
      [] th.code
  in
  let all = if !unknown then List.map fst (LocMap.bindings mem.locs) else [] in
    List.sort_uniq Loc.compare (known @ all)

(** Where a PS2.0 reservation can be of use. *)
let rmw_locations = locations ~stores:false

(** [max_writes ~loops th] bounds the writes [th] can still make, along any
    path, counting each loop at its bound. A run that finishes fulfils each of
    its promises by a write of its own, so a thread never needs more
    outstanding promises than this -- which, when an abort certifies them all,
    is the only bound there is. *)
let max_writes ~loops th =
  let rec of_nodes nodes = List.fold_left (fun n node -> n + of_node node) 0 nodes
  and of_node (node : ir_node) =
    match node.Ir.stmt with
    | Ir.GlobalStore _ | Ir.DerefStore _ | Ir.GlobalMalloc _ | Ir.Cas _
    | Ir.Fadd _ | Ir.Lock _ | Ir.Unlock _ ->
        1
    | Ir.If { then_body; else_body; _ } ->
        max (of_nodes then_body) (of_nodes (Option.value else_body ~default:[]))
    | Ir.While { body; _ } | Ir.Do { body; _ } ->
        let bound =
          match loops with
          | PerLoop k -> k
          | Global -> th.budget
        in
          bound * of_nodes body
    | Ir.Labeled { stmt; _ } -> of_node stmt
    | Ir.Threads { threads } -> List.fold_left (fun n t -> n + of_nodes t) 0 threads
    | _ -> 0
  in
    List.fold_left
      (fun n -> function
        | Stmt node -> n + of_node node
        | Iterate { body; left; _ } -> n + (left * of_nodes body)
        )
      0 th.code

let own_promises_of cs tid = List.filter (fun c -> c.kind = Promise tid) cs

let promise_count mem tid =
  LocMap.fold
    (fun _ cs n -> n + List.length (own_promises_of cs tid))
    mem.locs 0

(** {1 Tracking the Relations}

    An assertion asks about [.rf] and [.co] in the labels of the event
    structure {!Interpret} built, so each access a run makes has to be named by
    its event. A statement is several events -- one per branch it follows and
    per loop iteration it is in -- that share its source span, and each event
    carries its path condition over the symbols of the reads before it. In
    program order, then, an access is the event of its span, after the
    thread's last one, whose path condition the values the thread has read so
    far satisfy. The earliest such is the one.

    Tracking puts which message a read took into the state, so fewer states
    merge; it is only switched on when an assertion asks about a relation. *)

type tracker = {
  structure : symbolic_event_structure;
  by_span : (source_span, int list) Hashtbl.t;
  sat : (string, bool) Hashtbl.t;  (** Path conditions, as decided. *)
}

let make_tracker (structure : symbolic_event_structure) spans =
  let by_span = Hashtbl.create 64 in
    Hashtbl.iter
      (fun l span ->
        Hashtbl.replace by_span span
          (l :: Option.value (Hashtbl.find_opt by_span span) ~default:[])
      )
      spans;
    { structure; by_span; sat = Hashtbl.create 64 }

(** Whether [phi] holds with the symbols [binds] gives values to. A symbol it
    does not is left free. *)
let path_holds tr binds phi =
  let env s = List.assoc_opt s binds in
  let phi = List.map (Expr.Expr.evaluate ~env) phi in
    if List.mem (EBoolean false) phi then false
    else
      match List.filter (fun e -> e <> EBoolean true) phi with
      | [] -> true
      | phi -> (
          let k = String.concat " ; " (List.map Expr.Expr.to_string phi) in
            match Hashtbl.find_opt tr.sat k with
            | Some b -> b
            | None ->
                let b = Solver.is_sat phi in
                  Hashtbl.replace tr.sat k b;
                  b
        )

let show_span = function
  | Some (sp : source_span) ->
      Printf.sprintf "line %d, column %d" sp.start_line sp.start_col
  | None -> "an unknown position"

(** The event of type [typ] an access at [span] is, for thread [th]. *)
let event_of tr ~typ span th =
  let po = tr.structure.po in
  let candidates =
    Option.bind span (Hashtbl.find_opt tr.by_span)
    |> Option.value ~default:[]
    |> List.filter (fun l ->
        (Hashtbl.find tr.structure.events l).typ = typ
        && ( match th.last with
           | None -> true
           | Some p -> USet.mem po (p, l)
           )
        && path_holds tr th.binds
             (Option.value (Hashtbl.find_opt tr.structure.restrict l) ~default:[])
    )
  in
  let earliest =
    List.filter
      (fun l -> not (List.exists (fun l' -> l' <> l && USet.mem po (l', l)) candidates))
      candidates
  in
    match earliest with
    | [ l ] -> l
    | [] ->
        unsupported "naming the %s at %s by an event of the event structure"
          (show_event_type typ) (show_span span)
    | _ ->
        unsupported
          "naming the %s at %s by one event: the values read so far leave %s \
           open"
          (show_event_type typ) (show_span span)
          (String.concat ", " (List.map string_of_int earliest))

(** [th] after the read at [at] took [c], with value [v]. *)
let track_read at th c v =
  match at with
  | None -> (th, None)
  | Some (tr, span) ->
      let l = event_of tr ~typ:Read span th in
      let binds =
        match (Hashtbl.find tr.structure.events l).rval with
        | Some (VSymbol s) ->
            List.sort compare ((s, Val.to_expr v) :: List.remove_assoc s th.binds)
        | _ -> th.binds
      in
      let rf_log =
        match c.src with
        | Some src -> List.sort compare ((src, l) :: th.rf_log)
        | None -> th.rf_log
      in
        ( {
            th with
            last = Some l;
            binds;
            rf_log;
            mapped = List.sort compare (l :: th.mapped);
          },
          Some l )

(** [th] after the write at [at], and the message's provenance. *)
let track_write at th =
  match at with
  | None -> (th, None)
  | Some (tr, span) ->
      let l = event_of tr ~typ:Write span th in
        ({ th with last = Some l; mapped = List.sort compare (l :: th.mapped) }, Some l)

let label_src = Option.map (fun l -> Label l)

(** [mem] with promise [p] known to be the write [l]. *)
let resolve mem p l =
  match (p.src, l) with
  | Some (Pending id), Some l ->
      { mem with resolved = List.sort compare ((id, l) :: mem.resolved) }
  | _ -> mem

(** {1 Thread Steps} *)

(** Where a thread runs: in the real memory, or alone in a capped memory to
    certify its promises. *)
type world = Real | Capped

type config = { th : thread; mem : memory; sc : View.t }

(** A successor of a step, with the write the step made, if any. *)
type succ = (Loc.t * Val.t) option * config

(** What a thread can do next: a step, or -- on undefined behaviour -- abort,
    in the configuration it reached. *)
type move = Step of succ | Abort of string * config

(** PS2.0's condition for aborting (section 4.3): the thread's view of every
    location is below each of its outstanding promises there, so that it could
    still fulfil them -- which is all an abort, standing for any behaviour at
    all, has to be able to do. *)
let promise_consistent ~tid cfg =
  LocMap.for_all
    (fun l cs ->
      List.for_all
        (fun p -> p.kind <> Promise tid || Q.lt (View.get cfg.th.cur l) p.to_)
        cs
    )
    cfg.mem.locs

let read_view th l c mode =
  let s = View.single l c.to_ in
  let cur = View.join th.cur s in
  let cur = if is_acq mode then View.join cur c.view else cur in
  let acq = View.join (View.join th.acq s) (View.join c.view cur) in
    { th with cur; acq }

(** The thread after writing [l] at [t], and the message view of the write:
    the release view of [l], joined for an update with the view of the message
    it read -- which is what makes a release sequence. *)
let write_view th l t mode extra =
  let s = View.single l t in
  let cur = View.join th.cur s in
  let acq = View.join th.acq s in
  let relv = if is_rel mode then cur else View.join (rel_of th l) s in
    ({ th with cur; acq; rel = LocMap.add l relv th.rel }, View.join relv extra)

let own_promises cs tid = List.filter (fun c -> c.kind = Promise tid) cs

let reads ?at ~tid cfg l mode register =
  let cs = cells cfg.mem l in
  let curl = View.get cfg.th.cur l in
    List.filter_map
      (fun c ->
        if readable_by tid c && Q.geq c.to_ curl then
          let th, _ =
            track_read at (set_reg (read_view cfg.th l c mode) register c.value) c c.value
          in
            Some (None, { cfg with th })
        else None
      )
      cs

let writes ?at ~world ~tid cfg l v mode =
  let th = cfg.th in
  let cs = cells cfg.mem l in
  let curl = View.get th.cur l in
  let own = own_promises cs tid in
    if is_rel mode && own <> [] then []
    else
      let fulfil =
        List.filter_map
          (fun p ->
            if Val.equal p.value v && Q.gt p.to_ curl then
              let th', view = write_view th l p.to_ mode View.bot in
                if View.le view p.view then
                  let th', w = track_write at th' in
                    Some
                      ( Some (l, v),
                        {
                          cfg with
                          th = th';
                          mem =
                            replace (resolve cfg.mem p w) l p
                              { p with kind = Msg; view; src = label_src w };
                        }
                      )
                else None
            else None
          )
          own
      in
      (* Running alone, the lowest gap is the best: a lower timestamp leaves
         more to read and more promises to fulfil. In capped memory it is the
         only one. *)
      let candidates =
        match (world, gaps cs curl) with
        | Real, gs -> gs
        | _, g :: _ -> [ g ]
        | _, [] -> []
      in
      let fresh_writes =
        List.map
          (fun g ->
            let from, to_ = place g in
            let th', view = write_view th l to_ mode View.bot in
            let th', w = track_write at th' in
                ( Some (l, v),
                  {
                    cfg with
                    th = th';
                    mem =
                      insert cfg.mem l
                        { from; to_; value = v; view; kind = Msg; src = label_src w };
                  }
                )
          )
          candidates
      in
        fulfil @ fresh_writes

(** An update of [l]: [update] maps the value read to [Some] value to write, or
    to [None] where the update fails -- a failing CAS, which is a plain read,
    or a lock already held, which cannot step at all ([blocking]). *)
let updates ?at ~world ~tid ~blocking cfg l ~rmode ~wmode register update =
  let th = cfg.th in
  let cs = cells cfg.mem l in
  let curl = View.get th.cur l in
  let release_blocked = is_rel wmode && own_promises cs tid <> [] in
  (* The update reading [c], as it lands in the slot after [c]. *)
  let write_after cs mem c v th_r r_label =
    (* The write half of the update, named, and the pair recorded. *)
    let written th' =
      let th', w = track_write at th' in
        match (r_label, w) with
        | Some r, Some w ->
            ({ th' with rmw_log = List.sort compare ((r, w) :: th'.rmw_log) }, w |> Option.some)
        | _ -> (th', w)
    in
    match slot cs c.to_ with
    | Some p when p.kind = Promise tid ->
        if Val.equal p.value v then
          let th', view = write_view th_r l p.to_ wmode c.view in
            if View.le view p.view then
              let th', w = written th' in
                Some
                  ( th',
                    replace (resolve mem p w) l p
                      { p with kind = Msg; view; value = v; src = label_src w }
                  )
            else None
        else None
    | Some r when r.kind = Reserve tid ->
        let th', view = write_view th_r l r.to_ wmode c.view in
        let th', w = written th' in
          Some
            ( th',
              replace mem l r
                { r with kind = Msg; view; value = v; src = label_src w }
            )
    | Some _ -> None
    | None ->
        let to_ = attach_to cs c.to_ in
        let th', view = write_view th_r l to_ wmode c.view in
        let th', w = written th' in
          Some
            ( th',
              insert mem l
                { from = c.to_; to_; value = v; view; kind = Msg; src = label_src w }
            )
  in
  (* The step reading [c] from memory [mem], or [None] if it cannot be made. *)
  let step cs mem c =
    let th_r, r_label =
      track_read at (set_reg (read_view th l c rmode) register c.value) c c.value
    in
      match update c.value with
      | None when blocking -> None
      | None -> Some (None, { cfg with th = th_r; mem })
      | Some _ when release_blocked -> None
      | Some v ->
          Option.map
            (fun (th', mem') -> (Some (l, v), { cfg with th = th'; mem = mem' }))
            (write_after cs mem c v th_r r_label)
  in
    List.filter_map
      (fun c ->
        if readable_by tid c && Q.geq c.to_ curl then step cs cfg.mem c else None
      )
      cs

(** A fence. A release, acq-rel or SC fence cannot be made while the thread
    has promises: a promise made before it could not be fulfilled by a write
    the fence releases. *)
let fence ~tid cfg mode =
  let th = cfg.th in
  let acquire th = { th with cur = th.acq } in
  let release th = { th with rel_all = th.cur; rel = LocMap.empty } in
    match mode with
    | (Release | ReleaseAcquire | SC) when has_promises cfg.mem tid -> []
    | Acquire | Consume -> [ (None, { cfg with th = acquire th }) ]
    | Release -> [ (None, { cfg with th = release th }) ]
    | ReleaseAcquire -> [ (None, { cfg with th = release (acquire th) }) ]
    | SC ->
        let v = View.join th.acq cfg.sc in
          [
              ( None,
                {
                  cfg with
                  th = { th with cur = v; acq = v; rel_all = v; rel = LocMap.empty };
                  sc = v;
                }
              );
          ]
    | Relaxed | Normal | Strong | Nonatomic -> [ (None, cfg) ]

(** [program_steps ~world ~loops ~tid cfg] is every move thread [tid] can make
    by running its next memory access, each successor normalized. A fork is not
    among them; {!explore} handles it. *)
let rec program_steps ?tr ~world ~loops ~tid cfg =
  try program_steps_exn ?tr ~world ~loops ~tid cfg
  with Stuck what -> [ Abort (what, cfg) ]

and program_steps_exn ?tr ~world ~loops ~tid cfg =
  match cfg.th.code with
  | Stmt node :: rest ->
      let cfg = { cfg with th = { cfg.th with code = rest } } in
      let regs = cfg.th.regs in
      let at = Option.map (fun tr -> (tr, node.Ir.annotations.source_span)) tr in
      let succs =
        match node.Ir.stmt with
        | Ir.GlobalLoad { register; global; load } ->
            reads ?at ~tid cfg (global, Z.zero) load.mode register
        | Ir.DerefLoad { register; address; load } ->
            reads ?at ~tid cfg (Loc.of_value (eval regs address)) load.mode register
        | Ir.GlobalStore { global; expr; assign } ->
            writes ?at ~world ~tid cfg (global, Z.zero) (eval regs expr) assign.mode
        | Ir.DerefStore { address; expr; assign } ->
            writes ?at ~world ~tid cfg
              (Loc.of_value (eval regs address))
              (eval regs expr) assign.mode
        | Ir.GlobalMalloc { global; _ } ->
            let th, p = fresh_alloc cfg.th in
              writes ?at ~world ~tid { cfg with th } (global, Z.zero) p Relaxed
        | Ir.Cas { register; address; expected; desired; load_mode; assign_mode }
          ->
            let expected = eval regs expected and desired = eval regs desired in
              updates ?at ~world ~tid ~blocking:false cfg
                (Loc.of_value (eval regs address))
                ~rmode:load_mode ~wmode:assign_mode register (fun v ->
                  if Val.equal v expected then Some desired else None
              )
        | Ir.Fadd { register; address; operand; load_mode; assign_mode; _ } ->
            let operand = eval regs operand in
              updates ?at ~world ~tid ~blocking:false cfg
                (Loc.of_value (eval regs address))
                ~rmode:load_mode ~wmode:assign_mode register (fun v ->
                  Some (binop "+" v operand)
              )
        | Ir.Lock { global } ->
            (* An acquiring CAS from 0 to 1 that waits while the lock is held.
               It has no register to report into. *)
            let l = (Option.value global ~default:"lock", Z.zero) in
              updates ~world ~tid ~blocking:true cfg l ~rmode:Acquire
                ~wmode:Relaxed " lock" (fun v ->
                  if Val.equal v Val.zero then Some (Val.Int Z.one) else None
              )
              |> List.map (fun (w, c) ->
                (w, { c with th = { c.th with regs; written = cfg.th.written } })
              )
        | Ir.Unlock { global } ->
            writes ~world ~tid cfg
              (Option.value global ~default:"lock", Z.zero)
              Val.zero Release
        | Ir.Fence { mode } -> fence ~tid cfg mode
        | Ir.Threads _ -> []
        | stmt ->
            unsupported "a statement left after normalization: %s"
              (Ir.to_string ~ann_to_string:(fun _ -> "") node)
      in
      let norm (w, c) =
        match normalize ~loops c.th with
        | th -> Step (w, { c with th })
        | exception Stuck what -> Abort (what, c)
      in
        List.map norm succs
  | _ -> []

(** {1 State Keys} *)

let view_repr (v : View.t) = LocMap.bindings v

let thread_repr th =
  ( th.code,
    SMap.bindings th.regs,
    th.written,
    view_repr th.cur,
    view_repr th.acq,
    view_repr th.rel_all,
    List.map (fun (l, v) -> (l, view_repr v)) (LocMap.bindings th.rel),
    th.budget,
    th.allocs,
    (th.last, th.binds, th.rf_log, th.rmw_log, th.mapped, th.promised) )

let mem_repr mem =
  List.map
    (fun (l, cs) ->
      ( l,
        List.map
          (fun c -> (c.from, c.to_, c.value, view_repr c.view, c.kind, c.src))
          cs ))
    (LocMap.bindings mem.locs),
  mem.resolved

(** A digest identifying a state: equal states have equal digests. *)
let key repr = Digest.string (Marshal.to_string repr [ Marshal.No_sharing ])

(** {1 Certification} *)

(** The values a PS1.0 cap message may take, for [th] certifying in [mem]:
    the values in memory, in [th]'s registers and in its code, 0 and 1, and one
    value none of those is. PS1.0 quantifies over every value; the program can
    only tell apart the values it holds or mentions, so one representative of
    all the rest suffices. *)
let domain th mem =
  let values = ref [ Val.zero; Val.Int Z.one ] in
  let add v =
    if not (List.exists (Val.equal v) !values) then values := v :: !values
  in
  let rec of_expr = function
    | ENum z -> add (Val.Int z)
    | EBinOp (l, _, r) ->
        of_expr l;
        of_expr r
    | EUnOp (_, e) -> of_expr e
    | EOr es -> List.iter of_expr es
    | _ -> ()
  in
  let rec of_nodes nodes = List.iter of_node nodes
  and of_node (node : ir_node) =
    List.iter of_expr (Ir.extract_conditions_from_stmt node.Ir.stmt);
    match node.Ir.stmt with
    | Ir.RegisterStore { expr; _ }
    | Ir.GlobalStore { expr; _ }
    | Ir.DerefStore { expr; _ } ->
        of_expr expr
    | Ir.Cas { expected; desired; _ } ->
        of_expr expected;
        of_expr desired
    | Ir.Fadd { operand; _ } -> of_expr operand
    | Ir.If { then_body; else_body; _ } ->
        of_nodes then_body;
        Option.iter of_nodes else_body
    | Ir.While { body; _ } | Ir.Do { body; _ } -> of_nodes body
    | Ir.Labeled { stmt; _ } -> of_node stmt
    | _ -> ()
  in
    LocMap.iter
      (fun _ cs ->
        List.iter (fun c -> if c.kind <> Reserve (-1) then add c.value) cs
      )
      mem.locs;
    SMap.iter (fun _ v -> add v) th.regs;
    List.iter
      (function
        | Stmt n -> of_node n
        | Iterate { condition; body; _ } ->
            of_expr condition;
            of_nodes body
        )
      th.code;
    let largest =
      List.fold_left
        (fun m -> function
          | Val.Int z -> Z.max m (Z.abs z)
          | Val.Ptr _ -> m
          )
        Z.zero !values
    in
      add (Val.Int (Z.succ largest));
      List.rev !values

(** [cap ~tid ?values mem] is the capped memory thread [tid] certifies in
    (PS2.0, section 4.1): every gap between adjacent cells reserved, so an
    update can read no message but a cap; and a cap message after each
    location's last cell, carrying the value of its last concrete message and
    the maximal view -- unless that last cell is [tid]'s own reservation.
    [values] overrides the caps' values: PS1.0's certification against every
    future memory is certification against every such choice (PS2.0, Remark
    2). A location nothing was written to is capped at its initial value.
    Returns the maximal view too, which the SC view is raised to. *)
let cap ~tid ?(values = LocMap.empty) mem =
  let last cs = List.nth cs (List.length cs - 1) in
  let maxview =
    LocMap.fold
      (fun l cs v ->
        List.fold_left
          (fun v c ->
            match c.kind with
            | Reserve _ -> v
            | Msg | Promise _ -> View.join v (View.single l c.to_)
          )
          v cs
      )
      mem.locs View.bot
  in
  let capped l cs =
    let rec fill = function
      | a :: (n :: _ as rest) when Q.lt a.to_ n.from ->
          a
          :: {
               from = a.to_;
               to_ = n.from;
               kind = Reserve (-1);
               src = None;
               view = View.bot;
               value = Val.zero;
             }
          :: fill rest
      | a :: rest -> a :: fill rest
      | [] -> []
    in
    let last_value =
      List.fold_left
        (fun v c ->
          match c.kind with
          | Msg | Promise _ -> c.value
          | Reserve _ -> v
        )
        Val.zero cs
    in
    let value =
      match Option.bind l (fun l -> LocMap.find_opt l values) with
      | Some v -> v
      | None -> last_value
    in
      if (last cs).kind = Reserve tid then fill cs
      else
        let from = (last cs).to_ in
        let to_ = Q.add from Q.one in
        let view =
          match l with
          | Some l -> View.join maxview (View.single l to_)
          | None -> maxview
        in
          fill cs @ [ { from; to_; value; view; kind = Msg; src = None } ]
  in
    ( {
        locs = LocMap.mapi (fun l cs -> capped (Some l) cs) mem.locs;
        dflt = capped None [ init_cell ];
        resolved = mem.resolved;
      },
      maxview )

(** The capped memories thread [tid] certifies against from [cfg]: the one
    capped memory for PS2.0, one per choice of cap values for PS1.0. *)
let certification_starts ~version ~tid cfg =
  let start values =
    let mem, maxview = cap ~tid ~values cfg.mem in
      { cfg with mem; sc = View.join cfg.sc maxview }
  in
    match version with
    | PS2 -> [ start LocMap.empty ]
    | PS1 ->
        let dom = domain cfg.th cfg.mem in
          LocMap.fold
            (fun l _ choices ->
              List.concat_map
                (fun choice -> List.map (fun v -> LocMap.add l v choice) dom)
                choices
            )
            cfg.mem.locs [ LocMap.empty ]
          |> List.map start

let config_key cfg = key (thread_repr cfg.th, mem_repr cfg.mem, view_repr cfg.sc)

(** [consistent ~version ~loops ~tid cfg] holds when thread [tid], running
    alone from [cfg], can fulfil every promise it has outstanding in each
    memory it certifies against. *)
let consistent ~version ~loops ~tid cfg =
  if not (has_promises cfg.mem tid) then true
  else
    let memo = Hashtbl.create 64 in
    let rec certify cfg =
      if not (has_promises cfg.mem tid) then true
      else
        let k = config_key cfg in
          match Hashtbl.find_opt memo k with
          | Some b -> b
          | None ->
              let b =
                List.exists
                  (function
                    | Step (_, c) -> certify c
                    (* PS2.0 lets the certifying thread replace an abort by
                       any sequence of operations, fulfilling its promises
                       among them. PS1.0 has no undefined behaviour. *)
                    | Abort (_, c) -> version = PS2 && promise_consistent ~tid c
                    )
                  (program_steps ~world:Capped ~loops ~tid cfg)
              in
                Hashtbl.replace memo k b;
                b
    in
      List.for_all certify (certification_starts ~version ~tid cfg)

(** The writes thread [tid] could make running alone from [cfg] in a memory it
    certifies against: the only promises certification can accept.

    Under PS2.0 a reachable abort certifies every promise, as it stands for any
    behaviour at all. Then the thread may also promise any value of {!domain}
    to any location its code stores to -- the same finite stand-in for "any
    value" PS1.0's caps use. *)
let potential_writes ~version ~loops ~tid cfg =
  let seen = Hashtbl.create 64 in
  let found = ref [] in
  let aborts = ref false in
  let record = function
    | Some (l, v) ->
        if
          not
            (List.exists
               (fun (l', v') -> Loc.compare l l' = 0 && Val.equal v v')
               !found
            )
        then found := (l, v) :: !found
    | None -> ()
  in
  let rec go cfg =
    let k = config_key cfg in
      if not (Hashtbl.mem seen k) then begin
        Hashtbl.add seen k ();
        List.iter
          (function
            | Step (w, c) ->
                record w;
                go c
            | Abort _ -> aborts := true
            )
          (program_steps ~world:Capped ~loops ~tid cfg)
      end
  in
    List.iter go (certification_starts ~version ~tid cfg);
    if !aborts && version = PS2 then begin
      let values = domain cfg.th cfg.mem in
        List.iter
          (fun l -> List.iter (fun v -> record (Some (l, v))) values)
          (locations ~stores:true cfg.th cfg.mem)
    end;
    List.rev !found

(** {1 Exploration} *)

type state = {
  threads : thread array;
  memory : memory;
  sc_view : View.t;
  aborted : string option;
      (** Why a thread aborted, ending the run with undefined behaviour. *)
}

(** [canonical st] renames every timestamp to its rank among its location's
    timestamps. Only their order matters -- a gap between two distinct ones is
    always wide enough -- so states equal up to this renaming behave alike. *)
let canonical st =
  let stamps = Hashtbl.create 16 in
  let add l t =
    let s = Option.value (Hashtbl.find_opt stamps l) ~default:[ Q.zero ] in
      Hashtbl.replace stamps l (t :: s)
  in
  let add_view v = LocMap.iter add v in
    LocMap.iter
      (fun l cs -> List.iter (fun c -> add l c.from; add l c.to_; add_view c.view) cs)
      st.memory.locs;
    Array.iter
      (fun th ->
        add_view th.cur; add_view th.acq; add_view th.rel_all;
        LocMap.iter (fun _ v -> add_view v) th.rel)
      st.threads;
    add_view st.sc_view;
    let ranks = Hashtbl.create 16 in
      Hashtbl.iter
        (fun l ts ->
          let sorted = List.sort_uniq Q.compare ts in
          let tbl = Hashtbl.create 8 in
            List.iteri (fun i t -> Hashtbl.replace tbl (Q.to_string t) (Q.of_int i)) sorted;
            Hashtbl.replace ranks l tbl)
        stamps;
      let rank l t = Hashtbl.find (Hashtbl.find ranks l) (Q.to_string t) in
      let view v = LocMap.mapi rank v in
      let thread th =
        { th with cur = view th.cur; acq = view th.acq; rel_all = view th.rel_all; rel = LocMap.map view th.rel }
      in
        {
          threads = Array.map thread st.threads;
          memory =
            {
              st.memory with
              locs =
                LocMap.mapi
                  (fun l cs -> List.map (fun c -> { c with from = rank l c.from; to_ = rank l c.to_; view = view c.view }) cs)
                  st.memory.locs;
            };
          sc_view = view st.sc_view;
          aborted = st.aborted;
        }

let state_key st =
  key
    ( Array.map thread_repr st.threads,
      mem_repr st.memory,
      view_repr st.sc_view,
      st.aborted )

(** Exploration statistics, for the log. *)
type stats = {
  mutable states : int;
  mutable promises : int;
  mutable certifications : int;
  consistency : (Digest.t, bool) Hashtbl.t;
      (** {!consistent}, by thread and configuration. *)
  candidates : (Digest.t, (Loc.t * Val.t) list) Hashtbl.t;
      (** {!potential_writes}, by thread and configuration. *)
}

let memoized tbl ~tid cfg f =
  let k = key (tid, config_key cfg) in
    match Hashtbl.find_opt tbl k with
    | Some v -> v
    | None ->
        let v = f () in
          Hashtbl.replace tbl k v;
          v

(** [spawn parent i code] is the [i]th thread [parent] forks, starting from
    [parent]'s registers and views. *)
let spawn ~loops parent i code =
  normalize ~loops
    {
      parent with
      name = Printf.sprintf "%s.%d" parent.name i;
      code = stmts code;
      written = [];
      allocs = 0;
      rf_log = [];
      rmw_log = [];
      mapped = [];
      promised = 0;
    }

(** The threads a fork starts, with a thread that is nothing but a nested fork
    replaced by the threads it forks. *)
let rec fork_threads ~loops parent threads =
  List.concat
    (List.mapi
       (fun i code ->
         match code with
         | [ { Ir.stmt = Ir.Threads { threads = inner }; _ } ] ->
             fork_threads ~loops (spawn ~loops parent i []) inner
         | _ -> [ spawn ~loops parent i code ]
       )
       threads
    )

(** [join parent children] is [parent] after its children finished: their
    registers, a later child's winning, and the join of their views. *)
let join ~loops parent children =
  let joined =
    List.fold_left
      (fun p c ->
        let p =
          List.fold_left
            (fun p r -> set_reg p r (SMap.find r c.regs))
            p c.written
        in
          {
            p with
            cur = View.join p.cur c.cur;
            acq = View.join p.acq c.acq;
            rel_all = View.join p.rel_all c.rel_all;
            rel = LocMap.union (fun _ a b -> Some (View.join a b)) p.rel c.rel;
            binds = List.sort_uniq compare (p.binds @ c.binds);
            rf_log = List.sort compare (p.rf_log @ c.rf_log);
            rmw_log = List.sort compare (p.rmw_log @ c.rmw_log);
            mapped = List.sort compare (p.mapped @ c.mapped);
          }
      )
      parent children
  in
    normalize ~loops joined

(** [explore ~version ~loops ~stats threads memory sc] is every final state the
    threads can reach together: all of them finished, no promise outstanding.
    Each thread is normalized. *)
let rec explore ?tr ~version ~loops ~stats threads memory sc_view =
  let n = Array.length threads in
  let visited = Hashtbl.create 1024 in
  let finals = Hashtbl.create 16 in
  let rec dfs st =
    let st = canonical st in
    let k = state_key st in
      if not (Hashtbl.mem visited k) then begin
        Hashtbl.add visited k ();
        stats.states <- stats.states + 1;
        (* A finished thread has no promises left: the step that finished it
           had to leave it consistent. An aborted run is over. *)
        if st.aborted <> None || Array.for_all (fun th -> th.code = []) st.threads
        then
          Hashtbl.replace finals k st
        else
          for tid = 0 to n - 1 do
            List.iter dfs (successors st tid)
          done
      end
  and successors st tid =
    let th = st.threads.(tid) in
    let cfg = { th; mem = st.memory; sc = st.sc_view } in
    let rebuild ?aborted (c : config) =
      let threads = Array.copy st.threads in
        threads.(tid) <- c.th;
        { threads; memory = c.mem; sc_view = c.sc; aborted }
    in
    let admissible (c : config) =
      if has_promises c.mem tid then begin
        memoized stats.consistency ~tid c (fun () ->
            stats.certifications <- stats.certifications + 1;
            consistent ~version ~loops ~tid c
        )
      end
      else true
    in
      match th.code with
      | [] -> []
      | Stmt { Ir.stmt = Ir.Threads { threads = forked }; _ } :: rest ->
          if n > 1 then
            unsupported
              "a parallel composition nested inside a thread that runs \
               alongside others"
          else
            let parent = { th with code = rest } in
            (* The forking thread has no promises, being alone, so it can
               always abort. *)
            begin
            match Array.of_list (fork_threads ~loops parent forked) with
            | exception Stuck what -> [ rebuild ~aborted:what cfg ]
            | children ->
                List.map
                  (fun fin ->
                    let c = { th = parent; mem = fin.memory; sc = fin.sc_view } in
                      match fin.aborted with
                      | Some what -> rebuild ~aborted:what c
                      | None -> (
                          match join ~loops parent (Array.to_list fin.threads) with
                          | parent' -> rebuild { c with th = parent' }
                          | exception Stuck what -> rebuild ~aborted:what c
                        )
                  )
                  (explore ?tr ~version ~loops ~stats children st.memory st.sc_view)
            end
      | _ ->
          let steps =
            List.filter_map
              (function
                | Step (_, c) -> if admissible c then Some (rebuild c) else None
                | Abort (what, c) ->
                    if promise_consistent ~tid c then Some (rebuild ~aborted:what c)
                    else (
                      note_stuck what;
                      None
                    )
                )
              (program_steps ?tr ~world:Real ~loops ~tid cfg)
          in
          (* Alone, a thread gains nothing by promising: nobody could read the
             promise before it is fulfilled. *)
          let promises = if n > 1 then promise_steps cfg tid else [] in
          let reservations =
            if n > 1 && version = PS2 then reservation_steps cfg tid else []
          in
            steps
            @ List.filter_map
                (fun c -> if admissible c then Some (rebuild c) else None)
                (promises @ reservations)
  and promise_steps cfg tid =
    let th = cfg.th in
    let rmw = rmw_locations th cfg.mem in
    if promise_count cfg.mem tid >= max_writes ~loops th then []
    else
      List.concat_map
        (fun (l, v) ->
          let cs = cells cfg.mem l in
          let curl = View.get th.cur l in
          let with_interval (from, to_) =
            stats.promises <- stats.promises + 1;
            let view = View.join (rel_of th l) (View.single l to_) in
            let src, th =
              match tr with
              | Some _ ->
                  ( Some (Pending (Printf.sprintf "%s#%d" th.name th.promised)),
                    { th with promised = th.promised + 1 } )
              | None -> (None, th)
            in
              {
                th;
                mem =
                  insert cfg.mem l
                    { from; to_; value = v; view; kind = Promise tid; src };
                sc = cfg.sc;
              }
          in
          (* Anywhere free above what the thread has seen, and attached to a
             message it could update. *)
          let detached = List.map (fun g -> with_interval (place g)) (gaps cs curl) in
          (* An attached promise can only be fulfilled by an update; for a
             plain write the detached one in the same gap does as well. *)
          let updatable = List.exists (fun l' -> Loc.compare l l' = 0) rmw in
          let attached =
            List.filter_map
              (fun c ->
                if
                  updatable && readable_by tid c && Q.geq c.to_ curl
                  && slot cs c.to_ = None
                then
                  Some (with_interval (c.to_, attach_to cs c.to_))
                else None
              )
              cs
          in
            detached @ attached
        )
        (memoized stats.candidates ~tid cfg (fun () ->
             potential_writes ~version ~loops ~tid cfg
         )
        )
  and reservation_steps cfg tid =
    let th = cfg.th in
    let reserve =
      List.concat_map
        (fun l ->
          let cs = cells cfg.mem l in
          let curl = View.get th.cur l in
            List.filter_map
              (fun c ->
                if readable_by tid c && Q.geq c.to_ curl && slot cs c.to_ = None then
                  Some
                    {
                      cfg with
                      mem =
                        insert cfg.mem l
                          {
                            from = c.to_;
                            to_ = attach_to cs c.to_;
                            value = Val.zero;
                            view = View.bot;
                            kind = Reserve tid;
                            src = None;
                          };
                    }
                else None
              )
              cs
        )
        (rmw_locations th cfg.mem)
    in
    let cancel =
      LocMap.fold
        (fun l cs acc ->
          List.fold_left
            (fun acc c ->
              if c.kind = Reserve tid then { cfg with mem = remove cfg.mem l c } :: acc
              else acc
            )
            acc cs
        )
        cfg.mem.locs []
    in
      reserve @ cancel
  in
    dfs { threads; memory; sc_view; aborted = None };
    Hashtbl.fold (fun _ st acc -> st :: acc) finals []

(** {1 Outcomes} *)

(** The last value written to each location. *)
let final_memory mem =
  LocMap.fold
    (fun l cs acc ->
      match List.rev (List.filter (fun c -> c.kind = Msg) cs) with
      | c :: _ -> (l, c.value) :: acc
      | [] -> acc
    )
    mem.locs []

(** The outcome of a final state: the value of every register, and of every
    location under its name -- which is how {!Assertion} reads a condition on
    [x]'s final value. *)
let outcome (st : state) =
  let env = Hashtbl.create 16 in
    List.iter
      (fun (l, v) -> Hashtbl.replace env (Loc.to_string l) (Val.to_expr v))
      (final_memory st.memory);
    (* A run that aborted before its first thread was set up has none. *)
    if Array.length st.threads > 0 then
      SMap.iter
        (fun r v -> Hashtbl.replace env r (Val.to_expr v))
        st.threads.(0).regs;
    env

let show_outcome env =
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) env []
  |> List.sort compare
  |> List.map (fun (k, v) -> Printf.sprintf "%s=%s" k (Expr.Expr.to_string v))
  |> String.concat " "

(** The relations a tracked run ends with, over event labels. *)
type relations = {
  events : int list;
  rf : (int * int) list;
  co : (int * int) list;
      (** Timestamp order per location over the write events, transitively
          closed, as sMRD's coherence order is. *)
  rmw : (int * int) list;
  symbols : (string * expr) list;  (** What each read's symbol took. *)
}

(** One distinct outcome: the final values, why the run aborted if it did, and
    its relations if they were tracked. *)
type result = {
  env : (string, expr) Hashtbl.t;
  why_aborted : string option;
  relations : relations option;
}

let relations_of tr (st : state) =
  let main =
    if Array.length st.threads > 0 then Some st.threads.(0) else None
  in
  let rf =
    Option.fold ~none:[]
      ~some:(fun th ->
        List.filter_map
          (fun (src, r) ->
            match src with
            | Label w -> Some (w, r)
            | Pending id ->
                Option.map (fun w -> (w, r)) (List.assoc_opt id st.memory.resolved)
          )
          th.rf_log
      )
      main
  in
  let is_write l =
    match Hashtbl.find_opt tr.structure.events l with
    | Some (ev : event) -> ev.typ = Write
    | None -> false
  in
  let co =
    LocMap.fold
      (fun _ cs acc ->
        let writes =
          List.filter_map
            (fun c ->
              match (c.kind, c.src) with
              | Msg, Some (Label l) when is_write l -> Some l
              | _ -> None
            )
            (List.sort by_ts cs)
        in
        let rec pairs = function
          | w :: rest -> List.map (fun w' -> (w, w')) rest @ pairs rest
          | [] -> []
        in
          pairs writes @ acc
      )
      st.memory.locs []
  in
  let rmw = Option.fold ~none:[] ~some:(fun th -> th.rmw_log) main in
  let events =
    Option.fold ~none:[] ~some:(fun th -> th.mapped) main
    @ List.concat_map (fun (a, b) -> [ a; b ]) (rf @ co @ rmw)
    |> List.sort_uniq compare
  in
    {
      events;
      rf = List.sort_uniq compare rf;
      co = List.sort_uniq compare co;
      rmw = List.sort_uniq compare rmw;
      symbols = Option.fold ~none:[] ~some:(fun th -> th.binds) main;
    }

let execution_of_result id r : symbolic_execution =
  let set l = USet.of_list l in
  let rel f = Option.fold ~none:(USet.create ()) ~some:(fun r -> set (f r)) r.relations in
    {
      id;
      e = rel (fun r -> r.events);
      rf = rel (fun r -> r.rf);
      dp = USet.create ();
      ppo = USet.create ();
      rmw = rel (fun r -> r.rmw);
      fwd = USet.create ();
      we = USet.create ();
      (* The values the reads took, so that conditions over the symbols of
         events -- the path condition of a write read from -- are decided. *)
      ex_p =
        Option.fold ~none:[]
          ~some:(fun r ->
            List.map (fun (s, v) -> EBinOp (ESymbol s, "=", v)) r.symbols
          )
          r.relations;
      justifications = [];
      co = Option.map (fun r -> set r.co) r.relations;
      fix_rf_map = Hashtbl.create 0;
      pointer_map = None;
      final_env = r.env;
      aborted = r.why_aborted;
    }

(** [outcomes ~version ~loops ~step_counter program] is every distinct outcome
    of [program] under [version], each as its [final_env] and, for a run that
    aborted, why. *)
let outcomes ?tr ~version ~loops ~step_counter (program : ir_node list) =
  let stats =
    {
      states = 0;
      promises = 0;
      certifications = 0;
      consistency = Hashtbl.create 1024;
      candidates = Hashtbl.create 1024;
    }
  in
  Hashtbl.reset stuck_paths;
  let main () =
    normalize ~loops
      {
        name = "t";
        code = stmts program;
        regs = SMap.empty;
        written = [];
        cur = View.bot;
        acq = View.bot;
        rel_all = View.bot;
        rel = LocMap.empty;
        budget = step_counter;
        allocs = 0;
        last = None;
        binds = [];
        rf_log = [];
        rmw_log = [];
        mapped = [];
        promised = 0;
      }
  in
  let finals =
    match main () with
    | main ->
        (* A read of an initial value reads from no write event, and has no
           [rf] edge, as under sMRD: the initial message carries no [src]. *)
        explore ?tr ~version ~loops ~stats [| main |] empty_memory View.bot
    | exception Stuck what ->
        [
          {
            threads = [||];
            memory = empty_memory;
            sc_view = View.bot;
            aborted = Some what;
          };
        ]
  in
    Hashtbl.iter
      (fun what n ->
        Logs_safe.warn (fun m ->
            m
              "%s: %d steps had undefined behaviour (%s) in a thread that was \
               not promise-consistent, so could not abort; their paths were \
               discarded"
              (show_version version) n what
        )
      )
      stuck_paths;
  let seen = Hashtbl.create 16 in
  let envs =
    List.filter_map
      (fun st ->
        let env = outcome st in
        let relations = Option.map (fun tr -> relations_of tr st) tr in
        let k =
          ( show_outcome env,
            st.aborted,
            Option.map (fun r -> (r.rf, r.co, r.rmw)) relations )
        in
          if Hashtbl.mem seen k then None
          else (
            Hashtbl.add seen k ();
            Some (k, { env; why_aborted = st.aborted; relations })
          )
      )
      finals
    |> List.sort (fun (a, _) (b, _) -> compare a b)
    |> List.map snd
  in
    Logs_safe.info (fun m ->
        m "%s: %d states, %d promises tried, %d certifications, %d outcomes"
          (show_version version) stats.states stats.promises
          stats.certifications (List.length envs)
    );
    envs

(** {1 Pipeline Step} *)

let version_of_semantics = function
  | Promising1 -> Some PS1
  | Promising2 -> Some PS2
  | Smrd -> None

let loops_of_options (options : options) step_counter =
  match options.loop_semantics with
  | StepCounterPerLoop -> PerLoop step_counter
  | FiniteStepCounter -> Global
  | Symbolic | Generic ->
      unsupported
        "symbolic loop semantics; promising semantics needs a step counter \
         (--step-counter or --step-counter-per-loop)"

(** [calculate_executions ~version ctx] fills [ctx.executions] with the
    outcomes of the program under [version], one execution per outcome. *)
(** The relations promising semantics can answer for: [.rf] and [.co], which it
    defines, [.rmw], and [.po], the event structure's own. [.dp] and [.ppo] are
    sMRD's, and have no counterpart. *)
let answerable_relations = [ ".rf"; ".co"; ".rmw"; ".po" ]

(** The relations [e] asks about. *)
let rec relations_named = function
  | EVar v when String.length v > 0 && v.[0] = '.' -> [ v ]
  | EBinOp (l, _, r) -> relations_named l @ relations_named r
  | EUnOp (_, e) -> relations_named e
  | EOr es -> List.concat_map relations_named es
  | _ -> []

let calculate_executions ~version (ctx : mordor_ctx) =
  match ctx.program_stmts with
  | None ->
      Logs_safe.err (fun m -> m "No program statements for promising semantics.");
      ctx
  | Some program ->
      List.iter
        (function
          | Ir.Chained _ ->
              failwith
                "Refinement chains are checked under sMRD only; promising \
                 semantics computes one program's outcomes."
          | Ir.Outcome { condition = Ir.CondExpr e; _ }
            when List.exists
                   (fun r -> not (List.mem r answerable_relations))
                   (relations_named e) ->
              failwith
                (Printf.sprintf
                   "%s: the assertion asks about %s, which promising \
                    semantics does not define; it answers for %s."
                   ctx.litmus_name
                   (String.concat ", "
                      (List.filter
                         (fun r -> not (List.mem r answerable_relations))
                         (relations_named e)
                      )
                   )
                   (String.concat ", " answerable_relations)
                )
          | Ir.Outcome { model = Some model; _ } | Ir.Model { model }
            when model <> ""
                 && not
                      (List.mem (String.lowercase_ascii model)
                         promising_model_names
                      ) ->
              Logs_safe.warn (fun m ->
                  m
                    "The assertion names the model %S, and is checked under \
                     %s instead."
                    model (show_version version)
              )
          | _ -> ()
          )
        ctx.assertions;
      if Option.value ctx.litmus_constraints ~default:[] <> [] then
        Logs_safe.warn (fun m ->
            m
              "%s: the constraints on symbolic values in the header are \
               ignored; promising semantics computes concrete values."
              ctx.litmus_name
        );
      let loops = loops_of_options ctx.options ctx.step_counter in
      (* The relations are tracked only when an assertion asks about one:
         tracking costs states. *)
      let asks =
        List.exists
          (function
            | Ir.Outcome { condition = Ir.CondExpr e; _ } -> relations_named e <> []
            | _ -> false
            )
          ctx.assertions
      in
      let tr =
        match (asks, ctx.structure, ctx.source_spans) with
        | true, Some structure, Some spans -> Some (make_tracker structure spans)
        | true, _, _ ->
            failwith
              "Relations are tracked against the interpreted event structure, \
               and there is none: run Interpret.step_interpret first."
        | false, _, _ -> None
      in
      let envs =
        try outcomes ?tr ~version ~loops ~step_counter:ctx.step_counter program
        with Unsupported what ->
          failwith
            (Printf.sprintf "%s: promising semantics does not support %s."
               ctx.litmus_name what
            )
      in
        List.iter
          (fun r ->
            Logs_safe.debug (fun m ->
                m "%s outcome: %s%s%s" (show_version version) (show_outcome r.env)
                  ( match r.why_aborted with
                  | Some what -> " (aborted: " ^ what ^ ")"
                  | None -> ""
                  )
                  ( match r.relations with
                  | Some rel ->
                      let pairs ps =
                        String.concat " "
                          (List.map (fun (a, b) -> Printf.sprintf "%d->%d" a b) ps)
                      in
                        Printf.sprintf "; rf: %s; co: %s" (pairs rel.rf) (pairs rel.co)
                  | None -> ""
                  )
            )
          )
          envs;
        let executions = List.mapi execution_of_result envs in
        (* Every assertion is checked against these executions, whichever model
           it names. *)
        let model = "promising" in
          ctx.options.coherent <- model;
          ctx.assertion_models <- List.map (fun _ -> model) ctx.assertions;
          ctx.model_executions <- None;
          ctx.executions <- Some (USet.of_list executions);
          ctx

(** [step_calculate_executions lwt_ctx] computes the executions under the
    promising semantics [ctx.options.semantics] selects, in place of sMRD's
    justification and dependency steps: it follows [Interpret.step_interpret]
    and precedes [Assertion.step_check_assertions].

    @raise Invalid_argument if the options select sMRD. *)
let step_calculate_executions (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  Lwt.map
    (fun ctx ->
      match version_of_semantics ctx.options.semantics with
      | Some version -> calculate_executions ~version ctx
      | None ->
          invalid_arg
            "Promising.step_calculate_executions: the options select sMRD"
    )
    lwt_ctx
