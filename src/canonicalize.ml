(** Canonicalization of symbolic executions (from S9; productized by R1).

    Produces an order- and id-independent rendering of an execution (and of a
    whole execution set), so two runs of the pipeline can be compared for
    equivalence regardless of the internal enumeration order in which events,
    relation pairs, and executions happen to be produced.

    This is the trustworthy comparison primitive the bottom-up migration is
    gated on: every "canonicalized outputs equal" exit criterion is checked
    through here. R1's golden-diff target ([test/golden]) renders each litmus
    test's execution set through this module and diffs it against a committed
    golden.

    What is canonicalized:
    - events are ordered by (thread, program-order label) and renumbered to a
      dense [0..n) index; each carries a descriptor (thread, kind, location);
    - the relations po (restricted to the execution), rf, dp, ppo and rmw are
      rewritten through the renumbering and sorted;
    - path predicates are rendered to strings and sorted.

    Note on limitations (feeds plan risk R2): predicates are compared
    *syntactically* (rendered expression strings). Two semantically-equivalent
    but syntactically-different predicate sets will diverge here; where that
    happens the comparison must escalate to a solver check. [signature]
    therefore lets callers exclude predicates so that the structural core can
    be compared independently of the syntactic-predicate question. Coherence
    order [co] is not part of a [symbolic_execution] (it is recomputed on
    demand in {!Coherence}) and so is not included. *)

open Expr
open Types
open Uset

(** Canonical form of a single execution. Fields hold renumbered, sorted data;
    equality is ordinary structural equality. *)
type t = {
  events : string list;  (** canonical event descriptors, in canonical order *)
  po : (int * int) list;  (** structure po restricted to this execution *)
  rf : (int * int) list;
  dp : (int * int) list;
  ppo : (int * int) list;
  rmw : (int * int) list;
  predicates : string list;  (** sorted rendered path conditions *)
}

(** A short, stable description of an event: thread, kind (with [*] for RMW)
    and location. Used both as canonical content and as a tie-break key. *)
let event_descriptor (structure : symbolic_event_structure) (id : int) : string
    =
  match Hashtbl.find_opt structure.events id with
  | None -> Printf.sprintf "?%d" id
  | Some evt ->
      let thread =
        Hashtbl.find_opt structure.thread_index id
        |> Option.map string_of_int
        |> Option.value ~default:"-"
      in
      let loc =
        Option.map Expr.to_string evt.loc |> Option.value ~default:""
      in
      let kind =
        show_event_type evt.typ ^ if evt.is_rdmw then "*" else ""
      in
        Printf.sprintf "t%s:%s@%s" thread kind loc

(* Canonical event order: by thread, then by label. Event labels are allocated
   in program order, so within a thread this reproduces program order without a
   separate topological pass over po. *)
let canonical_order (structure : symbolic_event_structure) (a : int) (b : int) :
    int =
  let thr id =
    Hashtbl.find_opt structure.thread_index id |> Option.value ~default:(-1)
  in
    compare (thr a, a) (thr b, b)

(** [canonicalize structure exec] renders [exec] into its canonical form. *)
let canonicalize (structure : symbolic_event_structure)
    (exec : symbolic_execution) : t =
  let pairs r = USet.values r in
  let endpoints r = List.concat_map (fun (a, b) -> [ a; b ]) (pairs r) in
  (* Node set = participating events plus any endpoint mentioned by a relation
     (e.g. the init write, label 0, which reads-from edges reference but which
     is not always in [exec.e]). This keeps init visible and consistently
     renumbered. *)
  let nodes =
    USet.values exec.e
    @ endpoints exec.rf @ endpoints exec.rmw @ endpoints exec.dp
    @ endpoints exec.ppo
    |> List.sort_uniq compare
  in
  let ordered = List.sort (canonical_order structure) nodes in
  let remap = Hashtbl.create (List.length ordered) in
    List.iteri (fun i id -> Hashtbl.replace remap id i) ordered;
    let rn id = try Hashtbl.find remap id with Not_found -> -1 in
    let is_node id = Hashtbl.mem remap id in
    let rel r =
      pairs r
      |> List.filter (fun (a, b) -> is_node a && is_node b)
      |> List.map (fun (a, b) -> (rn a, rn b))
      |> List.sort_uniq compare
    in
    let po =
      (* po lives on the structure, not the execution; restrict to node set. *)
      USet.values structure.po
      |> List.filter (fun (a, b) -> is_node a && is_node b)
      |> List.map (fun (a, b) -> (rn a, rn b))
      |> List.sort_uniq compare
    in
      {
        events = List.map (event_descriptor structure) ordered;
        po;
        rf = rel exec.rf;
        dp = rel exec.dp;
        ppo = rel exec.ppo;
        rmw = rel exec.rmw;
        predicates =
          List.map Expr.to_string exec.ex_p |> List.sort_uniq compare;
      }

let string_of_pairs (ps : (int * int) list) : string =
  ps
  |> List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
  |> String.concat " "

(** A single canonical string for one execution. When [with_predicates] is
    false (the default), path conditions are excluded so that the structural
    core can be compared independently of syntactic-predicate divergence. *)
let signature ?(with_predicates = false) (t : t) : string =
  let events =
    t.events |> List.mapi (fun i d -> Printf.sprintf "%d=%s" i d)
    |> String.concat " "
  in
  let base =
    [
      "E: " ^ events;
      "po: " ^ string_of_pairs t.po;
      "rf: " ^ string_of_pairs t.rf;
      "dp: " ^ string_of_pairs t.dp;
      "ppo: " ^ string_of_pairs t.ppo;
      "rmw: " ^ string_of_pairs t.rmw;
    ]
  in
  let lines =
    if with_predicates then
      base @ [ "phi: " ^ String.concat " ; " t.predicates ]
    else base
  in
    String.concat "\n" lines

(** [canonicalize_set structure execs] canonicalizes every execution and
    returns them sorted, so the result is a canonical rendering of the
    execution *set* (independent of the order [execs] were produced in). *)
let canonicalize_set (structure : symbolic_event_structure)
    (execs : symbolic_execution list) : t list =
  List.map (canonicalize structure) execs
  |> List.sort (fun a b ->
         compare
           (signature ~with_predicates:true a)
           (signature ~with_predicates:true b))

(** Canonical string for a whole execution set. Executions are sorted by their
    individual signatures, so this is invariant under execution reordering. *)
let set_signature ?(with_predicates = false) (ts : t list) : string =
  ts
  |> List.map (signature ~with_predicates)
  |> List.sort compare
  |> List.mapi (fun i s -> Printf.sprintf "--- execution %d ---\n%s" i s)
  |> String.concat "\n"

(** True when two canonical execution sets are equal. Set [with_predicates:true]
    to also require syntactic predicate agreement. *)
let equal_sets ?(with_predicates = false) (a : t list) (b : t list) : bool =
  String.equal
    (set_signature ~with_predicates a)
    (set_signature ~with_predicates b)
