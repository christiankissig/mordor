open Events
open Expr
open Types
open Uset

module SymbolicEventStructure = struct
  type t = symbolic_event_structure

  let create () : t =
    {
      e = USet.create ();
      events = Hashtbl.create 16;
      po = USet.create ();
      po_iter = USet.create ();
      rmw = USet.create ();
      lo = USet.create ();
      restrict = Hashtbl.create 16;
      defacto = Hashtbl.create 16;
      fj = USet.create ();
      p = Hashtbl.create 16;
      constraints = [];
      conflict = USet.create ();
      origin = Hashtbl.create 16;
      loop_indices = Hashtbl.create 16;
      loop_conditions = Hashtbl.create 16;
      thread_index = Hashtbl.create 16;
      write_events = USet.create ();
      read_events = USet.create ();
      rlx_write_events = USet.create ();
      rlx_read_events = USet.create ();
      fence_events = USet.create ();
      branch_events = USet.create ();
      malloc_events = USet.create ();
      free_events = USet.create ();
      terminal_events = USet.create ();
    }

  (* [with_binding tbl k v] is a copy of [tbl] in which [k] is bound to [v].
     Copy on write: [dot] used to write into its operand's [restrict] and
     [defacto], so the operand came back changed, and a structure prefixed
     twice, or combined again after being prefixed, had its two results writing
     into each other. *)
  let with_binding tbl k v =
    let tbl = Hashtbl.copy tbl in
      Hashtbl.replace tbl k v;
      tbl

  (* [with_binding] when there is something to bind. *)
  let with_binding_opt tbl k = function
    | Some v -> with_binding tbl k v
    | None -> tbl

  (* [dot] is where an event enters a structure, so it is where the per-event
     tables learn of it: the event itself, the symbol it originates -- the one
     it reads or allocates, if any -- and, where the caller has them, the
     register environment it ran in, the loops it is inside and its thread.
     Interpretation used to keep one program-wide table of each and stamp them
     onto the finished structure, which then also described every event that
     had been created and never made it in. *)
  let dot ?env ?loops ?thread (event : event) (structure : t) phi defacto : t =
    if List.exists (fun p -> p = EBoolean false) phi then
      Logs_safe.warn (fun m ->
          m "Adding event %d under unsatisfiable path condition.\n" event.label
      );
    {
      e = USet.union structure.e (USet.singleton event.label);
      events = with_binding structure.events event.label event;
      po =
        USet.union structure.po
          (USet.map (fun e -> (event.label, e)) structure.e);
      po_iter = structure.po_iter;
      rmw = structure.rmw;
      lo = structure.lo;
      restrict = with_binding structure.restrict event.label phi;
      defacto = with_binding structure.defacto event.label defacto;
      fj = structure.fj;
      p = with_binding_opt structure.p event.label env;
      constraints = structure.constraints;
      conflict = structure.conflict;
      origin =
        ( match event.rval with
        | Some (VSymbol symbol) ->
            with_binding structure.origin symbol event.label
        | _ -> structure.origin
        );
      loop_indices = with_binding_opt structure.loop_indices event.label loops;
      loop_conditions = structure.loop_conditions;
      thread_index = with_binding_opt structure.thread_index event.label thread;
      write_events =
        ( if event.typ = Write then
            USet.union structure.write_events (USet.singleton event.label)
          else structure.write_events
        );
      read_events =
        ( if event.typ = Read then
            USet.union structure.read_events (USet.singleton event.label)
          else structure.read_events
        );
      rlx_write_events =
        ( if event.typ = Write && event.wmod = Relaxed then
            USet.union structure.rlx_write_events (USet.singleton event.label)
          else structure.rlx_write_events
        );
      rlx_read_events =
        ( if event.typ = Read && event.rmod = Relaxed then
            USet.union structure.rlx_read_events (USet.singleton event.label)
          else structure.rlx_read_events
        );
      fence_events =
        ( if event.typ = Fence then
            USet.union structure.fence_events (USet.singleton event.label)
          else structure.fence_events
        );
      branch_events =
        ( if event.typ = Branch then
            USet.union structure.branch_events (USet.singleton event.label)
          else structure.branch_events
        );
      malloc_events =
        ( if event.typ = Malloc then
            USet.union structure.malloc_events (USet.singleton event.label)
          else structure.malloc_events
        );
      free_events =
        ( if event.typ = Free then
            USet.union structure.free_events (USet.singleton event.label)
          else structure.free_events
        );
      terminal_events =
        ( if event.typ = Terminal then
            USet.union structure.terminal_events (USet.singleton event.label)
          else structure.terminal_events
        );
    }

  (* [merged a b] is a fresh table with [a]'s bindings and then [b]'s, [b]
     winning where both bind a key.

     While interpretation keeps one program-wide table of each kind, both
     operands of a combinator hold that very table, and the merge is a copy of
     it: the test for physical equality is what keeps that case from walking the
     table twice. Operands that own their tables get the union. *)
  let merged a b =
    if a == b || Hashtbl.length a >= Hashtbl.length b then (
      let tbl = Hashtbl.copy a in
        if b != a then Hashtbl.iter (Hashtbl.replace tbl) b;
        tbl
    )
    else
      (* Copy the larger and add the smaller: one event prefixed to a long
         continuation is the common case. *)
      let tbl = Hashtbl.copy b in
        Hashtbl.iter
          (fun k v -> if not (Hashtbl.mem tbl k) then Hashtbl.replace tbl k v)
          a;
        tbl

  (* [join x y] is the union of two sets, and is one of them when the other is
     empty rather than a copy of it.

     Sharing is safe because nothing adds to a structure's sets in place: [dot]
     has always handed its operand's [conflict], [rmw], [lo] and [fj] to its
     result as they were. It is needed because a structure is mostly built one
     event at a time, and a singleton is empty in every relation and all but
     one of the event sets. Copying the continuation's at each step made
     interpreting rcu-3, whose conflict relation has 607k pairs, take about
     5s instead of about 1s. *)
  let join x y =
    if USet.is_empty y then x else if USet.is_empty x then y else USet.union x y

  (* What [plus] and [cross] agree on: every set and relation is the union of
     the operands', and the per-event tables are merged. They differ in
     [conflict] alone.

     [loop_conditions] is the exception. It is keyed by loop, not by event, and
     holds one guard per interpreted occurrence of the loop, so it is not a
     table two operands can be asked to agree on; interpretation keeps it and
     hands it over when it returns (interpret.ml). *)
  let union (a : t) (b : t) ~conflict : t =
    {
      e = join a.e b.e;
      events = merged a.events b.events;
      po = join a.po b.po;
      po_iter = join a.po_iter b.po_iter;
      rmw = join a.rmw b.rmw;
      lo = join a.lo b.lo;
      restrict = merged a.restrict b.restrict;
      defacto = merged a.defacto b.defacto;
      fj = join a.fj b.fj;
      p = merged a.p b.p;
      constraints = a.constraints @ b.constraints;
      conflict;
      origin = merged a.origin b.origin;
      loop_indices = merged a.loop_indices b.loop_indices;
      loop_conditions = a.loop_conditions;
      thread_index = merged a.thread_index b.thread_index;
      write_events = join a.write_events b.write_events;
      read_events = join a.read_events b.read_events;
      rlx_write_events = join a.rlx_write_events b.rlx_write_events;
      rlx_read_events = join a.rlx_read_events b.rlx_read_events;
      fence_events = join a.fence_events b.fence_events;
      branch_events = join a.branch_events b.branch_events;
      malloc_events = join a.malloc_events b.malloc_events;
      free_events = join a.free_events b.free_events;
      terminal_events = join a.terminal_events b.terminal_events;
    }

  let plus a b : t =
    let conflict = USet.union a.conflict b.conflict in
    let conflict =
      USet.inplace_union ~into:conflict (URelation.cross a.e b.e)
    in
    let conflict =
      USet.inplace_union ~into:conflict (URelation.cross b.e a.e)
    in
      union a b ~conflict

  let cross a b : t = union a b ~conflict:(join a.conflict b.conflict)

  (* On [events_in_loop], below: intersected with [e]. [loop_indices] was once a
     program-wide table that interpret.ml handed over whole, stamped with every
     event it ever created, so an event dropped on the way out of interpretation
     kept its loop membership. branch_condition/nested_fail is where that
     showed: loop 1's members came back as [8; 9; 12] against an [e] holding
     neither 9 nor 12, so episodicity bisected over two events that did not
     exist.

     [dot] builds the table now and it binds events of the structure only, so
     for a structure interpretation built the intersection removes nothing. It
     stays for the ones built by hand, in tests and elsewhere, that make no
     such promise. *)

  (* [seq a b] is [a] followed by [b]: everything in [a] is po-before everything
     in [b], and the same pairs are recorded in [fj].

     This is the join.  It is [dot] generalised from one event to a whole
     structure -- [dot] prefixes an event by adding [{event} x structure.e] to
     po, and this adds [a.e x b.e] -- and it is what a parallel block composed
     with its continuation needs, since the continuation may not begin until
     every thread has finished.

     [fj] gets the same pairs because it is the fork-join relation:
     [Assertion]'s rhb reads it as [(ppo u fj u dp u rf)+] and [Elaborations]
     subtracts it from [ppo_loc].  Until now nothing wrote to it, so both read
     an empty relation.

     [a]'s terminal events stay terminal.  They are still the ends of their own
     threads, and [compute_ppo_init] only ever filters po, so the join cannot
     put a continuation event before one of them. *)
  let seq (a : t) (b : t) : t =
    let joined = URelation.cross a.e b.e in
    let c = cross a b in
      { c with po = USet.union c.po joined; fj = USet.union c.fj joined }

  let events_in_loop (structure : t) loop_id =
    Hashtbl.fold
      (fun event loop_indices acc ->
        if List.mem loop_id loop_indices && USet.mem structure.e event then
          USet.add acc event
        else acc
      )
      structure.loop_indices (USet.create ())

  let events_po_before structure event =
    USet.filter (fun (e1, e2) -> e2 = event) structure.po |> URelation.pi_1
end

(* The algebra of event structures: what a program denotes is built from
   [empty] and [singleton] with [seq], [choice] and [par], and nothing else.

   It is a facade over [SymbolicEventStructure]'s combinators and adds no
   behaviour of its own. What it adds is the vocabulary: the classic recursion
   builds a structure from the end with [dot], a bottom-up construction builds
   fragments and joins them, and both can say what they build in these five
   operations. This is the seam between the two. *)
module EventStructure = struct
  module S = SymbolicEventStructure

  type t = symbolic_event_structure

  let empty = S.create

  let singleton ?env ?loops ?thread event phi defacto =
    S.dot ?env ?loops ?thread event (S.create ()) phi defacto

  let choice = S.plus
  let par = S.cross

  (* [S.dot event b] is [seq (singleton event) b], and [S.seq a b] is
     [seq ~join:true a b]. *)
  let seq ?(join = false) (a : t) (b : t) : t =
    let ordered = URelation.cross a.e b.e in
    let c = S.cross a b in
      {
        c with
        po = USet.union c.po ordered;
        fj = (if join then USet.union c.fj ordered else c.fj);
      }

  let relabel ?(off = 0) ?(relab = fun _ -> None) ?(env_key = Fun.id)
      ?(thread_off = 0) (s : t) : t =
    let l x = x + off in
    let pair (a, b) = (l a, l b) in
    let ex = Expr.rename ~relab in
    let map fk fv tbl =
      let t = Hashtbl.create (max 16 (Hashtbl.length tbl)) in
        Hashtbl.iter (fun k v -> Hashtbl.replace t (fk k) (fv v)) tbl;
        t
    in
    let event (ev : event) =
      { (Event.rename ~relab ev) with label = l ev.label }
    in
      {
        e = USet.map l s.e;
        events = map l event s.events;
        po = USet.map pair s.po;
        po_iter = USet.map pair s.po_iter;
        rmw = USet.map (fun (a, c, b) -> (l a, ex c, l b)) s.rmw;
        lo = USet.map pair s.lo;
        restrict = map l (List.map ex) s.restrict;
        defacto = map l (List.map ex) s.defacto;
        fj = USet.map pair s.fj;
        p = map l (map env_key ex) s.p;
        constraints = List.map ex s.constraints;
        conflict = USet.map pair s.conflict;
        origin = map (fun x -> Option.value (relab x) ~default:x) l s.origin;
        loop_indices = map l Fun.id s.loop_indices;
        loop_conditions = s.loop_conditions;
        thread_index = map l (( + ) thread_off) s.thread_index;
        write_events = USet.map l s.write_events;
        read_events = USet.map l s.read_events;
        rlx_write_events = USet.map l s.rlx_write_events;
        rlx_read_events = USet.map l s.rlx_read_events;
        fence_events = USet.map l s.fence_events;
        branch_events = USet.map l s.branch_events;
        malloc_events = USet.map l s.malloc_events;
        free_events = USet.map l s.free_events;
        terminal_events = USet.map l s.terminal_events;
      }

  (* Everything rendered to sorted strings: the sets and tables are hash
     tables, whose order is an accident, and an expression holds a [Z.t]. *)
  let render (s : t) : string list list =
    let i = string_of_int in
    let pair (a, b) = Printf.sprintf "(%d,%d)" a b in
    let set show u = USet.values u |> List.map show |> List.sort compare in
    let tbl show_k show_v t =
      Hashtbl.fold (fun k v acc -> (show_k k ^ ": " ^ show_v v) :: acc) t []
      |> List.sort compare
    in
    let exprs es = String.concat " && " (List.map Expr.to_string es) in
    let env e = String.concat ", " (tbl Fun.id Expr.to_string e) in
      [
        set i s.e;
        tbl i show_event s.events;
        set pair s.po;
        set pair s.po_iter;
        set
          (fun (a, c, b) -> Printf.sprintf "(%d,%s,%d)" a (Expr.to_string c) b)
          s.rmw;
        set pair s.lo;
        tbl i exprs s.restrict;
        tbl i exprs s.defacto;
        set pair s.fj;
        tbl i env s.p;
        List.map Expr.to_string s.constraints |> List.sort_uniq compare;
        set pair s.conflict;
        tbl Fun.id i s.origin;
        tbl i (fun ls -> String.concat ";" (List.map i ls)) s.loop_indices;
        tbl i exprs s.loop_conditions;
        tbl i i s.thread_index;
        set i s.write_events;
        set i s.read_events;
        set i s.rlx_write_events;
        set i s.rlx_read_events;
        set i s.fence_events;
        set i s.branch_events;
        set i s.malloc_events;
        set i s.free_events;
        set i s.terminal_events;
      ]

  let equal a b = render a = render b
end

(* Find the origin of a symbol in a symbolic event structure *)
let origin structure (s : string) = Hashtbl.find_opt structure.origin s

(** [may_reuse structure a b] holds when allocations [a] and [b] may be handed
    the same address: one of them may be freed before the other is allocated,
    and an allocator is free to hand a released region straight back out.

    Which allocation a free releases is read off its location. A free of an
    allocation's own symbol releases that allocation and no other. A free
    through a pointer loaded from memory, or computed from one, may release any
    allocation whose address escapes into memory -- is written somewhere, and
    so may be loaded back. An address that is never written cannot be loaded:
    rcu-3's counter cell [rC] is only ever written through, and taking its
    reclaim loop's [free(rtemp)] to release it let the counter alias a node.
    The order is approximated by program order: the free cannot follow the
    later allocation in program order, the earlier allocation cannot follow
    the free, and the free and the later allocation must be able to occur
    together. Across threads nothing orders them yet, and a free in one thread
    may precede an allocation in another -- the allocator synchronises the two
    when it reuses the region. *)
let may_reuse (structure : symbolic_event_structure) =
  let allocations =
    USet.values structure.malloc_events
    |> List.filter_map (fun label ->
        match Hashtbl.find_opt structure.events label with
        | Some ({ loc = Some loc; _ } : event) -> Some (label, loc)
        | _ -> None
    )
  in
  let allocation_symbols =
    List.concat_map (fun (_, loc) -> Expr.get_symbols loc) allocations
  in
  let frees =
    USet.values structure.free_events
    |> List.filter_map (fun label ->
        match Hashtbl.find_opt structure.events label with
        | Some ({ loc = Some loc; _ } : event) -> Some (label, loc)
        | _ -> None
    )
  in
  let escaped =
    USet.values structure.write_events
    |> List.concat_map (fun label ->
        match Hashtbl.find_opt structure.events label with
        | Some ({ wval = Some v; _ } : event) -> Expr.get_symbols v
        | _ -> []
    )
  in
  let releases free_loc loc =
    Expr.equal free_loc loc
    || List.exists (fun s -> List.mem s escaped) (Expr.get_symbols loc)
       && List.exists
            (fun s -> not (List.mem s allocation_symbols))
            (Expr.get_symbols free_loc)
  in
  let before a b = USet.mem structure.po (a, b) in
  let conflicting a b =
    USet.mem structure.conflict (a, b) || USet.mem structure.conflict (b, a)
  in
  (* [earlier] is freed by some free, and [later] is allocated after it. *)
  let reused (earlier, earlier_loc) (later, _) =
    (not (before later earlier))
    && List.exists
         (fun (free, free_loc) ->
           releases free_loc earlier_loc
           && (not (before free earlier))
           && (not (before later free))
           && not (conflicting free later)
         )
         frees
  in
    fun a b ->
      match
        ( List.find_opt (fun (_, loc) -> Expr.equal loc a) allocations,
          List.find_opt (fun (_, loc) -> Expr.equal loc b) allocations )
      with
      | Some a, Some b -> reused a b || reused b a
      | _ -> false

(** Path type *)
type path_info = {
  path : int uset;
  p : expr list; (* List of predicate lists, serves as conjunction *)
}

(** Generate all paths through the control flow structure *)
let rec cartesian = function
  | [] -> [ [] ]
  | hd :: tl ->
      List.concat_map (fun x -> List.map (List.cons x) (cartesian tl)) hd

(** Generate maximal conflict-free sets of events as paths through the symbolic
    event structure. *)
let generate_max_conflictfree_sets (structure : symbolic_event_structure) =
  let e = USet.set_minus structure.e structure.branch_events in
  let po = USet.intersection structure.po (URelation.cross e e) in
  let po_intransitive = URelation.transitive_reduction po in
  let po_tree = URelation.adjacency_map po_intransitive in

  (*Partition neighbours into groups where each group is mutually in conflict *)
  let partition_by_conflict neighbours conflict =
    let neighbours_list = USet.values neighbours in

    (* Helper: find all neighbours in the same conflict group as 'seed' *)
    let rec find_conflict_group seed remaining acc =
      match remaining with
      | [] -> (acc, [])
      | n :: rest ->
          (* Check if n conflicts with all members of acc (including seed) *)
          let conflicts_with_all =
            List.for_all
              (fun member ->
                USet.mem conflict (member, n)
                || USet.mem conflict (n, member)
                || member = n
              )
              (seed :: acc)
          in
            if conflicts_with_all then find_conflict_group seed rest (n :: acc)
            else
              let group, remaining' = find_conflict_group seed rest acc in
                (group, n :: remaining')
    in

    (* Partition all neighbours into conflict groups *)
    let rec partition remaining groups =
      match remaining with
      | [] -> groups
      | seed :: rest ->
          let group, remaining' = find_conflict_group seed rest [ seed ] in
            partition remaining' (group :: groups)
    in

    partition neighbours_list []
  in

  (* DFS search for all paths. Each path is a uset event IDs. Search produces
     list of paths such paths. *)
  let rec dfs current =
    let neighbours =
      Hashtbl.find_opt po_tree current |> Option.value ~default:(USet.create ())
    in
      if USet.size neighbours == 0 then
        (* leaf node *)
        [ USet.singleton current ]
      else if USet.size neighbours == 1 then
        (* one neighbour; continue down that path *)
        let next = USet.values neighbours |> List.hd in
          dfs next |> List.map (fun path -> USet.add path current)
      else if
        USet.subset
          (USet.set_minus
             (URelation.cross neighbours neighbours)
             (URelation.identity neighbours)
          )
          structure.conflict
      then
        (* neighbour branches are in conflict; disjoint union *)
        USet.values neighbours
        |> List.map dfs
        |> List.flatten
        |> List.map (fun path -> USet.add path current)
      else
        (* Multiple neighbours: partition by conflict *)
        let conflict_groups =
          partition_by_conflict neighbours structure.conflict
        in

        (* For each conflict group, choose one alternative (disjoint union) *)
        (* Across groups, take all combinations (cartesian product) *)
        conflict_groups
        |> List.map (fun group ->
            (* Within this conflict group, just flatten (disjoint union) *)
            List.map dfs group |> List.flatten
        )
        |> cartesian
        |> List.map (fun paths ->
            List.fold_left
              (fun acc path -> USet.union acc path)
              (USet.singleton current) paths
        )
  in

  (* Find root events (events with no predecessors in po) *)
  let roots =
    let all_events = structure.e in
    let has_predecessor = URelation.pi_2 structure.po in
      USet.set_minus all_events has_predecessor
  in

  Logs_safe.debug (fun m ->
      m "Generating paths from roots: %s"
        (String.concat ", " (USet.values (USet.map (Printf.sprintf "%d") roots)))
  );

  (* Generate p from value restrictions along path and compose path_info. TODO
     need to filter paths by satisfiability? *)
  let paths =
    USet.values roots
    |> List.map dfs
    |> List.flatten
    |> List.map (fun path ->
        let p =
          USet.values path
          |> List.map (fun e ->
              Hashtbl.find_opt structure.restrict e |> Option.value ~default:[]
          )
          |> List.flatten
          |> USet.of_list
          |> USet.values
        in
          { path; p }
    )
  in
    Logs_safe.debug (fun m ->
        m "Generated %d paths through the control flow" (List.length paths)
    );
    paths

(* Check if write w is downward-closed same-location write before read r. This
   prevents r reading from shadowed writes w.*)
(* [exclude] names events the caller's execution does not contain -- the elided
   set, in practice.  A shadowing write has to be in the execution to shadow
   anything, and the write-elision tests are exactly where that bites: in
   write-before-lift.lit the second [y := 1] shadows the first, so when the
   second is elided the read must be free to take the first, and without this
   filter it is not.  Without it the freezing pass loses executions on
   write-before-lift, RREWA, Redundant Write after Read Elimination,
   PPO000-019, listing20 and listing21. *)
(* [state] is the solver state the shadowing test is decided under.  The rf
   edge being tested has its location checked under the path predicates, and
   the shadow test on the same edge used to run under r's branch conditions
   alone.  Callers now pass the predicates their own location test uses, so
   both tests on the edge see the same assumptions; with no [state], r's branch
   conditions remain the default.

   In practice the two decide the same way, which is worth knowing before
   expecting this to prune anything.  The interpreter continues a program
   after an [if] inside each branch, so [restrict r] already carries every
   branch condition on r's path.  What the path predicates add on top is the
   pairwise disjointness of static and allocated locations -- disequalities,
   which cannot make a location equality provable -- and the litmus [[...]]
   constraints, which no test uses.  Measured on 2026-09-11 over litmus-tests/
   and litmus-tests-review/: no rf edge in 284 files is shadowed under one
   state and not the other, and neither execution counts, verdicts nor run
   time move. *)
(* TODO optimize; pregenerate *)
let dslwb ?(exclude = USet.create ()) ?state structure w r =
  let write_events =
    structure.write_events
    |> USet.union structure.malloc_events
    |> USet.union structure.free_events
  in
  let r_restrict =
    match state with
    | Some state -> state
    | None -> Hashtbl.find_opt structure.restrict r |> Option.value ~default:[]
  in
  let result =
    USet.exists
      (fun (w2, r2) ->
        if
          r2 = r (* w2 po bfore r *)
          && w2 <> w (* w2 is not w *)
          && USet.mem write_events w2 (* w2 is a write *)
          && (not (USet.mem exclude w2)) (* w2 is in the execution *)
          && USet.mem structure.po (w, w2)
          (* w2 po after w, thus in between w and r *)
        then
          (* w2 potentially shadows w *)
          match (get_loc structure w, get_loc structure w2) with
          | Some loc, Some loc2 -> Solver.exeq ~state:r_restrict loc loc2
          | None, Some loc2 -> (
              if w > 0 then false
              else
                match get_loc structure r with
                | Some locr -> Solver.exeq ~state:r_restrict loc2 locr
                | None -> false
            )
          | _, _ -> false
        else false
      )
      structure.po
  in
    result

let init_ppo structure =
  let events = structure.events in
  let po = structure.po in
  let init_ppo =
    if Hashtbl.mem events 0 then USet.filter (fun (f, t) -> f <> t && f = 0) po
    else USet.create ()
  in
  let terminal_events =
    Hashtbl.fold
      (fun lbl ev acc -> if ev.typ = Terminal then USet.add acc lbl else acc)
      structure.events (USet.create ())
  in
  let terminal_ppo =
    USet.filter (fun (f, t) -> f <> t && USet.mem terminal_events t) po
  in
  (* TODO discern in subsequent computation *)
  let init_ppo = USet.union init_ppo terminal_ppo in
    init_ppo

(* TODO accomodate indexing po_iter by loop indices *)
let symbols_in_loop structure e =
  let e_loops =
    Hashtbl.find_opt structure.loop_indices e
    |> Option.value ~default:[]
    |> USet.of_list
  in
  let evt = Hashtbl.find structure.events e in
  let symbols =
    (Option.map Expr.get_symbols evt.loc |> Option.value ~default:[])
    @ (Option.map Value.get_symbols evt.rval |> Option.value ~default:[])
    @ (Option.map Expr.get_symbols evt.wval |> Option.value ~default:[])
    |> USet.of_list
    |> USet.filter (fun s ->
        let o_loops =
          Hashtbl.find structure.origin s
          |> Hashtbl.find_opt structure.loop_indices
          |> Option.value ~default:[]
          |> USet.of_list
        in
          USet.size (USet.intersection e_loops o_loops) > 0
    )
  in
    symbols
