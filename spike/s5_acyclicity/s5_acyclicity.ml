(* S5 (#17): is incrementally maintained topological order faster than
   re-checking acyclicity, at the sizes MoRDor asks about?

   Every relation [URelation.acyclic] was asked about in a run
   (MORDOR_S5_TRACE) is checked from scratch two ways: [URelation.acyclic] as
   it is, which closes the relation transitively and looks for a loop, and a
   depth-first search. Then each is rebuilt as a merge would build it: its
   edges shuffled and added in batches of [k], acyclicity asked after each
   batch, by

   - dfs:     a depth-first search over everything added so far;
   - bounded: for each new edge (u, v), a search from v for u over the graph
              so far -- only a cycle through a new edge can be new;
   - pk:      Pearce and Kelly's dynamic topological order (JEA 2006), which
              searches only between the ends of an edge that goes against the
              order it keeps.

   Every strategy must agree on the first batch after which the relation is
   cyclic. *)

open Uset

let read_trace path : (string * (int * int) list) list =
  let ic = open_in_bin path in
  let rec go acc =
    match (Marshal.from_channel ic : string * (int * int) list) with
    | r -> go (r :: acc)
    | exception End_of_file ->
        close_in ic;
        List.rev acc
  in
    go []

let time f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
    (r, Unix.gettimeofday () -. t0)

(** {1 Graphs} *)

type graph = {
  succ : (int, int list) Hashtbl.t;
  pred : (int, int list) Hashtbl.t;
}

let graph () = { succ = Hashtbl.create 64; pred = Hashtbl.create 64 }
let succs g v = Hashtbl.find_opt g.succ v |> Option.value ~default:[]
let preds g v = Hashtbl.find_opt g.pred v |> Option.value ~default:[]

let add_edge g (u, v) =
  Hashtbl.replace g.succ u (v :: succs g u);
  Hashtbl.replace g.pred v (u :: preds g v)

let nodes edges =
  List.concat_map (fun (a, b) -> [ a; b ]) edges |> List.sort_uniq compare

(* Three-colour depth-first search: a grey successor closes a cycle. *)
let dfs_acyclic g vertices =
  let colour = Hashtbl.create 64 in
  let rec visit v =
    match Hashtbl.find_opt colour v with
    | Some `Grey -> false
    | Some `Black -> true
    | None ->
        Hashtbl.replace colour v `Grey;
        let ok = List.for_all visit (succs g v) in
          Hashtbl.replace colour v `Black;
          ok
  in
    List.for_all visit vertices

let dfs_of_edges edges =
  let g = graph () in
    List.iter (add_edge g) edges;
    dfs_acyclic g (nodes edges)

(* Is [target] reachable from [source]? *)
let reaches g source target =
  let seen = Hashtbl.create 16 in
  let rec go v =
    v = target
    || (not (Hashtbl.mem seen v))
       && begin
         Hashtbl.replace seen v ();
         List.exists go (succs g v)
       end
  in
    go source

(** {1 Pearce--Kelly} *)

type pk = { pg : graph; ord : (int, int) Hashtbl.t; mutable next : int }

let pk () = { pg = graph (); ord = Hashtbl.create 64; next = 0 }

let ord t v =
  match Hashtbl.find_opt t.ord v with
  | Some o -> o
  | None ->
      let o = t.next in
        t.next <- o + 1;
        Hashtbl.replace t.ord v o;
        o

(* [pk_insert t (x, y)] adds the edge, keeping [ord] a topological order;
   [false] when the edge closes a cycle. *)
let pk_insert t (x, y) =
  let ox = ord t x and oy = ord t y in
    add_edge t.pg (x, y);
    if x = y then false
    else if ox < oy then true
    else
      let lb = oy and ub = ox in
      let seen = Hashtbl.create 16 in
      let forward = ref [] and cycle = ref false in
      let rec fwd v =
        if not (Hashtbl.mem seen v) then (
          Hashtbl.replace seen v ();
          forward := v :: !forward;
          List.iter
            (fun w ->
              if w = x then cycle := true
              else if Hashtbl.find t.ord w <= ub then fwd w
            )
            (succs t.pg v)
        )
      in
        fwd y;
        if !cycle then false
        else
          let backward = ref [] in
          let rec bwd v =
            if not (Hashtbl.mem seen v) then (
              Hashtbl.replace seen v ();
              backward := v :: !backward;
              List.iter
                (fun w -> if Hashtbl.find t.ord w >= lb then bwd w)
                (preds t.pg v)
            )
          in
            bwd x;
            let by_ord l =
              List.sort
                (fun a b ->
                  compare (Hashtbl.find t.ord a) (Hashtbl.find t.ord b)
                )
                l
            in
            let moved = by_ord !backward @ by_ord !forward in
            let slots =
              List.map (Hashtbl.find t.ord) moved |> List.sort compare
            in
              List.iter2 (fun v o -> Hashtbl.replace t.ord v o) moved slots;
              true

(** {1 Merges} *)

let shuffle seed l =
  let rng = Random.State.make [| seed |] in
    List.map (fun x -> (Random.State.bits rng, x)) l
    |> List.sort compare
    |> List.map snd

let rec batches k = function
  | [] -> []
  | l ->
      let rec take n acc = function
        | x :: rest when n > 0 -> take (n - 1) (x :: acc) rest
        | rest -> (List.rev acc, rest)
      in
      let b, rest = take k [] l in
        b :: batches k rest

(* The index of the first batch after which the relation is cyclic, or
   [None]. *)
let first_cycle ~k strategy edges =
  let bs = batches k edges in
    match strategy with
    | `Dfs ->
        let so_far = ref [] in
          List.find_index
            (fun b ->
              so_far := b @ !so_far;
              not (dfs_of_edges !so_far)
            )
            bs
    | `Bounded ->
        let g = graph () in
          List.find_index
            (fun b ->
              List.exists
                (fun (u, v) ->
                  add_edge g (u, v);
                  reaches g v u
                )
                b
            )
            bs
    | `Pk ->
        let t = pk () in
          List.find_index
            (fun b -> not (List.for_all (fun e -> pk_insert t e) b))
            bs

(** {1 Report} *)

let percentile p l =
  let a = Array.of_list (List.sort compare l) in
    if a = [||] then 0
    else a.(min (Array.length a - 1) (Array.length a * p / 100))

let () =
  let relations =
    List.concat_map read_trace (List.tl (Array.to_list Sys.argv))
    |> List.map (fun (site, pairs) -> (site, List.sort_uniq compare pairs))
  in
  let sizes = List.map (fun (_, e) -> List.length e) relations in
  let vertices = List.map (fun (_, e) -> List.length (nodes e)) relations in
    Printf.printf
      "%d relations; edges p50 %d p95 %d max %d; nodes p50 %d p95 %d max %d\n"
      (List.length relations) (percentile 50 sizes) (percentile 95 sizes)
      (percentile 100 sizes) (percentile 50 vertices) (percentile 95 vertices)
      (percentile 100 vertices);
    let by_site = Hashtbl.create 8 in
      List.iter
        (fun (site, e) ->
          let n, m =
            Hashtbl.find_opt by_site site |> Option.value ~default:(0, 0)
          in
            Hashtbl.replace by_site site (n + 1, max m (List.length e))
        )
        relations;
      Hashtbl.iter
        (fun site (n, m) ->
          Printf.printf "  %-60s %7d calls, max %d edges\n" site n m
        )
        by_site;
      (* from scratch *)
      let closure = ref 0. and dfs = ref 0. and disagree = ref 0 in
        List.iter
          (fun (_, e) ->
            let a, ta = time (fun () -> URelation.acyclic (USet.of_list e)) in
            let b, tb = time (fun () -> dfs_of_edges e) in
              closure := !closure +. ta;
              dfs := !dfs +. tb;
              if a <> b then incr disagree
          )
          relations;
        Printf.printf
          "from scratch: URelation.acyclic %.3fs, dfs %.3fs (%.0fx), disagree %d\n"
          !closure !dfs (!closure /. !dfs) !disagree;
        (* merges *)
        List.iter
          (fun k ->
            let results =
              List.map
                (fun strategy ->
                  let t = ref 0. and answers = ref [] in
                    List.iteri
                      (fun i (_, e) ->
                        let r, dt =
                          time (fun () -> first_cycle ~k strategy (shuffle i e))
                        in
                          t := !t +. dt;
                          answers := r :: !answers
                      )
                      relations;
                    (strategy, !t, !answers)
                )
                [ `Dfs; `Bounded; `Pk ]
            in
            let _, _, reference = List.hd results in
              Printf.printf "merges of %3d edges:" k;
              List.iter
                (fun (strategy, t, answers) ->
                  Printf.printf "  %s %.3fs%s"
                    ( match strategy with
                    | `Dfs -> "dfs"
                    | `Bounded -> "bounded"
                    | `Pk -> "pk"
                    )
                    t
                    (if answers = reference then "" else " (DISAGREES)")
                )
                results;
              print_newline ()
          )
          [ 1; 8; 64 ]
