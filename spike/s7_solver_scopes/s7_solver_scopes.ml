(* S7 (#19): replay a stream of satisfiability queries, as the pipeline asked
   them (Solver.S7), against ways of asking Z3.

   - fresh:        today's. Sorted and deduplicated, the cache first, and on a
                   miss the syntactic shortcuts, then a fresh Z3 solver.
   - pushpop:      the cache and the shortcuts, then one long-lived Z3 solver,
                   the query pushed, checked and popped.
   - pushpop-raw:  as pushpop, without the shortcuts.
   - prefix:       the cache and the shortcuts, then one long-lived solver that
                   keeps what consecutive queries share. The query in the order
                   its caller built it: the stack is popped back to the longest
                   prefix it shares with the last one, and the rest pushed one
                   assertion at a time.
   - fresh-nocache: fresh, with no cache; only with S7_NOCACHE set, since it
                   is slow on a large trace.
   - fresh again:  fresh, last, to show how much a warm Z3 context is worth.

   The cache is this harness's, the same for every strategy, keyed on the
   sorted conjunction's rendering. *)

open Expr

let read_trace path : Solver.S7.record list =
  let ic = open_in_bin path in
  let rec go acc =
    match (Marshal.from_channel ic : Solver.S7.record) with
    | r -> go (r :: acc)
    | exception End_of_file ->
        close_in ic;
        List.rev acc
  in
    go []

let dedup exprs =
  List.fold_left
    (fun acc e -> if List.exists (Expr.equal e) acc then acc else e :: acc)
    [] exprs
  |> List.rev

let sorted exprs = List.sort_uniq Expr.compare exprs
let key exprs = String.concat "\x00" (List.map Expr.to_string exprs)

type stats = {
  mutable z3 : int;
  mutable misses : int;
  time_by_site : (string, float) Hashtbl.t;
}

let with_cache ~cache f exprs =
  let k = key (sorted exprs) in
    match Hashtbl.find_opt cache k with
    | Some r -> (r, false)
    | None ->
        let r = f exprs in
          Hashtbl.replace cache k r;
          (r, true)

let fresh st exprs =
  let exprs = sorted exprs in
    match Solver.trivially exprs with
    | Some r -> Some r
    | None ->
        st.z3 <- st.z3 + 1;
        Solver.check (Solver.create exprs)

let pushpop ~shortcuts solver st exprs =
  let exprs = sorted exprs in
    match if shortcuts then Solver.trivially exprs else None with
    | Some r -> Some r
    | None ->
        st.z3 <- st.z3 + 1;
        ignore (Solver.push solver);
        ignore (Solver.add_assertions solver exprs);
        let r = Solver.check_asserted solver in
          ignore (Solver.pop solver);
          r

let prefix solver stack st exprs =
  match Solver.trivially (sorted exprs) with
  | Some r -> Some r
  | None ->
      st.z3 <- st.z3 + 1;
      let exprs = dedup exprs in
      let rec common n a b =
        match (a, b) with
        | x :: a', y :: b' when Expr.equal x y -> common (n + 1) a' b'
        | _ -> n
      in
      let shared = common 0 !stack exprs in
        for _ = 1 to List.length !stack - shared do
          ignore (Solver.pop solver)
        done;
        let rest = List.filteri (fun i _ -> i >= shared) exprs in
          List.iter
            (fun e ->
              ignore (Solver.push solver);
              ignore (Solver.add_assertions solver [ e ])
            )
            rest;
          stack := exprs;
          Solver.check_asserted solver

let run name ~cached ask (trace : Solver.S7.record list) =
  let st = { z3 = 0; misses = 0; time_by_site = Hashtbl.create 8 } in
  let cache = Hashtbl.create 4096 in
  let t0 = Unix.gettimeofday () in
  let answers =
    List.map
      (fun (r : Solver.S7.record) ->
        let t = Unix.gettimeofday () in
        let answer, miss =
          if cached then with_cache ~cache (ask st) r.exprs
          else (ask st r.exprs, true)
        in
          if miss then st.misses <- st.misses + 1;
          let dt = Unix.gettimeofday () -. t in
            Hashtbl.replace st.time_by_site r.site
              (dt
              +. (Hashtbl.find_opt st.time_by_site r.site
                 |> Option.value ~default:0.
                 )
              );
            answer
      )
      trace
  in
    (name, Unix.gettimeofday () -. t0, st, answers)

let () =
  let traces = List.tl (Array.to_list Sys.argv) in
    List.iter
      (fun path ->
        let trace = read_trace path in
        let long_lived () = Solver.create [] in
        let results =
          [
            run "fresh" ~cached:true fresh trace;
            (let s = long_lived () in
               run "pushpop" ~cached:true (pushpop ~shortcuts:true s) trace
            );
            (let s = long_lived () in
               run "pushpop-raw" ~cached:true (pushpop ~shortcuts:false s) trace
            );
            (let s = long_lived () and stack = ref [] in
               run "prefix" ~cached:true (prefix s stack) trace
            );
          ]
          @ ( if Sys.getenv_opt "S7_NOCACHE" = None then []
              else [ run "fresh-nocache" ~cached:false fresh trace ]
            )
          @ [ run "fresh-again" ~cached:true fresh trace ]
        in
        let _, _, _, reference = List.hd results in
        let hits_in_run =
          List.length (List.filter (fun (r : Solver.S7.record) -> r.hit) trace)
        in
          Printf.printf
            "== %s: %d queries, %d answered by the pipeline's cache\n"
            (Filename.basename path) (List.length trace) hits_in_run;
          List.iter
            (fun (name, t, st, answers) ->
              let disagree =
                List.fold_left2
                  (fun n a b -> if a = b then n else n + 1)
                  0 reference answers
              in
                Printf.printf
                  "  %-14s %8.3fs  misses %7d  z3 %7d  disagree %d\n" name t
                  st.misses st.z3 disagree
            )
            results;
          (* per site, for the two that matter *)
          let site_times name =
            let _, _, st, _ =
              List.find (fun (n, _, _, _) -> n = name) results
            in
              st.time_by_site
          in
          let f = site_times "fresh-again" and p = site_times "pushpop" in
          let sites =
            Hashtbl.fold (fun k v acc -> (k, v) :: acc) f []
            |> List.sort (fun (_, a) (_, b) -> compare b a)
          in
          let count site =
            List.length
              (List.filter (fun (r : Solver.S7.record) -> r.site = site) trace)
          in
            List.iter
              (fun (site, tf) ->
                Printf.printf
                  "    %-50s %7d queries  fresh %7.3fs  pushpop %7.3fs\n" site
                  (count site) tf
                  (Hashtbl.find_opt p site |> Option.value ~default:0.)
              )
              sites
      )
      traces
