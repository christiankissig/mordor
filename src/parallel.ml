(** Chunked dispatch of pure work onto a domain pool.

    [Lwt_domain.detach] is not a cheap call. Each one allocates a one-shot
    [Lwt_unix] notification, submits a task to the pool, and costs a self-pipe
    write plus a wakeup of the main loop when the task finishes; domainslib's
    workers spin some thousands of times before sleeping on a condition
    variable, so a stream of short tasks makes them sleep and wake once per
    item. Dispatching per item -- one detach per justification, path or
    execution -- paid all of that thousands of times per stage, for items that
    are often decided syntactically in no time at all.

    So work is dispatched in chunks. The pool sees a few dozen tasks per stage
    rather than thousands, while each task still holds enough items to be worth
    waking a domain for. On seqlock-1, best of three: 1.27s to 1.03s at
    [--threads 4], 1.42s to 1.16s at [--threads 8].

    It is worth being clear about what this does not fix. The futex traffic
    that a parallel run spends most of its syscall time in barely moved, 14573
    calls to 14776, so that time is contention on the shared caches -- the one
    mutex in {!Forwarding}'s PPO cache and {!Solver}'s conjunction cache -- and
    not task dispatch. Parallel runs are now about level with sequential rather
    than slower than it; making them actually faster is that contention's to
    give. *)

open Lwt.Syntax

(** Chunks per domain to aim for. More than one, because the items here differ
    wildly in cost -- a justification that needs a solver query against one that
    is decided syntactically -- and a domain that draws a slow chunk should not
    hold up the stage while its neighbours sit idle. Domainslib steals work
    between its queues, so the surplus chunks are what it balances with. *)
let chunks_per_domain = 4

(** [split ~size items] cuts [items] into consecutive runs of at most [size],
    in order. *)
let split ~size items =
  let rec take n taken rest =
    match rest with
    | x :: xs when n > 0 -> take (n - 1) (x :: taken) xs
    | rest -> (List.rev taken, rest)
  in
  let rec loop acc rest =
    match rest with
    | [] -> List.rev acc
    | rest ->
        let chunk, rest = take size [] rest in
          loop (chunk :: acc) rest
  in
    loop [] items

(** [map pool f items] applies [f] to every item on [pool], in chunks, and
    returns the results in the order of [items].

    [f] must be pure enough to run on any domain: it may read shared state, but
    anything it mutates has to be its own or synchronised.

    An item that raises takes its chunk down with it and the failure surfaces
    on the returned promise, so the items after it in that chunk do not run.
    Dispatching per item ran all of them before failing; either way the
    exception reaches the caller, and here it reaches it sooner. *)
(** {1 The pool} *)

(** The pool this process dispatches on, and the thread count it was built for.

    A run used to set up a pool in [Elaborations.batch_elaborations] and
    another in [Executions.calculate_dependencies], and tear each down again.
    Spawning a domain costs a few milliseconds, so a run paid for
    [2 * num_threads] of them before doing any work: on spinlock-1, which has
    no work to speak of, that was the whole runtime, growing with the thread
    count from 0.02s at one to 0.09s at eight. Over a directory of litmus
    tests, which is one process and hundreds of programs, it was paid on every
    one of them.

    One pool, kept for the process, is spawned once however many programs the
    process analyses. It also removes the leak that {!Lwt.finalize} was
    guarding: there is no per-phase teardown left for an exception to skip. *)
let pool_mutex = Mutex.create ()

let pool_in_use : (int * Lwt_domain.pool) option ref = ref None

(** [acquire ~num_threads] is the process's pool, built if this is the first
    call and rebuilt if the thread count has changed since the last one, or
    [None] when [num_threads] is 1 and the caller should stay sequential. *)
let acquire ~num_threads =
  if num_threads <= 1 then None
  else
    Mutex.protect pool_mutex (fun () ->
        match !pool_in_use with
        | Some (n, pool) when n = num_threads -> Some pool
        | existing ->
            Option.iter (fun (_, pool) -> Lwt_domain.teardown_pool pool) existing;
            let pool = Lwt_domain.setup_pool num_threads in
              pool_in_use := Some (num_threads, pool);
              Some pool
    )

(** Handing the domains back at exit rather than leaving the runtime to drop
    them. Nothing depends on this -- a pool left standing does not hold the
    process open -- but a pool that is torn down is one that cannot be holding
    anything when the next thing looks. *)
let () =
  at_exit (fun () ->
      Mutex.protect pool_mutex (fun () ->
          Option.iter (fun (_, pool) -> Lwt_domain.teardown_pool pool) !pool_in_use;
          pool_in_use := None
      )
  )

let map pool f items =
  match items with
  | [] -> Lwt.return []
  | _ ->
      let size =
        let n = List.length items in
        let chunks = Lwt_domain.get_num_domains pool * chunks_per_domain in
          max 1 ((n + chunks - 1) / chunks)
      in
      let promises =
        List.map
          (fun chunk ->
            Lwt_domain.detach pool
              (fun () ->
                match List.map f chunk with
                | results -> results
                | exception exn ->
                    let bt = Printexc.get_raw_backtrace () in
                      Printexc.raise_with_backtrace exn bt
              )
              ()
          )
          (split ~size items)
      in
      let+ results = Lwt.all promises in
        List.concat results
