(** Coherence checking for memory models *)

open Executions
open Types

(** Cache types *)
type imm_cache = {
  hb : (int * int) uset;
  rf : (int * int) uset;
  rfi : (int * int) uset;
  ar_ : (int * int) uset;
  ex_e : int uset;
  po : (int * int) uset;
  events : (int, event) Hashtbl.t;
  psc_a : (int * int) uset;
  psc_b : (int * int) uset;
  restrict : (int, expr list) Hashtbl.t;
  rmw : (int * int) uset;
  loc_restrict : (int * int) uset -> (int * int) uset;
}

type rc11_cache = {
  sb : (int * int) uset;
  hb : (int * int) uset;
  rfi : (int * int) uset;
  rf : (int * int) uset;
  ex_e : int uset;
  events : (int, event) Hashtbl.t;
  rmw : (int * int) uset;
  loc_restrict : (int * int) uset -> (int * int) uset;
}

type cache =
  | IMMCache of imm_cache
  | RC11Cache of rc11_cache
  | UndefinedCache of {
      rfi : (int * int) uset option;
      rmw : (int * int) uset option;
    }
  | EmptyCache

type restrictions = { coherent : string }

(** Helper: compose relations using semicolon (;) *)
let semicolon_rel (rels : (int * int) uset list) : (int * int) uset =
  match rels with
  | [] -> Uset.create ()
  | [ r ] -> r
  | r :: rest ->
      List.fold_left
        (fun acc rel ->
          let result = Uset.create () in
            Uset.iter
              (fun (a, b) ->
                Uset.iter
                  (fun (c, d) -> if b = c then Uset.add result (a, d) |> ignore)
                  rel
              )
              acc;
            result
        )
        r rest

(** Helper: create identity relation for events matching criteria *)
let em (events : (int, event) Hashtbl.t) (e : int uset) (typ : event_type)
    (mode_opt : mode option) (op_opt : string option)
    (second_mode_opt : mode option) : (int * int) uset =
  let result = Uset.create () in
    Uset.iter
      (fun ev_id ->
        try
          let event = Hashtbl.find events ev_id in
          let type_match = event.typ = typ in
          let mode_match =
            match mode_opt with
            | None -> true
            | Some m -> event.rmod = m || event.wmod = m || event.fmod = m
          in
          let second_mode_match =
            match second_mode_opt with
            | None -> true
            | Some m -> (
                match event.strong with
                | Some sm -> sm = m
                | None -> false
              )
          in
            if type_match && mode_match && second_mode_match then
              Uset.add result (ev_id, ev_id) |> ignore
        with Not_found -> ()
      )
      e;
    result

(** IMM coherence cache builder *)
let imm_coherent_cache (execution : symbolic_execution)
    (structure : symbolic_event_structure) (events : (int, event) Hashtbl.t)
    (loc_restrict : (int * int) uset -> (int * int) uset) : imm_cache =
  let ({ ex_e; rf; ex_rmw; _ } : symbolic_execution) = execution in
  let ({ po; restrict; _ } : symbolic_event_structure) = structure in
  let _E = ex_e in

  let rf = Uset.clone rf in
  let po = Uset.clone po in
  let rmw = Uset.clone ex_rmw in

  let thread_internal_restriction x = Uset.intersection x po in
  let thread_external_restriction x = Uset.set_minus x po in

  let w = em events _E Write None None None in

  (* rs = [W];(po ∩ loc);[W] ∪ [W];([po ∩ loc]?;rf;rmw)⁺? *)
  let rs =
    let part1 = semicolon_rel [ w; loc_restrict po; w ] in
    let inner =
      semicolon_rel [ Uset.reflexive_closure _E (loc_restrict po); rf; rmw ]
    in
    let part2 =
      semicolon_rel
        [ w; Uset.reflexive_closure _E (Uset.transitive_closure inner) ]
    in
      Uset.inplace_union part1 part2
  in

  (* release = ([W_rel] ∪ [F_rel];po);rs *)
  let release =
    let w_rel = em events _E Write (Some Release) None None in
    let f_rel_po =
      semicolon_rel [ em events _E Fence (Some Release) (Some ">") None; po ]
    in
      semicolon_rel [ Uset.inplace_union w_rel f_rel_po; rs ]
  in

  (* sw = release;(rf ∩ ¬po ∪ [po ∩ loc]?;(rf \ po));([R_acq] ∪ po;[F_acq]) *)
  let sw =
    let rf_internal = thread_internal_restriction rf in
    let rf_external = thread_external_restriction rf in
    let middle =
      Uset.inplace_union rf_internal
        (semicolon_rel
           [ Uset.reflexive_closure _E (loc_restrict po); rf_external ]
        )
    in
    let r_acq = em events _E Read (Some Acquire) None None in
    let po_f_acq =
      semicolon_rel [ po; em events _E Fence (Some Acquire) (Some ">") None ]
    in
      semicolon_rel [ release; middle; Uset.inplace_union r_acq po_f_acq ]
  in

  (* hb = (sw ∪ po)⁺ *)
  let hb = Uset.transitive_closure (Uset.inplace_union sw po) in

  (* bob (bounded ordered-before) *)
  let bob =
    let p1 =
      semicolon_rel [ po; em events _E Write (Some Release) None None ]
    in
    let p2 = semicolon_rel [ em events _E Read (Some Acquire) None None; po ] in
    let p3 = semicolon_rel [ po; em events _E Fence None None None ] in
    let p4 = semicolon_rel [ em events _E Fence None None None; po ] in
    let p5 =
      semicolon_rel
        [
          em events _E Write (Some Release) None None;
          loc_restrict po;
          em events _E Write None None None;
        ]
    in
      Uset.union p1 p2
      |> Uset.inplace_union p3
      |> Uset.inplace_union p4
      |> Uset.inplace_union p5
  in

  let deps = execution.dp in

  (* ppo = [R];(rf ∩ ¬po ∪ deps)⁺;[W] *)
  let ppo =
    let r = em events _E Read None None None in
    let w = em events _E Write None None None in
    let middle =
      Uset.transitive_closure
        (Uset.inplace_union (thread_internal_restriction rf) deps)
    in
      semicolon_rel [ r; middle; w ]
  in

  (* strong_ = [W_strong];po;[W] *)
  let strong_ =
    semicolon_rel
      [
        em events _E Write None None (Some Strong);
        po;
        em events _E Write None None None;
      ]
  in

  (* ar_ = (rf \ po) ∪ bob ∪ ppo ∪ strong_ *)
  let ar_ =
    thread_external_restriction rf
    |> Uset.inplace_union bob
    |> Uset.inplace_union ppo
    |> Uset.inplace_union strong_
  in

  (* psc_a = [F_sc];hb *)
  let psc_a = semicolon_rel [ em events _E Fence (Some SC) None None; hb ] in

  (* psc_b = hb;[F_sc] *)
  let psc_b = semicolon_rel [ hb; em events _E Fence (Some SC) None None ] in

  {
    hb;
    rf;
    rfi = Uset.inverse_relation rf;
    ar_;
    ex_e;
    po;
    events;
    psc_a;
    psc_b;
    restrict;
    rmw;
    loc_restrict;
  }

(** IMM coherence checker *)
let imm_coherent (co : (int * int) uset) (cache : imm_cache) : bool =
  let { hb; rfi; po; rf; ar_; psc_a; psc_b; rmw; _ } = cache in

  let thread_external_restriction x = Uset.set_minus x po in

  (* fr = rf⁻¹;co *)
  let fr = semicolon_rel [ rfi; co ] in

  (* eco = rf ∪ co;rf ∪ co ∪ fr;rf ∪ fr *)
  let eco =
    Uset.union rf (semicolon_rel [ co; rf ])
    |> Uset.inplace_union co
    |> Uset.inplace_union (semicolon_rel [ fr; rf ])
    |> Uset.inplace_union fr
  in

  (* Coherence: hb;eco ∪ hb is irreflexive *)
  if
    not (Uset.is_irreflexive (Uset.inplace_union (semicolon_rel [ hb; eco ]) hb))
  then false
  else
    (* Thin-air *)
    let coe = thread_external_restriction co in
    let detour =
      Uset.intersection
        (semicolon_rel [ coe; thread_external_restriction rf ])
        po
    in
    let psc = semicolon_rel [ psc_a; eco; psc_b ] in
    let ar = Uset.union ar_ psc |> Uset.inplace_union detour in

    if not (Uset.acyclic ar) then false
    else if
      (* Atomicity *)
      Uset.size rmw = 0
    then true
    else
      (* rmw ∩ (fre;coe) = ∅ *)
      Uset.size
        (Uset.intersection rmw
           (semicolon_rel [ thread_external_restriction fr; coe ])
        )
      = 0

(** RC11 coherence cache builder *)
let rc11_coherent_cache (execution : symbolic_execution)
    (structure : symbolic_event_structure) (events : (int, event) Hashtbl.t)
    (loc_restrict : (int * int) uset -> (int * int) uset) : rc11_cache =
  let ({ ex_e; rf; ex_rmw; _ } : symbolic_execution) = execution in
  let ({ po; _ } : symbolic_event_structure) = structure in
  let _E = ex_e in

  let rf = Uset.clone rf in
  let rmw = Uset.clone ex_rmw in
  let sb = Uset.clone po in

  (* rs = [W];[po ∩ loc]?;[W_rlx⁺];(rf;rmw)⁺? *)
  let rs =
    let w = em events _E Write None None None in
    let w_rlx = em events _E Write (Some Relaxed) (Some ">") None in
    let inner = Uset.transitive_closure (semicolon_rel [ rf; rmw ]) in
      semicolon_rel
        [
          w;
          Uset.reflexive_closure _E (loc_restrict sb);
          w_rlx;
          Uset.reflexive_closure _E inner;
        ]
  in

  (* TODO check against spec *)
  (* sw = [R_rel⁺ ∪ W_rel⁺ ∪ F_rel⁺];([F];sb)?;rs;rf;[R_rlx⁺];(sb;[F])?;[R_acq⁺ ∪ W_acq⁺ ∪ F_acq⁺] *)
  let sw =
    let rel =
      Uset.union
        (em events _E Read (Some Release) (Some ">") None)
        (em events _E Write (Some Release) (Some ">") None)
      |> Uset.inplace_union (em events _E Fence (Some Release) (Some ">") None)
    in
    let fence_sb =
      Uset.reflexive_closure _E
        (semicolon_rel [ em events _E Fence None None None; sb ])
    in
    let r_rlx = em events _E Read (Some Relaxed) (Some ">") None in
    let sb_fence =
      Uset.reflexive_closure _E
        (semicolon_rel [ sb; em events _E Fence None None None ])
    in
    let acq =
      Uset.union
        (em events _E Read (Some Acquire) (Some ">") None)
        (em events _E Write (Some Acquire) (Some ">") None)
      |> Uset.inplace_union (em events _E Fence (Some Acquire) (Some ">") None)
    in
      semicolon_rel [ rel; fence_sb; rs; rf; r_rlx; sb_fence; acq ]
  in

  (* hb = (sw ∪ sb)⁺ *)
  let hb = Uset.transitive_closure (Uset.inplace_union sw sb) in

  {
    sb;
    hb;
    rfi = Uset.inverse_relation rf;
    rf;
    ex_e;
    events;
    rmw;
    loc_restrict;
  }

(** RC11 coherence checker *)
let rc11_coherent (co : (int * int) uset) (cache : rc11_cache) : bool =
  let { sb; hb; rfi; rf; ex_e; events; rmw; loc_restrict } = cache in
  let _E = ex_e in

  (* rb = rf⁻¹;co *)
  let rb = semicolon_rel [ rfi; co ] in

  (* eco = (rf ∪ co ∪ rb)⁺ *)
  let eco =
    Uset.transitive_closure (Uset.union rf co |> Uset.inplace_union rb)
  in

  (* Atomicity: rmw ∩ (rb;co) = ∅ *)
  if Uset.size rmw <> 0 then
    if Uset.size (Uset.intersection rmw (semicolon_rel [ rb; co ])) <> 0 then
      false
    else if
      (* Coherence: hb;eco ∪ hb is irreflexive *)
      not
        (Uset.is_irreflexive (Uset.inplace_union (semicolon_rel [ hb; eco ]) hb))
    then false
    else
      (* SC consistency *)
      let sb_non_loc = Uset.set_minus sb (loc_restrict sb) in
      let scb =
        Uset.union sb (semicolon_rel [ sb_non_loc; hb ])
        |> Uset.union (loc_restrict hb)
        |> Uset.union co
        |> Uset.union rb
      in

      let sc_events = em events _E Init (Some SC) None None in
      let f_sc = em events _E Fence (Some SC) None None in

      let psc_base =
        semicolon_rel
          [
            Uset.inplace_union sc_events
              (semicolon_rel [ f_sc; Uset.reflexive_closure _E hb ]);
            scb;
            Uset.inplace_union sc_events
              (semicolon_rel [ Uset.reflexive_closure _E hb; f_sc ]);
          ]
      in

      let psc_f =
        semicolon_rel
          [ f_sc; Uset.inplace_union (semicolon_rel [ hb; eco; hb ]) hb; f_sc ]
      in

      let psc = Uset.union psc_base psc_f in
        Uset.acyclic psc
  else if
    (* No RMW operations, just check coherence *)
    not (Uset.is_irreflexive (Uset.inplace_union (semicolon_rel [ hb; eco ]) hb))
  then false
  else
    let sb_non_loc = Uset.set_minus sb (loc_restrict sb) in
    let scb =
      Uset.union sb (semicolon_rel [ sb_non_loc; hb ])
      |> Uset.union (loc_restrict hb)
      |> Uset.union co
      |> Uset.union rb
    in

    let sc_events = em events _E Init (Some SC) None None in
    let f_sc = em events _E Fence (Some SC) None None in

    let psc_base =
      semicolon_rel
        [
          Uset.inplace_union sc_events
            (semicolon_rel [ f_sc; Uset.reflexive_closure _E hb ]);
          scb;
          Uset.inplace_union sc_events
            (semicolon_rel [ Uset.reflexive_closure _E hb; f_sc ]);
        ]
    in

    let psc_f =
      semicolon_rel
        [ f_sc; Uset.inplace_union (semicolon_rel [ hb; eco; hb ]) hb; f_sc ]
    in

    let psc = Uset.union psc_base psc_f in
      Uset.acyclic psc

(** IMM dependency calculation *)
let imm_deps (execution : symbolic_execution) (events : (int, event) Hashtbl.t)
    (po : (int * int) uset) (e : int uset)
    (restrict : (int, expr list) Hashtbl.t) : (int * int) uset =
  (* data = [R];po;[W] where wval references rval *)
  let data =
    let r_w =
      semicolon_rel
        [
          em events e Read None None None; po; em events e Write None None None;
        ]
    in
      Uset.filter
        (fun (from_id, to_id) ->
          try
            let from_ev = Hashtbl.find events from_id in
            let to_ev = Hashtbl.find events to_id in
              match (from_ev.rval, to_ev.wval) with
              | Some rv, Some wv ->
                  (* Simple structural equality or symbol dependency check *)
                  Uset.value_equality rv wv
              | _ -> false
          with Not_found -> false
        )
        r_w
  in

  (* ctrl = [R];po where restrict differs *)
  let ctrl =
    let r_po = semicolon_rel [ em events e Read None None None; po ] in
      Uset.filter
        (fun (from_id, to_id) ->
          try
            let from_restrict = Hashtbl.find restrict from_id in
            let to_restrict = Hashtbl.find restrict to_id in
              from_restrict <> to_restrict
          with Not_found -> false
        )
        r_po
  in

  let addr = Uset.create () in
  let casdep = Uset.create () in
  let rex = Uset.create () in

  (* data ∪ ctrl ∪ addr;po? ∪ addr ∪ casdep ∪ [Rex];po *)
  data
  |> Uset.inplace_union ctrl
  |> Uset.inplace_union (semicolon_rel [ addr; po ])
  |> Uset.inplace_union addr
  |> Uset.inplace_union casdep
  |> Uset.inplace_union (semicolon_rel [ rex; po ])

(** Generate all permutations of a list *)
let rec permutations = function
  | [] -> [ [] ]
  | x :: xs ->
      let perms = permutations xs in
        List.concat
          (List.map
             (fun perm ->
               let rec insert_at_all_positions acc = function
                 | [] -> [ List.rev (x :: acc) ]
                 | y :: ys as rest ->
                     (List.rev acc @ (x :: rest))
                     :: insert_at_all_positions (y :: acc) ys
               in
                 insert_at_all_positions [] perm
             )
             perms
          )

(** Main coherence checking function *)
let check_for_coherence (structure : symbolic_event_structure)
    (events : (int, event) Hashtbl.t) (execution : symbolic_execution)
    (restrictions : restrictions) (include_dependencies : bool) : bool Lwt.t =
  if execution.ex_e = Uset.create () then Lwt.return false
  else
    let ({ po; restrict; _ } : symbolic_event_structure) = structure in
    let writes =
      Uset.filter
        (fun ev_id ->
          try
            let event = Hashtbl.find events ev_id in
              event.typ = Write
          with Not_found -> false
        )
        execution.ex_e
    in

    if Uset.size writes < 2 then Lwt.return true
    else
      (* Create location equivalence relation using semantic equality *)
      let%lwt eqlocs =
        let all_events = execution.ex_e in
          Uset.async_filter
            (fun (a, b) ->
              if a = b then Lwt.return true
              else
                try
                  let ev_a = Hashtbl.find events a in
                  let ev_b = Hashtbl.find events b in
                    match (ev_a.id, ev_b.id) with
                    | Some id_a, Some id_b ->
                        (* Use solver to check semantic equality *)
                        Solver.Semeq.exeq_value
                          (Solver.Semeq.create_state ())
                          id_a id_b
                    | _ -> Lwt.return false
                with Not_found -> Lwt.return false
            )
            (Uset.cross all_events all_events
            |> Uset.filter (fun (a, b) -> a <= b)
            )
      in
      let eqlocs = Uset.inplace_union eqlocs (Uset.inverse_relation eqlocs) in

      let loc_restrict x =
        Uset.filter (fun (a, b) -> Uset.mem eqlocs (a, b)) x
      in

      (* Check if reads from init *)
      let reads_from_init =
        Uset.exists (fun (_, to_id) -> to_id = 0) execution.rf
      in

      (* Group writes by location *)
      let writes_per_location =
        let groups = ref [] in
          Uset.iter
            (fun w ->
              let found = ref false in
                List.iter
                  (fun group ->
                    if Uset.mem eqlocs (List.hd !group, w) then (
                      (* Add ! here *)
                      group := w :: !group;
                      found := true
                    )
                  )
                  !groups;
                if not !found then
                  groups :=
                    ref (if reads_from_init then [ w; 0 ] else [ w ]) :: !groups
            )
            writes;
          List.filter (fun g -> List.length !g > 1) !groups
          |> List.map (fun g ->
                 let perms = permutations !g in
                   List.map
                     (fun perm ->
                       let rec to_pairs acc = function
                         | [] | [ _ ] -> List.rev acc
                         | x :: (y :: _ as rest) ->
                             to_pairs ((x, y) :: acc) rest
                       in
                         to_pairs [] perm
                     )
                     perms
             )
      in

      (* Build cache based on memory model *)
      (* Build cache based on memory model *)
      let cache_result, deps_fn, thin_fn, coherent_fn =
        match restrictions.coherent with
        | "imm" -> (
            let cache =
              imm_coherent_cache execution structure events loc_restrict
            in
              ( IMMCache cache,
                imm_deps,
                (fun _ _ -> true),
                (* thin_fn *)
                fun co c ->
                  match c with
                  | IMMCache cache -> imm_coherent co cache
                  | _ -> false
              )
          )
        | "rc11" | "rc11c" -> (
            let cache =
              rc11_coherent_cache execution structure events loc_restrict
            in
            let thin =
              if restrictions.coherent = "rc11" then
                fun (exec : symbolic_execution) (c : cache) ->
                match c with
                | RC11Cache cache -> Uset.acyclic (Uset.union cache.sb exec.rf)
                | _ -> true
              else fun _ _ -> true
            in
              ( RC11Cache cache,
                (fun _ _ _ _ _ -> Uset.create ()),
                thin,
                (* Already has the right type: symbolic_execution -> cache -> bool *)
                fun co c ->
                  match c with
                  | RC11Cache cache -> rc11_coherent co cache
                  | _ -> false
              )
          )
        | _ ->
            let cache =
              if Uset.size execution.ex_rmw > 0 then
                UndefinedCache
                  {
                    rfi = Some (Uset.inverse_relation execution.rf);
                    rmw = Some execution.ex_rmw;
                  }
              else UndefinedCache { rfi = None; rmw = None }
            in
            let coherent co cache =
              match cache with
              | UndefinedCache { rfi = Some rfi; rmw = Some rmw } ->
                  let fr = semicolon_rel [ rfi; co ] in
                    Uset.size (Uset.intersection rmw (semicolon_rel [ fr; co ]))
                    = 0
              | _ -> true
            in
              ( cache,
                (fun _ _ _ _ _ -> Uset.create ()),
                (fun _ _ -> true),
                coherent (* This one already has the right type *)
              )
      in

      (* Compute dependencies if needed *)
      let execution =
        if not include_dependencies then
          match cache_result with
          | IMMCache c ->
              {
                execution with
                dp = deps_fn execution events po structure.e restrict;
              }
          | RC11Cache c ->
              {
                execution with
                dp = deps_fn execution events po structure.e restrict;
              }
          | _ -> execution
        else execution
      in

      (* Check thin-air *)
      if (not include_dependencies) && not (thin_fn execution cache_result) then
        Lwt.return false
      else
        (* Try all coherence orders *)
        let rec try_all_orders = function
          | [] -> Lwt.return true
          | co_list :: rest ->
              let co = Uset.transitive_closure (Uset.of_list co_list) in
                if coherent_fn co cache_result then try_all_orders rest
                else Lwt.return false
        in

        let rec choose_one i vals =
          if i < 0 then
            let co = Uset.transitive_closure (Uset.of_list vals) in
              Lwt.return (coherent_fn co cache_result)
          else
            let rec try_perms = function
              | [] -> Lwt.return false
              | p :: ps ->
                  let%lwt result = choose_one (i - 1) (vals @ p) in
                    if result then Lwt.return true else try_perms ps
            in
              try_perms (List.nth writes_per_location i)
        in

        choose_one (List.length writes_per_location - 1) []
