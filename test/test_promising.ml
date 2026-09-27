(** Tests for the promising semantics, PS1.0 and PS2.0.

    The verdicts are the papers' own: Kang et al., POPL 2017 (sections 1-4)
    and Lee et al., PLDI 2020 (section 4). Each program runs through the same
    pipeline as sMRD's, with {!Semantics.step_calculate_executions} choosing
    the semantics. *)

open Alcotest
open Context
open Types
open Uset

let versions = [ ("PS1.0", Promising1); ("PS2.0", Promising2) ]

(** [run semantics source] is the context after the full pipeline. *)
let run semantics source =
  let ctx = make_context { default_options with semantics } () in
    ctx.litmus_name <- "test";
    ctx.litmus <- Some source;
    Lwt_main.run
      (Lwt.return ctx
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Semantics.step_calculate_executions
      |> Assertion.step_check_assertions
      )

(** The value [ctx]'s executions end with for [name], one per execution. *)
let finals ctx names =
  USet.values (Option.get ctx.executions)
  |> List.map (fun (ex : symbolic_execution) ->
      List.map
        (fun n ->
          match Hashtbl.find_opt ex.final_env n with
          | Some (ENum z) -> Z.to_int z
          | _ -> fail (n ^ " has no integer final value")
        )
        names
  )
  |> List.sort_uniq compare

let valid ctx = Option.get ctx.valid

(** A litmus test whose assertion holds under both versions. *)
let holds_under_both name source =
  test_case name `Quick (fun () ->
      List.iter
        (fun (v, semantics) ->
          check bool (name ^ " under " ^ v) true (valid (run semantics source))
        )
        versions
  )

let sb =
  {|x := 0; y := 0;
{ x := 1; r1 := y } ||| { y := 1; r2 := x }
%%
allow (r1 = 0 && r2 = 0) [Promising]|}

(** Store buffering: every combination, including both reading 0. *)
let test_sb_outcomes () =
  List.iter
    (fun (v, semantics) ->
      check
        (list (list int))
        ("SB under " ^ v)
        [ [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ]; [ 1; 1 ] ]
        (finals (run semantics sb) [ "r1"; "r2" ])
    )
    versions

(** Load buffering is allowed by promising [y := 1], but out-of-thin-air --
    the promise [y := r1] of LBd -- cannot be certified. *)
let test_lb_outcomes () =
  let lb store =
    Printf.sprintf
      {|x := 0; y := 0;
{ r1 := x; y := %s } ||| { r2 := y; x := r2 }
%%%%
allow (r1 = 1) [Promising]|}
      store
  in
    List.iter
      (fun (v, semantics) ->
        check
          (list (list int))
          ("LB under " ^ v)
          [ [ 0; 0 ]; [ 0; 1 ]; [ 1; 1 ] ]
          (finals (run semantics (lb "1")) [ "r1"; "r2" ]);
        check
          (list (list int))
          ("LBd under " ^ v)
          [ [ 0; 0 ] ]
          (finals (run semantics (lb "r1")) [ "r1"; "r2" ]);
        check bool ("LBfd under " ^ v) true
          (valid (run semantics (lb "r1 + 1 - r1")))
      )
      versions

(** The final value of a location is its last write in timestamp order. *)
let test_final_memory () =
  List.iter
    (fun (v, semantics) ->
      check
        (list (list int))
        ("2+2W under " ^ v)
        [ [ 1; 1 ]; [ 1; 2 ]; [ 2; 1 ]; [ 2; 2 ] ]
        (finals
           (run semantics
              {|x := 0; y := 0;
{ x := 1; y := 2 } ||| { y := 1; x := 2 }
%%
allow (x = 2 && y = 2) [Promising]|}
           )
           [ "x"; "y" ]
        )
    )
    versions

(** An update's write is adjacent to the message it reads: two increments
    cannot both read 0. *)
let test_par_inc () =
  List.iter
    (fun (v, semantics) ->
      check
        (list (list int))
        ("Par-Inc under " ^ v)
        [ [ 0; 1 ]; [ 1; 0 ] ]
        (finals
           (run semantics
              {|x := 0;
{ rp := &x; r1 := FADD(rlx, rlx, rp, 1) } ||| { rq := &x; r2 := FADD(rlx, rlx, rq, 1) }
%%
allow (r1 = 1) [Promising]|}
           )
           [ "r1"; "r2" ]
        )
    )
    versions

(** POPL 2017, section 3: allowed, by first promising the update to [z]
    attached to the message it reads. *)
let upd_stuck =
  {|x := 0; y := 0; z := 0;
{ r1 := x; rpz := &z; r2 := FADD(rlx, rlx, rpz, 1); y := r2 + 1 }
||| { r3 := y; x := r3 }
||| { rqz := &z; r4 := FADD(rlx, rlx, rqz, 1) }
%%
allow (r1 = 1 && r2 = 0) [Promising]|}

(** PLDI 2020, section 4.2, RPacq: PS2.0 allows the outcome by reserving the
    slot the acquire update reads into; PS1.0, which has no reservations and
    whose certification reads caps with the maximal view, does not. *)
let rpacq =
  {|x := 0; y := 0; z := 0;
{ ra := x; rpz := &z; rc := FADD(acq, rlx, rpz, ra); y := 1 }
||| { rb := y; x := rb }
%%
allow (ra = 1 && rc = 0) [Promising]|}

let test_rpacq_separates () =
  check bool "RPacq under PS1.0" false (valid (run Promising1 rpacq));
  check bool "RPacq under PS2.0" true (valid (run Promising2 rpacq))

(** The model name asks for promising semantics, and sMRD cannot answer it. *)
let test_model_name () =
  match run Smrd sb with
  | _ -> fail "sMRD accepted a [Promising] assertion"
  | exception Failure msg ->
      check bool "the error names --semantics" true
        (Test_zoo_models.contains msg "--semantics")

(** The same program runs under sMRD through the same step. *)
let test_smrd_unchanged () =
  let ctx =
    run Smrd
      {|x := 0; y := 0;
{ x := 1; r1 := y } ||| { y := 1; r2 := x }
%%
allow (r1 = 0 && r2 = 0) [smrd]|}
  in
    check bool "SB under sMRD" true (valid ctx);
    check bool "sMRD computed justifications" true
      (Option.is_some ctx.justifications)

let test_parse_semantics () =
  check bool "ps1" true (parse_semantics "PS1" = Promising1);
  check bool "promising2" true (parse_semantics "promising2" = Promising2);
  check bool "smrd" true (parse_semantics "smrd" = Smrd);
  check_raises "unknown"
    (Invalid_argument "unknown semantics \"ps3\" (expected smrd, ps1 or ps2)")
    (fun () -> ignore (parse_semantics "ps3"))

(** A null dereference is undefined behaviour, reported as such: [forbid (ub)]
    fails and [allow (ub)] holds. An aborted run has no final state, so it
    witnesses no outcome. *)
let test_undefined_behaviour () =
  let null condition =
    Printf.sprintf
      {|x := 0;
{ r1 := 5; rp := x; r2 := *rp } ||| { x := 0 }
%%%%
%s [Promising]|}
      condition
  in
    List.iter
      (fun (v, semantics) ->
        let ctx = run semantics (null "forbid (ub)") in
          check bool ("forbid (ub) under " ^ v) false (valid ctx);
          check (option bool) ("UB reported under " ^ v) (Some true)
            ctx.undefined_behaviour;
          check bool ("allow (ub) under " ^ v) true
            (valid (run semantics (null "allow (ub)")));
          check bool ("no final state under " ^ v) false
            (valid (run semantics (null "allow (r1 = 5)")))
      )
      versions

(** PS2.0 certifies a promise through an abort -- here dividing by the 0 the
    cap holds -- since an abort stands for any behaviour. PS1.0 has to certify
    for every cap value, 0 among them, and has no aborts. *)
let abort_certifies =
  {|x := 0; y := 0;
{ r1 := x; r2 := 1 / r1; y := 1 } ||| { r3 := y; x := r3 }
%%
allow (r1 = 1 && r3 = 1) [Promising]|}

let test_abort_certifies () =
  check bool "abort certifies under PS1.0" false
    (valid (run Promising1 abort_certifies));
  check bool "abort certifies under PS2.0" true
    (valid (run Promising2 abort_certifies))

let suite =
  ( "Promising",
    [
      test_case "store buffering" `Quick test_sb_outcomes;
      test_case "load buffering and thin air" `Quick test_lb_outcomes;
      test_case "final memory" `Quick test_final_memory;
      test_case "update atomicity" `Quick test_par_inc;
      holds_under_both "SB+fences"
        {|x := 0; y := 0;
{ x := 1; fence(sc); r1 := y } ||| { y := 1; fence(sc); r2 := x }
%%
forbid (r1 = 0 && r2 = 0) [Promising]|};
      holds_under_both "MP+fences"
        {|x := 0; y := 0;
{ x := 1; fence(rel); y := 1 } ||| { r1 := y; fence(acq); r2 := x }
%%
forbid (r1 = 1 && r2 = 0) [Promising]|};
      holds_under_both "MP without fences"
        {|x := 0; y := 0;
{ x := 1; y := 1 } ||| { r1 := y; r2 := x }
%%
allow (r1 = 1 && r2 = 0) [Promising]|};
      holds_under_both "LBr: no promise over a release write"
        {|x := 0; y := 0;
{ r1 := x; y.store(1, rel) } ||| { r2 := y; x := r2 }
%%
forbid (r1 = 1) [Promising]|};
      holds_under_both "LBa: promises over acquire reads"
        {|x := 0; y := 0;
{ r1 := x.load(acq); y := 1 } ||| { r2 := y; x := r2 }
%%
allow (r1 = 1) [Promising]|};
      holds_under_both "release sequence"
        {|x := 0; y := 0;
{ x := 1; y.store(1, rel); y := 2 }
||| { rpy := &y; r1 := FADD(rlx, rlx, rpy, 1) }
||| { r2 := y.load(acq); r3 := x }
%%
forbid (r2 = 3 && r3 = 0) [Promising]|};
      holds_under_both "Upd-Stuck" upd_stuck;
      test_case "RPacq separates the versions" `Quick test_rpacq_separates;
      test_case "undefined behaviour" `Quick test_undefined_behaviour;
      test_case "an abort certifies under PS2.0" `Quick test_abort_certifies;
      test_case "[Promising] needs --semantics" `Quick test_model_name;
      test_case "sMRD through the same step" `Quick test_smrd_unchanged;
      test_case "semantics names" `Quick test_parse_semantics;
    ] )
