(** Tests for the zoo's models defined over sMRD's relations as they stand.

    The verdicts each model gives on its separating witnesses are integration
    tests, under [litmus-tests/rmm-zoo/models/]. These check what those cannot:
    that the names resolve, that threads are told apart, that MRD refuses what
    it cannot answer, and that the zoo's ordering edges hold execution by
    execution. *)

open Alcotest
open Context
open Types
open Uset

let contains haystack needle =
  let n = String.length needle and h = String.length haystack in
  let rec go i =
    i + n <= h && (String.sub haystack i n = needle || go (i + 1))
  in
    go 0

(** Every implemented name selects the coherence model of that name. *)
let test_names_resolve () =
  List.iter
    (fun name ->
      ( match get_model_options name with
      | Some { coherent = Some coherent; ubopt = false } ->
          check string (name ^ " selects itself") name coherent
      | _ -> fail (name ^ " is not a model name")
      );
      match Coherence.ModelRegistry.lookup name with
      | Some model ->
          let module M = (val model : Coherence.MEMORY_MODEL) in
          check string (name ^ " is registered under its name") name M.name
      | None -> fail (name ^ " has no coherence model")
    )
    implemented_zoo_models

let parse source =
  let ctx = make_context { default_options with exhaustive = false } () in
    ctx.litmus <- Some source;
    Lwt_main.run (Lwt.return ctx |> Parse.step_parse_litmus)

(** The zoo spells some names with a hyphen, which the lexer has no identifier
    for. *)
let test_hyphenated_names_parse () =
  List.iter
    (fun (spelled, name) ->
      let ctx =
        parse
          (Printf.sprintf
             "x := 0;\n{ x := 1 } ||| { r0 := x }\n%%%%\nallow (r0 = 1) [%s]"
             spelled
          )
      in
        check string spelled name ctx.options.coherent
    )
    [ ("x86-TSO", "x86-tso"); ("OD-LSO", "od-lso"); ("ClightTSO", "clighttso") ]

(** Each thread of a block gets an index of its own, a nested block's threads
    theirs, and the code after a join is back in its parent's thread. The
    parser's [tid] was [0] in every thread body. *)
let test_threads_are_numbered () =
  let ctx =
    parse
      {|x := 0;
{ x := 1; y := 1 } ||| { r1 := y; { r2 := x } ||| { r3 := x }; r4 := y }
%%
allow (r1 = 0) [smrd]|}
  in
  let ctx = Lwt_main.run (Lwt.return ctx |> Interpret.step_interpret) in
  let structure = Option.get ctx.structure in
  (* Labels are allocated in program order: the initialising store, the first
     thread's two stores, then the second thread's four loads. *)
  let accesses =
    Hashtbl.fold
      (fun id (ev : event) acc ->
        if ev.typ = Read || ev.typ = Write then id :: acc else acc
      )
      structure.events []
    |> List.sort compare
    |> List.map (Hashtbl.find_opt structure.thread_index)
  in
    match accesses with
    | [ init; wx; wy; r1; r2; r3; r4 ] ->
        check bool "initialisation is not a thread body" true (init <> wx);
        check (option int) "one thread's events share an index" wx wy;
        check bool "the two threads differ" true (wx <> r1);
        check bool "nested threads differ from their parent" true
          (r2 <> r1 && r3 <> r1);
        check bool "and from each other" true (r2 <> r3);
        check (option int) "the join returns to the parent" r1 r4
    | _ -> fail "expected seven accesses"

let run ?(primary = "smrd") ~others source =
  let ctx =
    make_context
      { default_options with exhaustive = false }
      ~output_mode:Json ()
  in
    ctx.litmus <- Some source;
    Lwt_main.run
      (Lwt.return ctx
      |> Parse.step_parse_litmus
      |> step_select_models ~primary ~others
      |> Interpret.step_interpret
      |> Elaborations.step_generate_justifications
      |> Executions.step_calculate_dependencies
      )

(** MRD is sMRD only where sMRD's extensions have nothing to act on; allocated
    memory is outside that, and the run says so rather than answering as sMRD. A
    pointer to a named global is not: it resolves to the global. *)
let test_mrd_refuses_pointers () =
  match
    run ~primary:"mrd" ~others:[]
      {|rp := malloc(1);
*rp := 0;
{ *rp := 1 } ||| { r1 := *rp }
%%
allow (r1 = 1) [MRD]|}
  with
  | _ -> fail "MRD answered for a program with a pointer"
  | exception Failure msg -> check bool "says why" true (contains msg "MRD")

(** Programs the edges below are checked on. *)
let programs =
  [
    {|x := 0; y := 0;
{ x := 1; r0 := y } ||| { y := 1; r1 := x }
%%
allow (r0 = 0) [_]|};
    {|x := 0; y := 0;
{ r0 := x; y := 1 } ||| { r1 := y; x := 1 }
%%
allow (r0 = 1) [_]|};
    {|x := 0; y := 0;
{ x := 1 } ||| { r0 := x; y := 1 } ||| { r1 := y; r2 := x }
%%
allow (r0 = 1) [_]|};
    {|x := 0;
{ x := 1 } ||| { x := 2 } ||| { r0 := x; r1 := x } ||| { r2 := x; r3 := x }
%%
allow (r0 = 1) [_]|};
    {|x := 0;
{ x := 2; r0 := x; r1 := x } ||| { x := 1 }
%%
allow (r0 = 1) [_]|};
    {|x := 0; y := 0;
{ x.store(1, rel); y.store(2, rel); r0 := y.load(acq) }
||| { y.store(1, rel); x.store(2, rel); r1 := x.load(acq) }
%%
allow (r0 = 1) [_]|};
    {|x := 0;
{ rpx := &x; r0 := CAS(acq, rel, rpx, 0, 1) }
||| { rpy := &x; r1 := CAS(acq, rel, rpy, 0, 2) }
%%
allow (r0 = 1) [_]|};
    {|x := 0; y := 0; z := 0;
{ rpz := &z; x := 1; rz := CAS(rlx, rlx, rpz, 0, 1); fence(sc); r0 := y }
||| { y := 1; r1 := x }
%%
allow (r0 = 0) [_]|};
  ]

(** Stronger, weaker: every execution the first admits, the second does.

    Edges involving sMRD are not among them. sMRD's own filter rejects
    executions RC11 keeps and reaches their outcomes through others, so its
    edges hold of outcomes, not of executions. *)
let edges =
  [
    ("sc", "vbd");
    ("vbd", "sc");
    ("sc", "tso");
    ("tso", "x86-tso");
    ("x86-tso", "tso");
    ("tso", "clighttso");
    ("clighttso", "tso");
    ("tso", "coherence");
    ("sc", "sra");
    ("sra", "ra");
    ("ra", "wra");
    ("sc", "pc");
    ("pc", "pram");
    ("pc", "coherence");
    ("sc", "causal");
    ("causal", "pram");
    ("causal", "cc");
    ("causal", "wfr");
    ("pram", "slow");
    ("coherence", "slow");
    ("slow", "local");
    ("pram", "ryw");
    ("pram", "mr");
    ("pram", "mw");
    ("rc11", "rc17");
    ("sc", "od-lso");
    ("sc", "pocausal");
    ("rc11", "rc11z");
    ("rc11z", "rc11");
    (* The same release sequence and psc; RC17 checks thin air too. *)
    ("rc17", "c20");
  ]

let test_edges_hold () =
  let others =
    List.sort_uniq compare (List.concat_map (fun (a, b) -> [ a; b ]) edges)
  in
    List.iter
      (fun source ->
        let ctx = run ~others source in
        let admissions = Option.get ctx.model_admissions in
          List.iter
            (fun (stronger, weaker) ->
              Hashtbl.iter
                (fun id models ->
                  if List.mem stronger models && not (List.mem weaker models)
                  then
                    fail
                      (Printf.sprintf
                         "%s admits execution %d and %s does not, in\n%s"
                         stronger id weaker source
                      )
                )
                admissions
            )
            edges
      )
      programs

let oscillating verdicts =
  Printf.sprintf
    {|x := 0;
{ x.store(1, rel) } ||| { r0 := x.load(acq); r1 := x.load(acq); r2 := x.load(acq) }
||| { x.store(2, rel) }
%%%%
%s|}
    verdicts

(** Each line of a conjunction may name several models, and each model makes an
    assertion of its own, checked under that model. *)
let test_conjunction_parses () =
  let ctx =
    parse
      (oscillating
         "allow (r0 = 1 && r1 = 2 && r2 = 1) [WRA, CC]\n\
          forbid (r0 = 1 && r1 = 2 && r2 = 1) [RA, x86-TSO]"
      )
  in
    check int "four assertions" 4 (List.length ctx.assertions);
    check (list string) "each under its own model"
      [ "wra"; "cc"; "ra"; "x86-tso" ]
      ctx.assertion_models;
    check string "the first is the primary" "wra" ctx.options.coherent

let check_source source =
  let ctx = run ~primary:"default" ~others:[] source in
  let ctx = Lwt_main.run (Lwt.return ctx |> Assertion.step_check_assertions) in
    (Option.get ctx.valid, ctx.assertion_verdicts)

let test_conjunction_checks_each_model () =
  let valid, verdicts =
    check_source
      (oscillating
         "allow (r0 = 1 && r1 = 2 && r2 = 1) [WRA]\n\
          forbid (r0 = 1 && r1 = 2 && r2 = 1) [RA, SRA, SC]"
      )
  in
    check bool "WRA allows and the others forbid" true valid;
    check (list bool) "every assertion holds" [ true; true; true; true ]
      (List.map snd verdicts);
    let valid, verdicts =
      check_source
        (oscillating
           "forbid (r0 = 1 && r1 = 2 && r2 = 1) [SC]\n\
            allow (r0 = 1 && r1 = 2 && r2 = 1) [RA]"
        )
    in
      check bool "one failing assertion fails the test" false valid;
      check (list bool) "and only that one" [ true; false ]
        (List.map snd verdicts)

(** A model that folds undefined behaviour needs its own interpretation, which a
    conjunction does not get. *)
let test_conjunction_refuses_mixed_ub_fold () =
  match
    parse
      "x := 0;\n\
       { x := 1 } ||| { r0 := x }\n\
       %%\n\
       allow (r0 = 1) [RC11]\n\
       forbid (r0 = 1) [UB11]"
  with
  | _ -> fail "RC11 and UB11 shared an enumeration"
  | exception Failure msg ->
      check bool "says why" true (contains msg "undefined behaviour")

(** The C standard's models answer to the names of its C++ revisions too. *)
let test_cpp_aliases () =
  List.iter
    (fun (alias, name) ->
      match get_model_options alias with
      | Some { coherent = Some coherent; _ } ->
          check string (alias ^ " selects " ^ name) name coherent
      | _ -> fail (alias ^ " is not a model name")
    )
    [ ("cpp11", "c11"); ("cpp17", "c17"); ("cpp20", "c20") ]

let message_passing ~flag verdicts =
  Printf.sprintf
    {|data := 0; f := 0;
{ data.store(1, na); f.store(1, %s) }
||| { r1 := f.load(%s); if (r1 = 1) { r2 := data.load(na) } else { skip } }
%%%%
%s|}
    (fst flag) (snd flag) verdicts

(** A model with a race clause reports the races of its consistent executions as
    undefined behaviour, and one without reports none. *)
let test_races_are_undefined () =
  let valid, verdicts =
    check_source
      (message_passing ~flag:("rlx", "rlx")
         "allow (ub) [C11, C17, C20, RC11]\nforbid (ub) [smrd]"
      )
  in
    check bool "a relaxed flag leaves the data read racing" true valid;
    check (list bool) "under every model with a race clause"
      [ true; true; true; true; true ]
      (List.map snd verdicts);
    let valid, _ =
      check_source
        (message_passing ~flag:("rel", "acq")
           "forbid (ub) [C11, C17, C20, RC11]"
        )
    in
      check bool "release and acquire order the data accesses" true valid

(** C++20 repaired C11's SC fences (P0668); C11 and C++17 keep them, too weak to
    forbid IRIW. *)
let test_sc_fences_separate_c20 () =
  let valid, verdicts =
    check_source
      {|x := 0; y := 0;
{ x.store(1, rlx) } ||| { y.store(1, rlx) }
||| { r1 := x.load(rlx); fence(sc); r2 := y.load(rlx) }
||| { r3 := y.load(rlx); fence(sc); r4 := x.load(rlx) }
%%
allow (r1 = 1 && r2 = 0 && r3 = 1 && r4 = 0) [C11, C17]
forbid (r1 = 1 && r2 = 0 && r3 = 1 && r4 = 0) [C20, RC11]|}
  in
    check bool "C11 and C++17 allow, C++20 and RC11 forbid" true valid;
    check (list bool) "every assertion holds" [ true; true; true; true ]
      (List.map snd verdicts)

(** A relaxed store continuing a release store's release sequence keeps sMRD
    from eliding the release store under RC11's, C++11's and IMM's release
    sequences, and not under C++17's or sMRD's, where it carries no release. A
    release store may still elide it. *)
let test_elision_follows_release_sequences () =
  let release_then flag verdicts =
    Printf.sprintf
      {|x := 0; y := 0;
{ y.store(1, na); x.store(1, rel); x.store(2, %s) }
||| { r1 := x.load(acq); if (r1 = 2) { r2 := y.load(na) } else { skip } }
%%%%
%s|}
      flag verdicts
  in
  let valid, verdicts =
    check_source
      (release_then "rlx"
         "forbid (r1 = 2 && r2 = 0) [RC11, C11, IMM]\n\
          allow (r1 = 2 && r2 = 0) [C17, C20, smrd]"
      )
  in
    check bool "a relaxed store may not elide it under RC11, C11 and IMM" true
      valid;
    check (list bool) "every assertion holds"
      [ true; true; true; true; true; true ]
      (List.map snd verdicts);
    let valid, _ =
      check_source
        (release_then "rel" "forbid (r1 = 2 && r2 = 0) [RC11, C11, C17]")
    in
      check bool "a release store synchronises in its place" true valid

let suite =
  ( "Zoo models",
    [
      test_case "names resolve" `Quick test_names_resolve;
      test_case "hyphenated names parse" `Quick test_hyphenated_names_parse;
      test_case "threads are numbered" `Quick test_threads_are_numbered;
      test_case "MRD refuses pointers" `Quick test_mrd_refuses_pointers;
      test_case "zoo edges hold per execution" `Slow test_edges_hold;
      test_case "conjunction parses" `Quick test_conjunction_parses;
      test_case "conjunction checks each model" `Quick
        test_conjunction_checks_each_model;
      test_case "conjunction refuses mixed UB fold" `Quick
        test_conjunction_refuses_mixed_ub_fold;
      test_case "C++ revision names" `Quick test_cpp_aliases;
      test_case "races are undefined" `Quick test_races_are_undefined;
      test_case "SC fences separate C++20" `Quick test_sc_fences_separate_c20;
      test_case "elision follows release sequences" `Quick
        test_elision_follows_release_sequences;
    ]
  )
