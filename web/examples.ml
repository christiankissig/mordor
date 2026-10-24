(** The examples the editor's dropdown offers, for the web server's
    [/api/examples] and the static build's [examples.json] (W5, #181). *)

(** The examples the editor's dropdown offers, served from the corpus.

    Embedding a second copy of SB, MP and LB in the frontend meant the tool
    shipped three programs while [litmus-tests/] held nearly three hundred, and
    the copies were free to drift from the corpus (github #76). These are paths
    into the tree the integration suite scans, so an example is a test that is
    known to run.

    Grouped by what the example is for, not by where it lives. *)
let example_library =
  [
    ("Classics", "MP", "litmus-tests/test6/MP.lit");
    ("Classics", "LB", "litmus-tests/test6/LB.lit");
    ("Classics", "SB (3 threads)", "litmus-tests/test6/3.SB.lit");
    ("Classics", "IRIW", "litmus-tests/test6/IRIW.lit");
    ("Classics", "2+2W", "litmus-tests/test6/2+2W.lit");
    ("Classics", "RWC", "litmus-tests/test6/RWC.lit");
    ("Classics", "W+RWC", "litmus-tests/test6/W+RWC.lit");
    ("Coherence", "CoRR", "litmus-tests/test6/CoRR1.lit");
    ("Coherence", "CoRW", "litmus-tests/test6/CoRW.lit");
    ("Coherence", "CoWR", "litmus-tests/test6/CoWR.lit");
    ("Coherence", "CoWW", "litmus-tests/test6/CoWW.lit");
    ( "Fences and access modes",
      "IRIW+acq+sc",
      "litmus-tests/pldi_repairing/IRIW+acq+sc.lit"
    );
    ( "Fences and access modes",
      "IRIW+Fsc+Fsc",
      "litmus-tests/popl_bridging/IRIW+Fsc+Fsc.lit"
    );
    ( "Fences and access modes",
      "IRIW+rlx",
      "litmus-tests/rmm-zoo/properties/atomicity-mca/IRIW+rlx.lit"
    );
    ( "Fences and access modes",
      "RWC+syncs",
      "litmus-tests/pldi_repairing/RWC+syncs.lit"
    );
    ( "Dependencies and thin air",
      "LB+deps",
      "litmus-tests/popl_bubbly/LB+deps.lit"
    );
    ( "Dependencies and thin air",
      "LB+ctrldata",
      "litmus-tests/esop_problem/lb+ctrldat+ctrl-single.lit"
    );
    ( "Dependencies and thin air",
      "Out-of-thin-air (listing12)",
      "litmus-tests/avoidoota/listing12.lit"
    );
    ( "Dependencies and thin air",
      "Volatile store is not elided",
      "litmus-tests/own/volatile-store-not-elided.lit"
    );
    (* The ones cppMem cannot express at all, and which had no one-click route
       into the editor before. *)
    ("MoRDor only", "Use after free", "programs/uaf-bug.lit");
    ("MoRDor only", "Use after free (fixed)", "programs/uaf-bug-fixed.lit");
    ("MoRDor only", "Refinement chain", "litmus-tests/avoidoota/listing7.lit");
    ( "MoRDor only",
      "Episodicity: a register condition",
      "programs/episodicity/register_condition/fail.lit"
    );
  ]

(** [read_example path] is the file's contents, or [None] if it is not there. *)
let read_example path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
      close_in ic;
      Some s
  with Sys_error _ -> None

(** [to_json ()] is the library as the editor reads it: a list of [group],
    [label], [path] and [source].

    An entry whose file is missing is dropped with a warning rather than
    breaking the dropdown, so a corpus rename degrades to one fewer example. *)
let to_json () =
  let entries =
    List.filter_map
      (fun (group, label, path) ->
        match read_example path with
        | Some source ->
            Some
              (`Assoc
                 [
                   ("group", `String group);
                   ("label", `String label);
                   ("path", `String path);
                   ("source", `String source);
                 ]
              )
        | None ->
            Logs.warn (fun m -> m "example not found, skipping: %s" path);
            None
      )
      example_library
  in
    `List entries
