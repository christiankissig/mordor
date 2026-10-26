(** The integration suites name their corpora ([litmus-tests/],
    [programs/episodicity/]) and the CLI ([_build/default/cli/main.exe]) by
    paths relative to the project root, and their case names are those paths.
    [dune exec test/test_integration.exe] runs from wherever it is invoked,
    [dune build @runtest] and [@integration] run it in [_build/default/test].
    [enter ()] moves to the project root, found as the nearest ancestor of the
    working directory with a [dune-project] (the build directory has none), so
    that the paths resolve from all of them. Each suite calls it before reading
    its corpus, which it does when its module is initialised. *)

let root =
  let rec up dir fuel =
    if fuel = 0 then None
    else if Sys.file_exists (Filename.concat dir "dune-project") then Some dir
    else
      let parent = Filename.dirname dir in
        if parent = dir then None else up parent (fuel - 1)
  in
    up (Sys.getcwd ()) 8

let enter () =
  match root with
  | Some dir -> if Sys.getcwd () <> dir then Sys.chdir dir
  | None ->
      Printf.eprintf
        "test_integration: no dune-project above %s; the corpora will not be \
         found\n"
        (Sys.getcwd ())
