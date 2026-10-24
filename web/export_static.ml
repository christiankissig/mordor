(* The data the static build's frontend reads from files instead of the
   server (W5, #181):

     export_static.exe OUT_DIR

   writes OUT_DIR/examples.json, what /api/examples serves, and
   OUT_DIR/tests.json: the lists /api/tests/list, /api/episodicity/list and
   /api/program/list serve, and the source of every file on them. Run from the
   repository's root, as the server is. *)

let write path json =
  Out_channel.with_open_bin path (fun oc ->
      Out_channel.output_string oc (Yojson.Safe.to_string json)
  )

let () =
  let out = Sys.argv.(1) in
  let litmus = Test_runner_api.read_litmus_files Test_runner_api.litmus_dir in
  let episodicity =
    Episodicity_runner_api.read_litmus_files
      Episodicity_runner_api.episodicity_dir
  in
  let programs =
    Test_runner_api.read_program_files Test_runner_api.programs_dir
  in
  let strings l = `List (List.map (fun s -> `String s) l) in
  let source path = In_channel.with_open_bin path In_channel.input_all in
    write (Filename.concat out "examples.json") (Examples.to_json ());
    write
      (Filename.concat out "tests.json")
      (`Assoc
         [
           ("tests", strings litmus);
           ("episodicity", strings episodicity);
           ("programs", strings programs);
           ( "sources",
             `Assoc
               (List.map
                  (fun p -> (p, `String (source p)))
                  (List.sort_uniq compare (litmus @ episodicity @ programs))
               )
           );
         ]
      )
