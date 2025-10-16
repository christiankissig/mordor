(** Main entry point for sMRD *)
open Lwt.Syntax

open Types

(** Run verification *)
let verify_program program options =
  let* result = Symmrd.create_symbolic_event_structure program options in
    Lwt.return result

(** Pretty print results *)
let print_results result =
  Printf.printf "=== Verification Results ===\n";
  Printf.printf "Valid: %b\n" result.valid;
  Printf.printf "Undefined Behavior: %b\n" result.ub;
  Printf.printf "Executions: %d\n" (List.length result.executions);
  Printf.printf "Events: %d\n" (Hashtbl.length result.structure.e);
  Printf.printf "===========================\n"

(** Example programs *)
let example_programs =
  [
    ( "Store Buffering",
      {|
name = SB
%%
{ x := 1 } ||| { y := 1 }
%% allow (x = 0 && y = 0) [rc11]
  |}
    );
    ( "Message Passing",
      {|
name = MP
%%
{ x := 1; y := 1 } ||| { r1 := y; r2 := x }
%% forbid (r1 = 1 && r2 = 0) [rc11]
  |}
    );
    ( "Load Buffering",
      {|
name = LB
%%
{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }
%% forbid (r1 = 1 && r2 = 1) [rc11]
  |}
    );
  ]

(** Run example *)
let run_example name program =
  Printf.printf "\n=== Running: %s ===\n" name;
  Printf.printf "Program:\n%s\n\n" program;

  let* result = verify_program program default_options in
    print_results result;
    Lwt.return_unit

(** Main *)
let main () =
  Printf.printf "sMRD - Symbolic Memory Relaxation Dependencies\n";
  Printf.printf "OCaml Implementation\n\n";

  let* () =
    Lwt_list.iter_s (fun (name, prog) -> run_example name prog) example_programs
  in

  Lwt.return_unit

let () = Lwt_main.run (main ())
