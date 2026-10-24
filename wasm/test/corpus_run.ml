(* The W1 corpus (#175) through the browser build's Z3 (W4, #180), for
   corpus.py:

     node wasm/node_run.js Z3DIR corpus_run.bc.js LIST OUT

   For each path in LIST, one per line, asserts the .smt2 file's assertions on
   a fresh solver and checks it, through globalThis.mordorZ3 -- the calls the
   browser Smt_backend makes -- and writes the path, the answer (sat, unsat,
   "unknown: <reason>" or "error: <message>") and the check's seconds to OUT. *)

open Js_of_ocaml

let now () =
  Js.Unsafe.meth_call (Js.Unsafe.get Js.Unsafe.global "performance") "now" [||]
  /. 1000.

let call name args =
  Js.Unsafe.meth_call (Js.Unsafe.get Js.Unsafe.global "mordorZ3") name args

let run text =
  try
    let s = call "solver" [||] in
      ignore (call "assert" [| s; Js.Unsafe.inject (Js.string text) |]);
      let t = now () in
      let r = Js.float_of_number (call "check" [| s |]) in
      let secs = now () -. t in
        ( ( match int_of_float r with
          | 1 -> "sat"
          | -1 -> "unsat"
          | _ ->
              "unknown: "
              ^ Js.to_string (Js.Unsafe.coerce (call "reasonUnknown" [| s |]))
          ),
          secs
        )
  with Js_error.Exn e -> ("error: " ^ Js_error.message e, 0.)

let () =
  match Array.to_list Sys.argv |> List.tl with
  | [ list; out ] ->
      let oc = open_out_bin out in
        In_channel.with_open_bin list In_channel.input_all
        |> String.split_on_char '\n'
        |> List.filter (( <> ) "")
        |> List.iter (fun path ->
            let answer, secs =
              run (In_channel.with_open_bin path In_channel.input_all)
            in
              Printf.fprintf oc "%s\t%s\t%.6f\n%!" path answer secs
        );
        close_out oc
  | _ -> failwith "usage: corpus_run LIST OUT"
