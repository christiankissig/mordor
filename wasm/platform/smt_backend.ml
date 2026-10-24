(** The browser's {!Smt_backend}: Z3 compiled to wasm (W4, #180; the route WS2,
    #176, chose).

    It drives Z3 through [globalThis.mordorZ3] (wasm/z3/z3_shim.js),
    synchronously: a call blocks the Web Worker MoRDor runs in until Z3 answers.
    The shim makes the same C API calls as the native backend's OCaml bindings
    -- a Z3 solver per MoRDor solver, push, pop, assert, check, and model
    evaluation with completion -- except that assertions cross as SMT-LIB text
    ({!Smtlib}), which Z3 parses, rather than as a tree of handles. *)

open Types
open Js_of_ocaml

type solver = {
  z3 : Js.Unsafe.any;  (** The shim's handle on the Z3 solver *)
  vars : (string, unit) Hashtbl.t;
      (** Every symbol the assertions named, in the order the native backend
          meets them: a model binds each of them. *)
}

let call name args =
  let z3 = Js.Unsafe.get Js.Unsafe.global "mordorZ3" in
    if not (Js.Optdef.test z3) then
      failwith
        "Z3 is not loaded: globalThis.mordorZ3 is missing. Load \
         wasm/z3/z3_shim.js and call loadZ3 before MoRDor (see \
         wasm/README.md).";
    Js.Unsafe.meth_call z3 name args

let create () = { z3 = call "solver" [||]; vars = Hashtbl.create 32 }
let push s = call "push" [| s.z3 |]
let pop s = call "pop" [| s.z3 |]

let add s exprs =
  let var v = if not (Hashtbl.mem s.vars v) then Hashtbl.add s.vars v () in
  let text = Smtlib.assertions var exprs in
    call "assert" [| s.z3; Js.Unsafe.inject (Js.string text) |]

let check s =
  match int_of_float (Js.float_of_number (call "check" [| s.z3 |])) with
  | 1 -> Some true
  | -1 -> Some false
  | _ -> None

(* As the native backend: every symbol, evaluated with model completion, read
   as an integer if it is one. Z3 prints a negative one as (- 5), which is
   not, so it becomes a VVar, as it does natively. *)
let model s =
  let names =
    Hashtbl.fold (fun name () acc -> name :: acc) s.vars [] |> List.rev
  in
  let values =
    call "model"
      [|
        s.z3;
        Js.Unsafe.inject (Js.array (Array.of_list (List.map Js.string names)));
      |]
  in
    if not (Js.Opt.test values) then None
    else
      let values = Js.to_array values in
      let bindings = Hashtbl.create 16 in
        List.iteri
          (fun i name ->
            match Js.Opt.to_option values.(i) with
            | None -> ()
            | Some v -> (
                let str = Js.to_string v in
                  try Hashtbl.add bindings name (VNumber (Z.of_string str))
                  with _ -> Hashtbl.add bindings name (VVar str)
              )
          )
          names;
        Some bindings

let statistics s = Js.to_string (call "statistics" [| s.z3 |])
