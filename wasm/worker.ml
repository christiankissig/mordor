(* The Web Worker entry point (W3, #179). Each message the page posts is a
   request (see {!Session}); the worker posts back each JSON message of the
   answer as a string, as the server sends them over SSE, and then [null] to
   say the answer is complete. *)

open Js_of_ocaml

let () =
  Worker.set_onmessage (fun (data : Js.js_string Js.t) ->
      Session.handle (Js.to_string data) ~send:(fun message ->
          Worker.post_message (Js.string message)
      );
      Worker.post_message Js.null
  )
