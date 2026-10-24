(* For testing the browser build under node: [node node_main.bc.js PIPELINE]
   reads a request body on stdin and prints the answer as the server's SSE
   stream frames it (see [Session.main_sse]). *)
let () = Session.main_sse ()
