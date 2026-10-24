(* The browser build's sessions on the native platform, Z3 and all:
   [session_native.exe PIPELINE] reads a request body on stdin and prints the
   answer as the server's SSE stream frames it (see [Session.main_sse]), for
   comparing with [node_main.bc.js]. *)
let () = Session.main_sse ()
