open Types

type justification = {
  p : expr list; (* Predicates/conditions *)
  d : string uset; (* Dependency symbols *)
  fwd : (int * int) uset; (* Forwarding edges (event pairs) *)
  we : (int * int) uset; (* Write-elision edges (event pairs) *)
  w : event; (* The write event being justified *)
  op : string * justification option * expr option; (* Operation tag *)
}
