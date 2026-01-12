open Ast
open Types

let make_labeled labels stmt =
  if labels = [] then stmt else SLabeled { label = List.rev labels; stmt }

(** Helper to create source_span from parser positions *)
let make_source_span startpos endpos =
  {
    start_line = startpos.Lexing.pos_lnum;
    start_col = startpos.Lexing.pos_cnum - startpos.Lexing.pos_bol;
    end_line = endpos.Lexing.pos_lnum;
    end_col = endpos.Lexing.pos_cnum - endpos.Lexing.pos_bol;
  }

(** Context stacks *)
let thread_ctx_stack = ref [ { tid = 0; path = [] } ]

let src_ctx_stack = ref [ { pc = 0 } ]
let loop_ctx_stack = ref [ { lid = 0; loops = [] } ]
let current_thread_ctx () = List.hd !thread_ctx_stack
let current_src_ctx () = List.hd !src_ctx_stack
let current_loop_ctx () = List.hd !loop_ctx_stack

(** Reset all context stacks to initial state *)
let reset_parser_state () =
  thread_ctx_stack := [ { tid = 0; path = [] } ];
  src_ctx_stack := [ { pc = 0 } ];
  loop_ctx_stack := [ { lid = 0; loops = [] } ]

(** Functions tying context objects to parser actions **)
let push_thread () =
  let curr_thread_ctx = current_thread_ctx () in
  let new_thread_ctx =
    { tid = 0; path = curr_thread_ctx.path @ [ curr_thread_ctx.tid ] }
  in
  let curr_src_ctx = current_src_ctx () in
  let new_src_ctx = { pc = 0 } in
    thread_ctx_stack := new_thread_ctx :: !thread_ctx_stack;
    src_ctx_stack := new_src_ctx :: !src_ctx_stack

let pop_thread () =
  thread_ctx_stack := List.tl !thread_ctx_stack;
  src_ctx_stack := List.tl !src_ctx_stack

let inc_thread_id () =
  let curr = current_thread_ctx () in
  let updated = { curr with tid = curr.tid + 1 } in
    thread_ctx_stack := updated :: List.tl !thread_ctx_stack

let inc_pc () =
  let curr = current_src_ctx () in
  let updated = { pc = curr.pc + 1 } in
    src_ctx_stack := updated :: List.tl !src_ctx_stack

let push_loop () =
  let curr = List.hd !loop_ctx_stack in
  let new_loop = { lid = 0; loops = curr.loops @ [ curr.lid ] } in
    loop_ctx_stack := new_loop :: !loop_ctx_stack

let pop_loop () = loop_ctx_stack := List.tl !loop_ctx_stack

let inc_loop_id () =
  let curr = List.hd !loop_ctx_stack in
  let updated = { curr with lid = curr.lid + 1 } in
    loop_ctx_stack := updated :: List.tl !loop_ctx_stack
