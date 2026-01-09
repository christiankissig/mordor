open Context
open Ir_context_utils
open Types
open Lwt.Syntax

module LoopInformation = struct
  type json_loop_source_span = {
    id : int;
    start_line : int;
    start_col : int;
    end_line : int;
    end_col : int;
  }
  [@@deriving yojson]

  type json_loop_information = {
    type_ : string; [@key "type"]
    loops : json_loop_source_span list;
  }
  [@@deriving yojson]

  let generate_loop_information_json (ctx : mordor_ctx) : string =
    let program =
      match ctx.program_stmts with
      | Some p -> p
      | None -> failwith "Program statements not available in context"
    in
    let (loop_ids_and_spans : (int * source_span option) list) =
      collect_loop_ids_and_spans program
    in

    let json_loops =
      List.map
        (fun ((lid : int), (span_opt : source_span option)) ->
          match span_opt with
          | Some span ->
              {
                id = lid;
                start_line = span.start_line;
                start_col = span.start_col;
                end_line = span.end_line;
                end_col = span.end_col;
              }
          | None ->
              {
                id = lid;
                start_line = -1;
                start_col = -1;
                end_line = -1;
                end_col = -1;
              }
        )
        loop_ids_and_spans
    in

    let loop_info = { type_ = "loop-info"; loops = json_loops } in
    let json = json_loop_information_to_yojson loop_info in
      Yojson.Safe.to_string json

  let send_loop_information (send_func : string -> unit Lwt.t)
      (ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
    let* ctx = ctx in
    let json_str = generate_loop_information_json ctx in
      let* () = send_func json_str in
        Lwt.return ctx
end
