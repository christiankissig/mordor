(** One request to the browser build, answered as the web server answers it: the
    same {!Streaming} pipelines and the same JSON messages, sent through [send]
    instead of over SSE (W3, #179).

    A request is the JSON body the server's [/api/<pipeline>/stream] endpoints
    take, with the pipeline named in a [pipeline] field: [parse], [interpret],
    [episodicity], [assertions] or [visualize]. *)

let pipelines =
  [
    ("parse", Streaming.visualize_parse_to_stream);
    ("interpret", Streaming.visualize_interpret_to_stream);
    ("episodicity", Streaming.visualize_test_episodicity_to_stream);
    ("assertions", Streaming.visualize_test_assertions_to_stream);
    ("visualize", Streaming.visualize_to_stream);
  ]

(** [handle body ~send] answers [body], sending each message as it is made.
    Every stage resolves synchronously here, with one domain and no I/O, so the
    answer is complete when [handle] returns. *)
let handle body ~send =
  let json = try Yojson.Basic.from_string body with _ -> `Assoc [] in
  let send_data message =
    send message;
    Lwt.return_unit
  in
  let pipeline =
    match json with
    | `Assoc fields -> (
        match List.assoc_opt "pipeline" fields with
        | Some (`String name) -> List.assoc_opt name pipelines
        | _ -> None
      )
    | _ -> None
  in
    match pipeline with
    | None ->
        send
          (Streaming.error_json
             ("Unknown pipeline; one of "
             ^ String.concat ", " (List.map fst pipelines)
             )
          )
    | Some pipeline -> (
        let answer =
          Streaming.run pipeline (Streaming.request_of_json json) ~send_data
        in
          match Lwt.state answer with
          | Lwt.Return () -> ()
          | Lwt.Fail exn -> send (Streaming.error_json (Printexc.to_string exn))
          | Lwt.Sleep ->
              send
                (Streaming.error_json
                   "A stage did not resolve synchronously, which the browser \
                    build cannot wait for"
                )
      )

(** [main_sse ()] reads a request body from stdin for the pipeline
    [Sys.argv.(1)], as [/api/PIPELINE/stream] takes it, and prints each message
    as the server's SSE stream frames it: for comparing a platform's answers
    with another's. *)
let main_sse () =
  let pipeline = Sys.argv.(1) in
  let body =
    match Yojson.Basic.from_string (In_channel.input_all stdin) with
    | `Assoc fields -> `Assoc (("pipeline", `String pipeline) :: fields)
    | _ -> `Assoc [ ("pipeline", `String pipeline) ]
    | exception _ -> `Assoc [ ("pipeline", `String pipeline) ]
  in
    handle (Yojson.Basic.to_string body) ~send:(fun message ->
        Printf.printf "data: %s\n\n%!" message
    )
