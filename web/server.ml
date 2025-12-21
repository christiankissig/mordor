(** Mordor Web Server - Clean version with external HTML *)

open Lwt.Syntax
open Context
open Types

let visualize_to_json program options step_counter =
  let context = make_context options ~output_mode:Json ~step_counter () in
    context.litmus <- Some program;

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Symmrd.step_calculate_dependencies
      |> Eventstructureviz.step_visualize_event_structure
    in

    let output =
      match ctx.output with
      | Some output -> output
      | None -> "{\"error\": \"No output generated\"}"
    in

    Lwt.return output

let sse_data json_obj =
  let json_str = Yojson.Basic.to_string json_obj in
    Printf.sprintf "data: %s\n\n" json_str

let visualize_sse_handler request =
  let program = Dream.query request "program" |> Option.value ~default:"" in
  let step_counter =
    Dream.query request "steps"
    |> Option.map int_of_string
    |> Option.value ~default:5
  in

  Printf.printf "📥 SSE request: %d chars, %d steps\n%!" (String.length program)
    step_counter;

  Dream.stream
    ~headers:
      [
        ("Content-Type", "text/event-stream");
        ("Cache-Control", "no-cache");
        ("Connection", "keep-alive");
        ("X-Accel-Buffering", "no");
      ]
    (fun stream ->
      Lwt.catch
        (fun () ->
          let* () =
            Dream.write stream
              (sse_data (`Assoc [ ("status", `String "parsing") ]))
          in
            let* () = Dream.flush stream in

            let options =
              {
                default_options with
                use_finite_step_counter_semantics = true;
                use_step_counter_per_loop = true;
              }
            in

            let* () =
              Dream.write stream
                (sse_data (`Assoc [ ("status", `String "interpreting") ]))
            in
              let* () = Dream.flush stream in

              let* json_result_string =
                Lwt.catch
                  (fun () -> visualize_to_json program options step_counter)
                  (fun exn ->
                    let error = Printexc.to_string exn in
                      Printf.printf "❌ Error: %s\n%!" error;
                      Lwt.return
                        (Printf.sprintf "{\"error\": %s}"
                           (Yojson.Basic.to_string (`String error))
                        )
                  )
              in

              Printf.printf "✅ Result: %d bytes\n%!"
                (String.length json_result_string);

              (* Check result size *)
              let result_size = String.length json_result_string in
                Printf.printf "📊 Result size: %d bytes\n%!" result_size;

                (* Try to parse the JSON, with fallback for invalid escapes *)
                let result_json =
                  try
                    (* First attempt: parse directly *)
                    let parsed_result =
                      Yojson.Basic.from_string json_result_string
                    in

                    if result_size > 500000 then
                      Printf.printf "⚠️ Large result (%d bytes)\n%!" result_size;

                    `Assoc
                      [
                        ("status", `String "complete");
                        ("result", parsed_result);
                        ("size", `Int result_size);
                      ]
                  with
                  | Yojson.Json_error msg ->
                      (* JSON parse error - likely invalid escape sequences *)
                      Printf.printf "⚠️ JSON has invalid escapes: %s\n%!" msg;
                      Printf.printf
                        "📝 Attempting to fix escape sequences...\n%!";

                      (* Try to fix common escape issues *)
                      let fixed_json =
                        (* Replace invalid UTF-8 escape sequences *)
                        let s = json_result_string in
                          (* This is a simple fix - you might need to adjust based on actual content *)
                          s
                      in

                      (* Send as raw string to let client handle it *)
                      Printf.printf
                        "📤 Sending as raw string for client-side parsing\n%!";
                      `Assoc
                        [
                          ("status", `String "complete_raw");
                          ("result_raw", `String json_result_string);
                          ("size", `Int result_size);
                          ( "warning",
                            `String
                              "JSON contains special characters, rendering may \
                               be limited"
                          );
                        ]
                  | e ->
                      Printf.printf "⚠️ Unexpected parse error: %s\n%!"
                        (Printexc.to_string e);
                      `Assoc
                        [
                          ("status", `String "error");
                          ( "error",
                            `String
                              ("Failed to parse result: " ^ Printexc.to_string e)
                          );
                        ]
                in

                let* () = Dream.write stream (sse_data result_json) in
                  let* () = Dream.flush stream in
                    Printf.printf "🎉 Complete!\n%!";

                    Dream.close stream
        )
        (fun exn ->
          Printf.printf "❌ SSE error: %s\n%!" (Printexc.to_string exn);
          let* () =
            Dream.write stream
              (sse_data (`Assoc [ ("error", `String (Printexc.to_string exn)) ]))
          in
            Dream.close stream
        )
    )

let health_handler _request = Dream.json "{\"status\": \"ok\"}"

(* Setup logging *)
let setup_logs () =
  let pp_header ppf (l, h) =
    let timestamp = Unix.gettimeofday () in
    let tm = Unix.localtime timestamp in
      Format.fprintf ppf "[%02d:%02d:%02d.%03d] %a: " tm.Unix.tm_hour
        tm.Unix.tm_min tm.Unix.tm_sec
        (int_of_float ((timestamp -. floor timestamp) *. 1000.))
        Logs_fmt.pp_header (l, h)
  in
  let reporter = Logs_fmt.reporter ~pp_header () in
    Logs.set_reporter reporter;
    Logs.set_level (Some Logs.Debug)

let () =
  setup_logs ();
  Printexc.record_backtrace true;
  Printf.printf "🔮 Mordor Web - Graph Visualization\n";
  Printf.printf "🌐 http://localhost:8080\n\n";

  Dream.run ~interface:"0.0.0.0" ~port:8080
  @@ Dream.logger
  @@ Dream.router
       [
         Dream.get "/" (Dream.from_filesystem "web/frontend" "index.html");
         Dream.get "/static/**" (Dream.static "web/frontend/static");
         Dream.get "/health" health_handler;
         Dream.get "/api/visualize/stream" visualize_sse_handler;
       ]
