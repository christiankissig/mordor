(** Mordor Web Server - Clean version with external HTML *)

open Lwt.Syntax
open Context
open Types
open Source_info

let visualize_to_stream program options step_counter stream =
  let context = make_context options ~output_mode:Json ~step_counter () in
    context.litmus <- Some program;

    (* Create a function to send graph data through SSE *)
    let send_data json_str =
      let* () = Dream.write stream (Printf.sprintf "data: %s\n\n" json_str) in
        Dream.flush stream
    in

    let* ctx =
      Lwt.return context
      |> Parse.step_parse_litmus
      |> LoopInformation.send_loop_information send_data
      |> Interpret.step_interpret
      |> Eventstructureviz.step_send_event_structure_graph ~send_data
      |> Episodicity.step_test_episodicity
      |> Episodicity.send_episodicity_results send_data
      |> Symmrd.step_calculate_dependencies
      |> Assertion.step_check_assertions
      |> Eventstructureviz.step_send_execution_graphs ~send_data
    in

    Lwt.return ctx

let sse_data json_obj =
  let json_str = Yojson.Basic.to_string json_obj in
    Printf.sprintf "data: %s\n\n" json_str

let visualize_sse_handler request =
  let program = Dream.query request "program" |> Option.value ~default:"" in

  let loop_semantics =
    Dream.query request "loop_semantics"
    |> Option.value ~default:"finite-step-counter"
  in

  let loop_semantics =
    match String.lowercase_ascii loop_semantics with
    | "symbolic" -> Symbolic
    | "step-counter" -> StepCounterPerLoop
    | _ -> StepCounterPerLoop
  in

  let step_counter =
    match loop_semantics with
    | Generic | Symbolic -> 0
    | StepCounterPerLoop | FiniteStepCounter ->
        Dream.query request "steps"
        |> Option.map int_of_string
        |> Option.value ~default:2
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

            let options = { default_options with loop_semantics } in

            let* () =
              Dream.write stream
                (sse_data (`Assoc [ ("status", `String "interpreting") ]))
            in
              let* () = Dream.flush stream in

              let* () =
                Dream.write stream
                  (sse_data (`Assoc [ ("status", `String "visualizing") ]))
              in
                let* () = Dream.flush stream in

                let* _ctx =
                  Lwt.catch
                    (fun () ->
                      visualize_to_stream program options step_counter stream
                    )
                    (fun exn ->
                      let error = Printexc.to_string exn in
                        Printf.printf "❌ Error: %s\n%!" error;
                        let* () =
                          Dream.write stream
                            (sse_data (`Assoc [ ("error", `String error) ]))
                        in
                          let* () = Dream.flush stream in
                            Lwt.fail exn
                    )
                in

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
