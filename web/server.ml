(** Mordor Web Server - Backend *)

open Lwt.Syntax
open Context
open Types

(* JSON helpers *)
let json_string s = `String s
let json_bool b = `Bool b
let json_int i = `Assoc [ ("value", `Int i) ]

(* Convert program to JSON for event structure visualization *)
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

    (* Extract the JSON output from the context *)
    let json_output =
      match ctx.output with
      | Some output -> output
      | None -> "{\"error\": \"No output generated\"}"
    in

    Lwt.return json_output

(* SSE handler for streaming computation progress *)
let visualize_sse_handler request =
  let program = Dream.query request "program" |> Option.value ~default:"" in
  let step_counter =
    Dream.query request "steps"
    |> Option.map int_of_string
    |> Option.value ~default:5
  in

  Dream.stream
    ~headers:
      [
        ("Content-Type", "text/event-stream");
        ("Cache-Control", "no-cache");
        ("Connection", "keep-alive");
      ]
    (fun stream ->
      (* Send initial status *)
      let* () = Dream.write stream "data: {\"status\": \"parsing\"}\n\n" in
        let* () = Dream.flush stream in

        (* Run the visualization *)
        let options =
          {
            default_options with
            use_finite_step_counter_semantics = true;
            use_step_counter_per_loop = true;
          }
        in

        (* Send parsing complete *)
        let* () =
          Dream.write stream "data: {\"status\": \"interpreting\"}\n\n"
        in
          let* () = Dream.flush stream in

          (* Get the result *)
          let* json_result =
            try visualize_to_json program options step_counter
            with e ->
              Lwt.return
                (Printf.sprintf "{\"error\": \"%s\"}" (Printexc.to_string e))
          in

          (* Send computing dependencies *)
          let* () =
            Dream.write stream
              "data: {\"status\": \"computing_dependencies\"}\n\n"
          in
            let* () = Dream.flush stream in

            (* Send final result *)
            let result_json =
              Printf.sprintf
                "data: {\"status\": \"complete\", \"result\": %s}\n\n"
                json_result
            in
              let* () = Dream.write stream result_json in
                let* () = Dream.flush stream in

                (* Close the stream *)
                Dream.close stream
    )

(* Regular POST endpoint for quick visualization *)
let visualize_handler request =
  let* body = Dream.body request in

  (* Parse JSON body *)
  let json = Yojson.Basic.from_string body in
  let program =
    Yojson.Basic.Util.member "program" json |> Yojson.Basic.Util.to_string
  in
  let step_counter =
    try Yojson.Basic.Util.member "steps" json |> Yojson.Basic.Util.to_int
    with _ -> 5
  in

  let options =
    {
      default_options with
      use_finite_step_counter_semantics = true;
      use_step_counter_per_loop = true;
    }
  in

  try
    let* json_result = visualize_to_json program options step_counter in
      Dream.json json_result
  with e ->
    Dream.json ~status:`Internal_Server_Error
      (Printf.sprintf "{\"error\": \"%s\"}" (Printexc.to_string e))

(* Health check endpoint *)
let health_handler _request =
  Dream.json "{\"status\": \"ok\", \"service\": \"mordor-web\"}"

(* Embedded HTML page *)
let index_html =
  {|<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Mordor - Event Structure Visualizer</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: #1e1e1e;
            color: #d4d4d4;
            height: 100vh;
            overflow: hidden;
        }
        .container { display: flex; flex-direction: column; height: 100vh; }
        header {
            background: #252526;
            border-bottom: 1px solid #3e3e42;
            padding: 1rem 1.5rem;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }
        header h1 { font-size: 1.5rem; color: #cccccc; }
        .header-controls { display: flex; gap: 1rem; align-items: center; }
        .main-content { display: flex; flex: 1; overflow: hidden; }
        .panel {
            display: flex;
            flex-direction: column;
            background: #1e1e1e;
            border: 1px solid #3e3e42;
            flex: 1;
        }
        .panel-header {
            background: #252526;
            border-bottom: 1px solid #3e3e42;
            padding: 0.75rem 1rem;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }
        .panel-header h2 { font-size: 1rem; color: #cccccc; }
        #litmus-input {
            flex: 1;
            padding: 1rem;
            background: #1e1e1e;
            border: none;
            color: #d4d4d4;
            font-family: 'Consolas', 'Courier New', monospace;
            font-size: 0.95rem;
            resize: none;
            outline: none;
        }
        #visualization {
            flex: 1;
            overflow: auto;
            padding: 1rem;
            background: #1e1e1e;
        }
        .empty-state {
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            height: 100%;
            color: #6a6a6a;
        }
        button {
            cursor: pointer;
            border: none;
            border-radius: 4px;
            padding: 0.5rem 1.5rem;
            font-size: 0.9rem;
            font-weight: 500;
        }
        .btn-primary { background: #0e639c; color: white; }
        .btn-primary:hover { background: #1177bb; }
        .status { font-size: 0.85rem; color: #cccccc; }
        #log {
            background: #252526;
            border-top: 1px solid #3e3e42;
            height: 150px;
            overflow-y: auto;
            padding: 0.5rem 1rem;
            font-family: 'Consolas', monospace;
            font-size: 0.85rem;
        }
        .log-entry { padding: 0.25rem 0; }
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>🔮 Mordor - Event Structure Visualizer</h1>
            <div class="header-controls">
                <label>Steps: <input type="number" id="step-counter" value="5" min="1" max="100" style="width:70px; padding:0.3rem; background:#3c3c3c; border:1px solid #555; color:#d4d4d4; border-radius:4px;"></label>
                <button id="visualize-btn" class="btn-primary">Visualize</button>
            </div>
        </header>
        <div class="main-content">
            <div class="panel">
                <div class="panel-header">
                    <h2>Litmus Source</h2>
                    <select id="examples" style="padding:0.3rem; background:#3c3c3c; border:1px solid #555; color:#d4d4d4; border-radius:4px;">
                        <option value="">-- Select Example --</option>
                        <option value="sb">Store Buffering (SB)</option>
                        <option value="mp">Message Passing (MP)</option>
                        <option value="lb">Load Buffering (LB)</option>
                    </select>
                </div>
                <textarea id="litmus-input" placeholder="Enter your litmus test here...

Example:
name = SB
%%
{ x := 1 } ||| { y := 1 }
%% allow (x = 0 && y = 0) [rc11]"></textarea>
            </div>
            <div class="panel">
                <div class="panel-header">
                    <h2>Event Structure</h2>
                    <div class="status" id="status">Ready</div>
                </div>
                <div id="visualization">
                    <div class="empty-state">
                        <p>Enter litmus source and click "Visualize"</p>
                    </div>
                </div>
            </div>
        </div>
        <div id="log"></div>
    </div>
    <script>
        const EXAMPLES = {
            sb: `name = SB\n%%\n{ x := 1 } ||| { y := 1 }\n%% allow (x = 0 && y = 0) [rc11]`,
            mp: `name = MP\n%%\n{ x := 1; y := 1 } ||| { r1 := y; r2 := x }\n%% forbid (r1 = 1 && r2 = 0) [rc11]`,
            lb: `name = LB\n%%\n{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }\n%% forbid (r1 = 1 && r2 = 1) [rc11]`
        };

        const input = document.getElementById('litmus-input');
        const vizBtn = document.getElementById('visualize-btn');
        const viz = document.getElementById('visualization');
        const status = document.getElementById('status');
        const log = document.getElementById('log');
        const examples = document.getElementById('examples');

        function logMessage(msg) {
            const time = new Date().toLocaleTimeString();
            log.innerHTML += `<div class="log-entry">[${time}] ${msg}</div>`;
            log.scrollTop = log.scrollHeight;
        }

        examples.addEventListener('change', (e) => {
            if (e.target.value) {
                input.value = EXAMPLES[e.target.value];
                logMessage('Loaded example: ' + e.target.value.toUpperCase());
            }
            e.target.value = '';
        });

        vizBtn.addEventListener('click', async () => {
            const program = input.value.trim();
            if (!program) {
                logMessage('⚠️ Please enter a litmus program');
                return;
            }

            const steps = parseInt(document.getElementById('step-counter').value) || 5;
            viz.innerHTML = '<div class="empty-state"><p>Computing...</p></div>';
            status.textContent = 'Processing...';
            logMessage('🚀 Starting visualization...');

            const params = new URLSearchParams({ program, steps: steps.toString() });
            const eventSource = new EventSource(`/api/visualize/stream?${params.toString()}`);

            eventSource.onmessage = (event) => {
                const data = JSON.parse(event.data);
                if (data.status === 'parsing') logMessage('📝 Parsing...');
                else if (data.status === 'interpreting') logMessage('⚙️ Interpreting...');
                else if (data.status === 'computing_dependencies') logMessage('🔗 Computing dependencies...');
                else if (data.status === 'complete') {
                    logMessage('✅ Complete!');
                    viz.innerHTML = `<pre style="color:#d4d4d4;overflow:auto;">${JSON.stringify(data.result, null, 2)}</pre>`;
                    status.textContent = 'Complete';
                    eventSource.close();
                }
            };

            eventSource.onerror = () => {
                logMessage('❌ Error: Connection failed');
                viz.innerHTML = '<div class="empty-state"><p style="color:#f48771;">Error occurred</p></div>';
                status.textContent = 'Error';
                eventSource.close();
            };
        });
    </script>
</body>
</html>|}

(* Serve the embedded HTML *)
let index_handler _request = Dream.html index_html

(* Main routes *)
let routes =
  [
    Dream.get "/" index_handler;
    Dream.get "/health" health_handler;
    Dream.post "/api/visualize" visualize_handler;
    Dream.get "/api/visualize/stream" visualize_sse_handler;
  ]

(* Start the server *)
let () =
  let () = Printf.printf "🔮 Mordor Web Server\n" in
  let () = Printf.printf "📂 Current directory: %s\n" (Sys.getcwd ()) in
  let () = Printf.printf "🌐 Starting server on http://localhost:8080\n" in
  let () = Printf.printf "Press Ctrl+C to stop\n\n" in
    Dream.run ~port:8080 @@ Dream.logger @@ Dream.router routes
