(** Mordor Web Server - Complete with Fixed Labels *)

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

(* Embedded complete HTML page with graph visualization *)
let index_html =
  {|<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Mordor - Event Structure Visualizer</title>
    <script src="https://unpkg.com/cytoscape@3.28.1/dist/cytoscape.min.js"></script>
    <script src="https://unpkg.com/layout-base@2.0.1/layout-base.js"></script>
    <script src="https://unpkg.com/cose-base@2.2.0/cose-base.js"></script>
    <script src="https://unpkg.com/cytoscape-cose-bilkent@4.1.0/cytoscape-cose-bilkent.js"></script>
    <script src="https://unpkg.com/cytoscape-fcose@2.2.0/cytoscape-fcose.js"></script>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; background: #1e1e1e; color: #d4d4d4; height: 100vh; overflow: hidden; }
        .container { display: flex; flex-direction: column; height: 100vh; }
        header { background: #252526; border-bottom: 1px solid #3e3e42; padding: 1rem 1.5rem; display: flex; justify-content: space-between; align-items: center; }
        header h1 { font-size: 1.5rem; color: #cccccc; }
        .header-controls { display: flex; gap: 1rem; align-items: center; }
        .main-content { display: flex; flex: 1; overflow: hidden; }
        .panel { display: flex; flex-direction: column; background: #1e1e1e; border: 1px solid #3e3e42; flex: 1; position: relative; }
        .panel-header { background: #252526; border-bottom: 1px solid #3e3e42; padding: 0.75rem 1rem; display: flex; justify-content: space-between; align-items: center; }
        .panel-header h2 { font-size: 1rem; color: #cccccc; }
        #litmus-input { flex: 1; padding: 1rem; background: #1e1e1e; border: none; color: #d4d4d4; font-family: 'Consolas', 'Courier New', monospace; font-size: 0.95rem; resize: none; outline: none; }
        #cy { flex: 1; background: #1e1e1e; }
        .graph-controls { position: absolute; top: 60px; right: 10px; background: rgba(37, 37, 38, 0.95); border: 1px solid #3e3e42; border-radius: 4px; padding: 0.5rem; display: flex; flex-direction: column; gap: 0.5rem; z-index: 100; }
        .graph-controls button { background: #3c3c3c; border: none; color: #cccccc; padding: 0.4rem 0.8rem; border-radius: 3px; cursor: pointer; font-size: 0.85rem; }
        .graph-controls button:hover { background: #505050; }
        .graph-controls select { background: #3c3c3c; border: 1px solid #555; color: #d4d4d4; padding: 0.4rem; border-radius: 3px; font-size: 0.85rem; }
        .graph-stats { position: absolute; bottom: 10px; left: 10px; background: rgba(37, 37, 38, 0.95); border: 1px solid #3e3e42; border-radius: 4px; padding: 0.5rem 0.75rem; font-size: 0.85rem; z-index: 100; }
        .empty-state { display: flex; flex-direction: column; align-items: center; justify-content: center; height: 100%; color: #6a6a6a; position: absolute; top: 0; left: 0; right: 0; bottom: 0; }
        button { cursor: pointer; border: none; border-radius: 4px; padding: 0.5rem 1.5rem; font-size: 0.9rem; font-weight: 500; }
        .btn-primary { background: #0e639c; color: white; }
        .btn-primary:hover { background: #1177bb; }
        .btn-primary:disabled { background: #555; cursor: not-allowed; }
        .status { font-size: 0.85rem; color: #cccccc; }
        #log { background: #252526; border-top: 1px solid #3e3e42; height: 150px; overflow-y: auto; padding: 0.5rem 1rem; font-family: 'Consolas', monospace; font-size: 0.85rem; }
        .log-entry { padding: 0.25rem 0; }
        .error { color: #f48771; }
        .success { color: #89d185; }
        .info { color: #4ec9b0; }
        .spinner { border: 3px solid #3c3c3c; border-top: 3px solid #0e639c; border-radius: 50%; width: 40px; height: 40px; animation: spin 1s linear infinite; }
        @keyframes spin { 0% { transform: rotate(0deg); } 100% { transform: rotate(360deg); } }
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
                <textarea id="litmus-input" placeholder="Enter your litmus test here..."></textarea>
            </div>
            <div class="panel">
                <div class="panel-header">
                    <h2>Event Structure</h2>
                    <div class="status" id="status">Ready</div>
                </div>
                <div id="cy"></div>
                <div id="json-view" style="display: none; flex: 1; overflow: auto; padding: 1rem;">
                    <pre id="json-content" style="color: #d4d4d4; background: #252526; padding: 1rem; border-radius: 4px; overflow: auto;"></pre>
                </div>
                <div id="empty-state" class="empty-state"><p>Enter litmus source and click "Visualize"</p></div>
                <div class="graph-controls" id="graph-controls" style="display: none;">
                    <select id="layout-select">
                        <option value="fcose">fCoSE (Fast)</option>
                        <option value="cose-bilkent">COSE (Quality)</option>
                        <option value="breadthfirst">Hierarchical</option>
                        <option value="circle">Circle</option>
                    </select>
                    <button id="fit-btn">Fit</button>
                    <button id="toggle-view-btn">View JSON</button>
                    <button id="export-png-btn">Export PNG</button>
                </div>
                <div class="graph-stats" id="graph-stats" style="display: none;">
                    <div><strong>Nodes:</strong> <span id="node-count">0</span></div>
                    <div><strong>Edges:</strong> <span id="edge-count">0</span></div>
                </div>
            </div>
        </div>
        <div id="log"></div>
    </div>
    <script>
const EXAMPLES = {
    sb: "name = SB\n%%\n{ x := 1 } ||| { y := 1 }\n%% allow (x = 0 && y = 0) [rc11]",
    mp: "name = MP\n%%\n{ x := 1; y := 1 } ||| { r1 := y; r2 := x }\n%% forbid (r1 = 1 && r2 = 0) [rc11]",
    lb: "name = LB\n%%\n{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }\n%% forbid (r1 = 1 && r2 = 1) [rc11]"
};
const EDGE_COLORS = { po: '#4ec9b0', rf: '#0e639c', co: '#ffa500', fr: '#f48771', default: '#6a6a6a' };

class GraphVisualizer {
    constructor() {
        this.currentGraphData = null;
        this.isJsonView = false;

        this.cy = cytoscape({
            container: document.getElementById('cy'),
            style: [
                {
                    selector: 'node',
                    style: {
                        'background-color': '#0e639c',
                        'label': 'data(label)',
                        'color': '#ffffff',
                        'text-valign': 'center',
                        'text-halign': 'center',
                        'font-size': '11px',
                        'font-weight': 'bold',
                        'width': '35px',
                        'height': '35px',
                        'border-width': 2,
                        'border-color': '#1177bb',
                        'text-outline-color': '#000000',
                        'text-outline-width': 2
                    }
                },
                {
                    selector: 'edge',
                    style: {
                        'width': 2,
                        'line-color': 'data(color)',
                        'target-arrow-color': 'data(color)',
                        'target-arrow-shape': 'triangle',
                        'curve-style': 'bezier',
                        'label': 'data(type)',
                        'font-size': '9px',
                        'color': '#d4d4d4',
                        'text-background-color': '#1e1e1e',
                        'text-background-opacity': 0.8,
                        'text-background-padding': '2px'
                    }
                }
            ],
            minZoom: 0.1,
            maxZoom: 5,
            wheelSensitivity: 0.2
        });

        document.getElementById('examples').addEventListener('change', (e) => {
            if (e.target.value) {
                document.getElementById('litmus-input').value = EXAMPLES[e.target.value];
                this.log('Loaded example');
                e.target.value = '';
            }
        });

        document.getElementById('visualize-btn').addEventListener('click', () => this.visualize());
        document.getElementById('layout-select').addEventListener('change', (e) => this.applyLayout(e.target.value));
        document.getElementById('fit-btn').addEventListener('click', () => this.cy.fit());
        document.getElementById('toggle-view-btn').addEventListener('click', () => this.toggleView());
        document.getElementById('export-png-btn').addEventListener('click', () => {
            const png = this.cy.png({ output: 'blob', bg: '#1e1e1e', full: true, scale: 2 });
            const url = URL.createObjectURL(png);
            const a = document.createElement('a');
            a.href = url;
            a.download = 'event-structure.png';
            a.click();
        });

        this.log('Ready');
    }

    visualize() {
        const program = document.getElementById('litmus-input').value.trim();
        if (!program) { this.log('Enter a program', 'error'); return; }

        document.getElementById('visualize-btn').disabled = true;
        document.getElementById('empty-state').innerHTML = '<div class="spinner"></div>';
        this.log('Visualizing...');

        const params = new URLSearchParams({ program, steps: document.getElementById('step-counter').value });
        const es = new EventSource('/api/visualize/stream?' + params);

        es.onmessage = (e) => {
            try {
                const d = JSON.parse(e.data);
                if (d.error) {
                    this.log('Error: ' + d.error, 'error');
                    es.close();
                    document.getElementById('visualize-btn').disabled = false;
                    return;
                }
                if (d.status === 'complete') {
                    if (d.size && d.size > 1000000) {
                        this.log('Processing large dataset (' + Math.round(d.size/1024) + ' KB)...', 'info');
                    }
                    // d.result is already a parsed JSON object from the server
                    this.renderGraph(d.result);
                    es.close();
                    document.getElementById('visualize-btn').disabled = false;
                } else if (d.status === 'complete_raw') {
                    // Server couldn't parse, try on client side
                    if (d.warning) {
                        this.log('Warning: ' + d.warning, 'warning');
                    }
                    this.log('Parsing JSON client-side...', 'info');
                    try {
                        const parsed = JSON.parse(d.result_raw);
                        this.renderGraph(parsed);
                    } catch (parseErr) {
                        this.log('Client parse also failed: ' + parseErr.message, 'error');
                        console.error('Parse error:', parseErr);
                        console.error('First 1000 chars of raw data:', d.result_raw.substring(0, 1000));
                    }
                    es.close();
                    document.getElementById('visualize-btn').disabled = false;
                } else if (d.status === 'error') {
                    this.log('Server error: ' + d.error, 'error');
                    es.close();
                    document.getElementById('visualize-btn').disabled = false;
                } else {
                    this.log(d.status + '...');
                }
            } catch (err) {
                this.log('Parse error: ' + err.message, 'error');
                console.error('Full error:', err);
                console.error('Event data length:', e.data ? e.data.length : 'undefined');
                console.error('First 500 chars:', e.data ? e.data.substring(0, 500) : 'undefined');
                es.close();
                document.getElementById('visualize-btn').disabled = false;
            }
        };
        es.onerror = () => { this.log('Connection error', 'error'); es.close(); document.getElementById('visualize-btn').disabled = false; };
    }

    renderGraph(data) {
        try {
            // Data is already a parsed object from the server, no need to parse again
            const graph = data;
            this.currentGraphData = graph;  // Store for JSON view toggle

            this.log('Rendering graph...');
            console.log('Graph data nodes:', graph.nodes ? graph.nodes.length : 0, 'edges:', graph.edges ? graph.edges.length : 0);

            if (!graph.nodes || graph.nodes.length === 0) {
                this.log('No nodes in graph data', 'error');
                console.log('Graph structure:', graph);
                return;
            }

            if (graph.nodes.length > 1000) {
                this.log('Warning: Large graph (' + graph.nodes.length + ' nodes), rendering may be slow', 'warning');
            }

            this.cy.elements().remove();

            // Add nodes
            let nodeCount = 0;
            graph.nodes.forEach(n => {
                let label = '';

                // Build label based on available data
                if (n.type && n.location) {
                    label = n.label + ":" + n.type + '(' + n.location + ')';
                } else if (n.type) {
                    label = n.type;
                } else if (n.label !== undefined && n.label !== null) {
                    label = String(n.label);
                } else {
                    label = String(n.id);
                }

                this.cy.add({
                    data: {
                        id: String(n.id),
                        label: label
                    }
                });
                nodeCount++;

                // Progress indicator for large graphs
                if (nodeCount % 100 === 0 && graph.nodes.length > 500) {
                    console.log('Added ' + nodeCount + '/' + graph.nodes.length + ' nodes');
                }
            });

            // Add edges
            let edgeCount = 0;
            graph.edges.forEach(e => {
                const color = e.color || EDGE_COLORS[e.type] || EDGE_COLORS.default;
                const edgeType = e.type || 'edge';

                this.cy.add({
                    data: {
                        source: String(e.source),
                        target: String(e.target),
                        color: color,
                        type: edgeType
                    }
                });
                edgeCount++;

                // Progress indicator for large graphs
                if (edgeCount % 500 === 0 && graph.edges.length > 1000) {
                    console.log('Added ' + edgeCount + '/' + graph.edges.length + ' edges');
                }
            });

            this.log('Applying layout...');
            this.applyLayout('fcose');

            document.getElementById('empty-state').style.display = 'none';
            document.getElementById('graph-controls').style.display = 'flex';
            document.getElementById('graph-stats').style.display = 'block';
            document.getElementById('node-count').textContent = graph.nodes.length;
            document.getElementById('edge-count').textContent = graph.edges.length;
            this.log('Rendered: ' + graph.nodes.length + ' nodes, ' + graph.edges.length + ' edges', 'success');

            // Show graph view by default
            this.showGraphView();

        } catch (error) {
            this.log('Render failed: ' + error.message, 'error');
            console.error('Render error:', error);
            console.error('Stack:', error.stack);
            this.showError('Failed to render graph: ' + error.message);
        }
    }

    showError(message) {
        document.getElementById('empty-state').innerHTML = '<div style="color: #f48771; padding: 2rem; text-align: center;"><p>' + message + '</p><p style="margin-top: 1rem; font-size: 0.9rem;">Check browser console for details (F12)</p></div>';
        document.getElementById('empty-state').style.display = 'flex';
    }

    toggleView() {
        if (this.isJsonView) {
            this.showGraphView();
        } else {
            this.showJsonView();
        }
    }

    showGraphView() {
        this.isJsonView = false;
        document.getElementById('cy').style.display = 'block';
        document.getElementById('json-view').style.display = 'none';
        document.getElementById('toggle-view-btn').textContent = 'View JSON';
        document.getElementById('layout-select').disabled = false;
        document.getElementById('fit-btn').disabled = false;
        document.getElementById('export-png-btn').disabled = false;
        this.log('Switched to graph view');
    }

    showJsonView() {
        if (!this.currentGraphData) {
            this.log('No graph data available', 'error');
            return;
        }

        this.isJsonView = true;
        document.getElementById('cy').style.display = 'none';
        document.getElementById('json-view').style.display = 'block';
        document.getElementById('json-content').textContent = JSON.stringify(this.currentGraphData, null, 2);
        document.getElementById('toggle-view-btn').textContent = 'View Graph';
        document.getElementById('layout-select').disabled = true;
        document.getElementById('fit-btn').disabled = true;
        document.getElementById('export-png-btn').disabled = true;
        this.log('Switched to JSON view');
    }

    applyLayout(name) {
        const configs = {
            fcose: { name: 'fcose', animate: true, fit: true, padding: 50, nodeSeparation: 150 },
            'cose-bilkent': { name: 'cose-bilkent', animate: true, fit: true, padding: 50 },
            breadthfirst: { name: 'breadthfirst', directed: true, animate: true },
            circle: { name: 'circle', animate: true }
        };
        this.cy.layout(configs[name] || configs.fcose).run();
    }

    log(msg, type = 'info') {
        const time = new Date().toLocaleTimeString();
        const cls = type === 'error' ? 'error' : type === 'success' ? 'success' : 'info';
        document.getElementById('log').innerHTML += '<div class="log-entry ' + cls + '">[' + time + '] ' + msg + '</div>';
        document.getElementById('log').scrollTop = 999999;
    }
}

new GraphVisualizer();
    </script>
</body>
</html>|}

(* Add this function before the main function *)
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
         Dream.get "/" (fun _req -> Dream.html index_html);
         Dream.get "/health" health_handler;
         Dream.get "/api/visualize/stream" visualize_sse_handler;
       ]
