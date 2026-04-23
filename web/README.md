# MoRDor - Web Server

## Overview

The web server (`mordor-web`) provides a browser UI for visualizing symbolic
event structures and running litmus tests. It is built on
[Dream](https://aantron.github.io/dream/) and streams results to the frontend
via Server-Sent Events (SSE).

```
├── dune
├── server.ml                          # Main entry point; routes and SSE handlers
├── test_runner_api.ml                 # REST handlers for running litmus tests via CLI
├── episodicity_runner_api.ml          # REST handlers for episodicity analysis via CLI
└── frontend/
    ├── index.html                     # Main split-screen editor/visualizer UI
    ├── help.html                      # Help documentation page
    └── static/
        ├── css/
        │   ├── mordor.css             # Main application styles
        │   └── test-runner.css        # Test runner panel styles
        └── js/
            ├── graph-visualizer.js    # D3-based event structure graph renderer
            ├── prism-smrd.js          # Prism syntax highlighting for litmus format
            └── test-runner.js         # Test runner panel logic
```

## Source Modules

- **`server.ml`** — Defines the five SSE pipeline variants, a shared 
  `make_sse_handler` factory, and the Dream router. Listens on `0.0.0.0:8080`.
- **`test_runner_api.ml`** — Scans `litmus-tests/` and `programs/` for `.lit` 
  files, executes them through the built CLI binary, and parses the text output 
  back into structured JSON.
- **`episodicity_runner_api.ml`** — Scans `programs/episodicity/` for `.lit` 
  files and runs `dune exec mordor -- episodicity` on them, parsing per-loop, 
  per-condition results from CLI output.

## API Reference

### Static content

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/` | Main application page (`index.html`) |
| `GET` | `/help/` | Help page (`help.html`) |
| `GET` | `/static/**` | CSS, JS, and other static assets |
| `GET` | `/health` | Health check — returns `{"status": "ok"}` |

### Visualization (SSE)

All visualization endpoints are `POST` and stream `text/event-stream`. The 
request body is JSON:

```json
{
  "program":        "<litmus test source>",
  "loop_semantics": "symbolic" | "step-counter",
  "steps":          "<integer>",
  "memory_model":   "smrd" | "rc11" | "rc11c" | "rc11ub" | "ub11" | "undefined"
}
```

Each endpoint runs a prefix of the full pipeline and streams intermediate status 
messages followed by graph/assertion data, ending with a completion message:

```json
{"type": "complete", "total_executions": <n>}
```

| Method | Path | Pipeline stages |
|--------|------|----------------|
| `POST` | `/api/visualize/stream` | parse → interpret → justifications → dependencies → assertions → execution graphs |
| `POST` | `/api/parse/stream` | parse |
| `POST` | `/api/interpret/stream` | parse → interpret → event structure graph |
| `POST` | `/api/episodicity/stream` | parse → interpret → event structure graph → episodicity |
| `POST` | `/api/assertions/stream` | parse → interpret → event structure graph → episodicity → justifications → dependencies → assertions → execution graphs |

### Test Runner

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/api/tests/list` | List all `.lit` files under `litmus-tests/` (recursive) |
| `POST` | `/api/tests/run` | Run a test via the CLI binary; body: `{"test": "<path>"}` |
| `GET` | `/api/tests/source?test=<path>` | Return source of a litmus test file |
| `GET` | `/api/program/list` | List `.lit` files under `programs/` (excludes `programs/episodicity/`) |

`POST /api/tests/run` response:
```json
{
  "success": bool,
  "exit_code": int,
  "output": "<raw CLI output>",
  "parsed": bool,
  "valid": bool | null,
  "undefined_behaviour": bool | null,
  "executions": int | null,
  "events": int | null
}
```

### Episodicity Runner

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/api/episodicity/list` | List all `.lit` files under `programs/episodicity/` |
| `POST` | `/api/episodicity/run` | Run episodicity analysis; body: `{"test": "<path>"}` |
| `GET` | `/api/episodicity/source?test=<path>` | Return source of an episodicity test file |

`POST /api/episodicity/run` response:
```json
{
  "success": bool,
  "exit_code": int,
  "output": "<raw CLI output>",
  "loops_analyzed": int,
  "all_episodic": bool,
  "results": [
    {
      "loop_id": int,
      "is_episodic": bool,
      "conditions": [
        { "condition_num": int, "satisfied": bool, "violation_count": int }
      ]
    }
  ]
}
```
