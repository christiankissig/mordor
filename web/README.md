# MoRDor - Web Server

## Overview

The web server (`mordor-web`) provides a browser UI for exploring a program's
event structure and justified executions, and for running litmus tests. Its
manual is served at `/manual/`. It is built on
[Dream](https://aantron.github.io/dream/) and streams results to the frontend
via Server-Sent Events (SSE).

```
├── dune
├── server.ml                          # Main entry point; routes and SSE handlers
├── test_runner_api.ml                 # REST handlers for running litmus tests via CLI
├── episodicity_runner_api.ml          # REST handlers for episodicity analysis via CLI
└── frontend/
    ├── index.html                     # Main split-screen editor/visualizer UI
    ├── manual.html                    # The manual, including the language reference
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
| `GET` | `/manual/` | The manual (`manual.html`) |
| `GET` | `/help/` | The manual, for links to the former help page |
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
  "memory_model":   "default" | "smrd" | "rc11",
  "compare_models": ["smrd" | "rc11", ...]
}
```

`memory_model` is the primary model: executions are enumerated and shown under
it, and the assertion is checked against it. `"default"`, or any other value, is
the model the litmus test's annotation names, which may be one not offered here
such as IMM, or sMRD if it names none; a named model replaces the annotation.

`compare_models` (optional) are further models every execution is checked
against. The primary and duplicates are dropped, and other names are ignored. When any remain, `/api/visualize/stream` and `/api/assertions/stream`
send a count of the executions each model allows,

```json
{"type": "model_counts", "primary": "rc11",
 "counts": [{"model": "rc11", "executions": 21}, {"model": "smrd", "executions": 25}]}
```

and each `execution` message carries `other_models`, the compared models that
also allow it. The primary's count is the number of executions sent; a compared
model's also counts executions the primary rejects.

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

### Executions Export (non-streaming)

| Method | Path | Description |
|--------|------|-------------|
| `POST` | `/api/executions` | Run parse → interpret → justifications → dependencies and return all executions as a single JSON document |

Request body matches the SSE endpoints (`program`, `loop_semantics`, `steps`,
`memory_model`; `compare_models` is ignored). The response is `application/json` with the following shape:

```json
{
  "program": "<name>",
  "executions": [
    {
      "id": 0,
      "predicates": ["..."],
      "events": [
        { "id": 1, "type": "W", "label": 1, "thread": 0,
          "location": "x", "wval": "1",
          "rmod": "Relaxed", "wmod": "Relaxed", "fmod": "Relaxed",
          "volatile": false, "is_rmw": false, "constraints": [] }
      ],
      "po":  [[0, 1]],
      "dp":  [],
      "ppo": [[0, 1]],
      "rf":  [[1, 2]],
      "rmw": []
    }
  ]
}
```

The same payload is produced by the CLI's `executions` command.

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
