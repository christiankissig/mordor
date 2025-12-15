# Mordor Web - Quick Start Guide

## What Was Created

I've created a complete web application stub for Mordor with:

### Backend (`web/backend/`)
- **server.ml**: Dream-based web server with:
  - SSE endpoint for streaming computation progress
  - Regular POST endpoint for synchronous requests
  - Integration with your existing `visual-es` command
  - Proper error handling and logging

### Frontend (`web/frontend/`)
- **index.html**: Split-screen UI with:
  - Left panel: Multi-line litmus source editor
  - Right panel: Event structure visualization
  - Bottom: Progress log for tracking computation steps
  
- **static/styles.css**: Dark theme inspired by VS Code
  
- **static/app.js**: JavaScript application with:
  - SSE client for real-time updates
  - Event structure rendering
  - Example loading
  - Error handling
  
- **static/examples.js**: Sample litmus tests (SB, MP, LB)

## Integration Steps

### 1. Copy Files to Your Project

```bash
# From the directory where these files were created
cp -r /home/claude/web/ /path/to/your/mordor/project/

# Or manually copy:
# - web/backend/server.ml
# - web/backend/dune  
# - web/frontend/index.html
# - web/frontend/static/*
```

### 2. Update Your dune-project

Add the web package to your existing `dune-project`:

```lisp
(package
 (name mordor-web)
 (synopsis "Web interface for Mordor")
 (depends
  (ocaml (>= 4.14))
  mordor
  dream
  yojson
  lwt))
```

### 3. Install Dependencies

```bash
opam install dream yojson
```

### 4. Build and Run

```bash
# Build everything
dune build

# Run the web server
dune exec mordor-web

# Or directly run the executable
./_build/default/web/backend/server.exe
```

### 5. Open in Browser

Navigate to: http://localhost:8080

## Usage

1. **Enter litmus source** in the left panel (or load an example)
2. **Adjust step counter** if needed (default: 5)
3. **Click "Visualize"** to run the analysis
4. **Watch the progress log** as it parses, interprets, and computes dependencies
5. **View the result** in the right panel

## Current Output Format

The backend calls your existing pipeline:
```ocaml
Lwt.return context
  |> Parse.step_parse_litmus
  |> Interpret.step_interpret
  |> Symmrd.step_calculate_dependencies
  |> Eventstructureviz.step_visualize_event_structure
```

Currently, it expects JSON output from `step_visualize_event_structure`. You may need to adjust based on your actual output format.

## Next Steps

### Enhance the Visualization

The current implementation shows raw output. To improve:

1. **For DOT format**: Add viz.js or graphviz-wasm
2. **For JSON format**: Create custom SVG renderer or use d3.js
3. **For interactive graphs**: Use Cytoscape.js or vis.js

### Add More Features

- **Syntax highlighting**: Use CodeMirror or Monaco Editor
- **Save/Load**: Add browser localStorage support  
- **Export**: Allow downloading visualizations as SVG/PNG
- **Comparison**: Show multiple event structures side-by-side
- **Cancellation**: Add WebSocket support to cancel long computations

### Improve Backend

- **Progress callbacks**: Modify your core library to accept callbacks
- **Job queue**: For very long computations (>5 min)
- **Caching**: Cache results for repeated analyses
- **Rate limiting**: Prevent abuse

## Troubleshooting

### "Module Eventstructureviz not found"

Make sure `eventstructureviz.ml` is in your `mordor_lib` library's modules list in `src/dune`.

### "Output is not valid JSON"

Check what format your `step_visualize_event_structure` actually produces. You may need to adjust the backend to handle DOT format instead.

### Port 8080 already in use

Change the port in `server.ml`:
```ocaml
Dream.run ~port:3000  (* or any other port *)
```

## Architecture Overview

```
Browser                Web Server              Mordor Core
   |                       |                        |
   |--POST /api/visualize->|                        |
   |                       |--Parse.step_parse----->|
   |<--SSE: "parsing"------|                        |
   |                       |--Interpret.step------->|
   |<--SSE: "interpret"----|                        |
   |                       |--Symmrd.step---------->|
   |<--SSE: "deps"---------|                        |
   |                       |--Viz.step------------->|
   |<--SSE: result---------|<-----------------------|
   |   (close)             |                        |
```

## File Reference

```
your-project/
├── src/                    # Existing core library
│   ├── main.ml            # CLI (unchanged)
│   ├── eventstructureviz.ml
│   └── ...
├── web/                    # New web interface
│   ├── backend/
│   │   ├── server.ml      # Dream server with SSE
│   │   └── dune           # Build config
│   └── frontend/
│       ├── index.html     # Main page
│       └── static/
│           ├── styles.css # UI styles
│           ├── app.js     # Main logic
│           └── examples.js # Sample tests
├── dune-project           # Updated with mordor-web package
└── README.md
```

## Questions?

If you need help with:
- Adjusting the output format handling
- Adding specific visualization features
- Improving the progress tracking
- Deploying the web app

Just ask! The structure is designed to be easy to extend.
