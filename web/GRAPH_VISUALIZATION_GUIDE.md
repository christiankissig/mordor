# Interactive Graph Visualization Guide

## Overview

The new visualization uses **Cytoscape.js**, a high-performance graph visualization library designed for large graphs. It can handle:
- ✅ **500+ nodes**
- ✅ **10,000+ edges**
- ✅ Interactive zoom/pan
- ✅ Multiple layout algorithms
- ✅ Export to PNG/JSON

## Setup

### 1. Copy the New Files

```bash
# Copy the new HTML and JavaScript
cp web/frontend/index-graph.html web/frontend/index.html
cp web/frontend/static/graph-visualizer.js web/frontend/static/

# Update the server
cp web/backend/server-fixed.ml web/backend/server.ml

# Rebuild
dune build
```

### 2. Run the Server

```bash
dune exec mordor-web
```

Open http://localhost:8080

## Features

### Interactive Graph

- **Pan**: Click and drag background
- **Zoom**: Mouse wheel or pinch
- **Select nodes**: Click on nodes
- **Select multiple**: Shift + drag

### Layout Algorithms

**fCoSE (default)** - Fast, force-directed
- Best for: Large graphs (500+ nodes)
- Speed: ⚡⚡⚡ Fast
- Quality: ⭐⭐⭐ Good

**COSE Bilkent** - High-quality force-directed
- Best for: Medium graphs (<200 nodes)
- Speed: ⚡⚡ Medium
- Quality: ⭐⭐⭐⭐ Excellent

**Breadth First** - Hierarchical tree
- Best for: Tree-like structures
- Speed: ⚡⚡⚡ Fast
- Quality: ⭐⭐⭐ Good

**Circle** - Nodes in a circle
- Best for: Small graphs, quick overview
- Speed: ⚡⚡⚡ Instant
- Quality: ⭐⭐ Basic

**Grid** - Regular grid layout
- Best for: Dense graphs
- Speed: ⚡⚡⚡ Instant
- Quality: ⭐⭐ Basic

**Concentric** - Concentric circles
- Best for: Hierarchical data
- Speed: ⚡⚡⚡ Fast
- Quality: ⭐⭐⭐ Good

### Controls

- **Layout dropdown**: Change graph layout
- **Fit to Screen**: Zoom to show entire graph
- **Center**: Center the graph
- **Export PNG**: Download as image (2x resolution)
- **Export JSON**: Save graph data

### Graph Stats

Bottom-left overlay shows:
- Node count
- Edge count  
- Selected element count

### Legend

Shows edge types and their colors:
- **Program Order (po)** - Teal
- **Reads From (rf)** - Blue
- **Coherence (co)** - Orange
- **From Read (fr)** - Red

## Data Format

The visualizer accepts multiple JSON formats:

### Format 1: Standard Graph

```json
{
  "nodes": [
    {"id": "e1", "label": "Write x=1"},
    {"id": "e2", "label": "Read x"}
  ],
  "edges": [
    {"source": "e1", "target": "e2", "type": "rf"}
  ]
}
```

### Format 2: Event Structure

```json
{
  "events": [
    {"id": "e1", "label": "W(x,1)", "thread": 0},
    {"id": "e2", "label": "R(x,1)", "thread": 1}
  ],
  "relations": [
    {"from": "e1", "to": "e2", "type": "rf"}
  ]
}
```

### Format 3: Cytoscape Native

```json
[
  {"data": {"id": "e1", "label": "Event 1"}},
  {"data": {"id": "edge1", "source": "e1", "target": "e2"}}
]
```

## Modifying Your Backend

If your `Eventstructureviz` module outputs DOT format, you'll need to convert it to JSON. Add this to your OCaml code:

### Option 1: Generate JSON Directly

Modify `eventstructureviz.ml` to output JSON:

```ocaml
let to_json structure =
  let nodes = USet.elements structure.e |> List.map (fun event ->
    `Assoc [
      ("id", `String (event_to_string event));
      ("label", `String (event_label event))
    ]
  ) in
  
  let edges = List.concat [
    (* Program order *)
    USet.elements structure.po |> List.map (fun (src, tgt) ->
      `Assoc [
        ("source", `String (event_to_string src));
        ("target", `String (event_to_string tgt));
        ("type", `String "po")
      ]
    );
    (* Reads from *)
    USet.elements structure.rf |> List.map (fun (src, tgt) ->
      `Assoc [
        ("source", `String (event_to_string src));
        ("target", `String (event_to_string tgt));
        ("type", `String "rf")
      ]
    );
    (* Add more edge types... *)
  ] in
  
  `Assoc [
    ("nodes", `List nodes);
    ("edges", `List edges)
  ]
```

### Option 2: Convert DOT to JSON

If you have DOT output, parse it server-side (requires `ocamlgraph`):

```ocaml
(* In server.ml *)
let dot_to_json dot_string =
  (* Parse DOT and convert to JSON *)
  (* This is pseudocode - actual implementation depends on your DOT structure *)
  ...
```

### Option 3: Convert DOT to JSON in JavaScript

Parse DOT client-side (less efficient):

```javascript
// In graph-visualizer.js
function parseDot(dotString) {
    // Use a DOT parser library or write custom parser
    // Return {nodes: [...], edges: [...]}
}
```

## Performance Tips

### For Large Graphs (500+ nodes)

1. **Use fCoSE layout** - It's optimized for large graphs
2. **Disable texture during viewport** - Already configured
3. **Use lower quality during interaction**:
   ```javascript
   cy.userZoomingEnabled(false); // During layout
   layout.run();
   layout.on('layoutstop', () => {
       cy.userZoomingEnabled(true);
   });
   ```

### For Very Large Graphs (1000+ nodes)

Consider:
1. **Filtering/clustering** - Show subsets of the graph
2. **Virtualization** - Only render visible nodes
3. **Simplification** - Reduce edge count
4. **Progressive rendering** - Load in chunks

### Memory Optimization

```javascript
// Clear old graph before loading new one
cy.elements().remove();
cy.add(newElements);
```

## Customization

### Change Node Colors

Edit `graph-visualizer.js`:

```javascript
{
    selector: 'node',
    style: {
        'background-color': '#your-color',
        'border-color': '#your-border-color'
    }
}
```

### Change Edge Colors

Edit the `EDGE_COLORS` object:

```javascript
const EDGE_COLORS = {
    po: '#4ec9b0',
    rf: '#0e639c',
    co: '#ffa500',
    fr: '#f48771',
    mytype: '#ff00ff'  // Add custom type
};
```

### Add Node Tooltips

```javascript
cy.on('mouseover', 'node', (evt) => {
    const node = evt.target;
    // Show tooltip with node.data()
});
```

## Troubleshooting

### Graph Doesn't Appear

1. Check browser console for errors
2. Verify JSON format in server logs
3. Check that `convertToElements()` recognizes your data format

### Layout is Messy

1. Try different layout algorithms
2. Adjust layout parameters in `applyLayout()`
3. For hierarchical data, use breadthfirst

### Performance Issues

1. Check node/edge count in stats
2. Use fCoSE for >100 nodes
3. Consider filtering large graphs

### Edges Not Colored

1. Check that edge data has `type` field
2. Verify edge type exists in `EDGE_COLORS`
3. Check browser console for warnings

## Examples

### Simple Graph

```json
{
  "nodes": [
    {"id": "1", "label": "A"},
    {"id": "2", "label": "B"}
  ],
  "edges": [
    {"source": "1", "target": "2", "type": "po"}
  ]
}
```

### Complex Graph

```json
{
  "nodes": [
    {"id": "e1", "label": "W(x,1)", "thread": 0, "location": "x"},
    {"id": "e2", "label": "R(x,1)", "thread": 1, "location": "x"},
    {"id": "e3", "label": "W(y,1)", "thread": 0, "location": "y"},
    {"id": "e4", "label": "R(y,1)", "thread": 1, "location": "y"}
  ],
  "edges": [
    {"source": "e1", "target": "e3", "type": "po"},
    {"source": "e2", "target": "e4", "type": "po"},
    {"source": "e1", "target": "e2", "type": "rf"},
    {"source": "e3", "target": "e4", "type": "rf"}
  ]
}
```

## Next Steps

1. **Test with your actual data format**
2. **Adjust `convertToElements()` if needed**
3. **Customize colors and styling**
4. **Add additional node/edge metadata**
5. **Implement filtering for large graphs**
