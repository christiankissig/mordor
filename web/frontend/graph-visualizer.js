// Mordor Graph Visualizer - High-performance event structure visualization

const EXAMPLES = {
    sb: `name = SB\n%%\n{ x := 1 } ||| { y := 1 }\n%% allow (x = 0 && y = 0) [rc11]`,
    mp: `name = MP\n%%\n{ x := 1; y := 1 } ||| { r1 := y; r2 := x }\n%% forbid (r1 = 1 && r2 = 0) [rc11]`,
    lb: `name = LB\n%%\n{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }\n%% forbid (r1 = 1 && r2 = 1) [rc11]`
};

// Edge type colors
const EDGE_COLORS = {
    po: '#4ec9b0',      // Program Order - teal
    rf: '#0e639c',      // Reads From - blue
    co: '#ffa500',      // Coherence Order - orange
    fr: '#f48771',      // From Read - red
    default: '#6a6a6a'  // Unknown - gray
};

class GraphVisualizer {
    constructor() {
        this.cy = null;
        this.elements = {
            input: document.getElementById('litmus-input'),
            vizBtn: document.getElementById('visualize-btn'),
            status: document.getElementById('status'),
            log: document.getElementById('log'),
            examples: document.getElementById('examples'),
            emptyState: document.getElementById('empty-state'),
            graphControls: document.getElementById('graph-controls'),
            legend: document.getElementById('legend'),
            graphStats: document.getElementById('graph-stats'),
            nodeCount: document.getElementById('node-count'),
            edgeCount: document.getElementById('edge-count'),
            selectedCount: document.getElementById('selected-count'),
            layoutSelect: document.getElementById('layout-select'),
            fitBtn: document.getElementById('fit-btn'),
            centerBtn: document.getElementById('center-btn'),
            exportPngBtn: document.getElementById('export-png-btn'),
            exportJsonBtn: document.getElementById('export-json-btn')
        };
        
        this.currentEventSource = null;
        this.initCytoscape();
        this.initEventListeners();
        this.logInfo('Graph visualizer initialized');
    }
    
    initCytoscape() {
        // Initialize Cytoscape with performance optimizations
        this.cy = cytoscape({
            container: document.getElementById('cy'),
            
            // Styling
            style: [
                {
                    selector: 'node',
                    style: {
                        'background-color': '#0e639c',
                        'label': 'data(label)',
                        'color': '#d4d4d4',
                        'text-valign': 'center',
                        'text-halign': 'center',
                        'font-size': '10px',
                        'width': '30px',
                        'height': '30px',
                        'border-width': 2,
                        'border-color': '#1177bb'
                    }
                },
                {
                    selector: 'node:selected',
                    style: {
                        'background-color': '#ffa500',
                        'border-color': '#ffb733'
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
                        'arrow-scale': 1
                    }
                },
                {
                    selector: 'edge:selected',
                    style: {
                        'width': 3,
                        'line-color': '#ffa500'
                    }
                }
            ],
            
            // Performance settings
            minZoom: 0.1,
            maxZoom: 3,
            wheelSensitivity: 0.2,
            
            // Disable texture during interaction for better performance
            textureOnViewport: false,
            motionBlur: false,
            pixelRatio: 1
        });
        
        // Update stats on selection
        this.cy.on('select unselect', () => this.updateStats());
        
        // Node click handler
        this.cy.on('tap', 'node', (evt) => {
            const node = evt.target;
            this.logInfo(`Selected node: ${node.data('label')} (${node.data('id')})`);
        });
    }
    
    initEventListeners() {
        this.elements.examples.addEventListener('change', (e) => this.loadExample(e.target.value));
        this.elements.vizBtn.addEventListener('click', () => this.visualize());
        this.elements.layoutSelect.addEventListener('change', (e) => this.applyLayout(e.target.value));
        this.elements.fitBtn.addEventListener('click', () => this.cy.fit());
        this.elements.centerBtn.addEventListener('click', () => this.cy.center());
        this.elements.exportPngBtn.addEventListener('click', () => this.exportPNG());
        this.elements.exportJsonBtn.addEventListener('click', () => this.exportJSON());
    }
    
    loadExample(key) {
        if (!key) return;
        this.elements.input.value = EXAMPLES[key];
        this.logInfo(`Loaded example: ${key.toUpperCase()}`);
        this.elements.examples.value = '';
    }
    
    async visualize() {
        const program = this.elements.input.value.trim();
        if (!program) {
            this.logWarning('Please enter a litmus program');
            return;
        }
        
        // Close existing connection
        if (this.currentEventSource) {
            this.currentEventSource.close();
            this.currentEventSource = null;
        }
        
        const steps = parseInt(document.getElementById('step-counter').value) || 5;
        
        this.elements.vizBtn.disabled = true;
        this.elements.status.textContent = 'Processing...';
        this.showLoading();
        this.logInfo('Starting visualization...');
        
        const params = new URLSearchParams({ program, steps: steps.toString() });
        const url = `/api/visualize/stream?${params.toString()}`;
        
        this.currentEventSource = new EventSource(url);
        
        this.currentEventSource.onmessage = (event) => {
            try {
                const data = JSON.parse(event.data);
                
                if (data.error) {
                    this.logError(`Error: ${data.error}`);
                    this.showError(data.error);
                    this.currentEventSource.close();
                    this.elements.vizBtn.disabled = false;
                    return;
                }
                
                if (data.status === 'parsing') {
                    this.logInfo('Parsing...');
                } else if (data.status === 'interpreting') {
                    this.logInfo('Interpreting...');
                } else if (data.status === 'computing_dependencies') {
                    this.logInfo('Computing dependencies...');
                } else if (data.status === 'complete') {
                    this.logSuccess('Complete!');
                    this.renderGraph(data.result);
                    this.elements.status.textContent = 'Complete';
                    this.currentEventSource.close();
                    this.elements.vizBtn.disabled = false;
                }
            } catch (e) {
                this.logError(`Parse error: ${e.message}`);
                console.error('Parse error:', e);
            }
        };
        
        this.currentEventSource.onerror = () => {
            this.logError('Connection error');
            this.showError('Connection failed');
            this.elements.status.textContent = 'Error';
            this.elements.vizBtn.disabled = false;
            if (this.currentEventSource) {
                this.currentEventSource.close();
                this.currentEventSource = null;
            }
        };
    }
    
    renderGraph(data) {
        try {
            // Parse the data - could be JSON string or object
            const graphData = typeof data === 'string' ? JSON.parse(data) : data;
            
            this.logInfo(`Rendering graph: ${JSON.stringify(graphData).substring(0, 100)}...`);
            
            // Convert to Cytoscape format
            const elements = this.convertToElements(graphData);
            
            if (elements.nodes.length === 0) {
                this.logWarning('No nodes in graph data');
                this.showError('No graph data to display');
                return;
            }
            
            // Clear existing graph
            this.cy.elements().remove();
            
            // Add elements
            this.cy.add(elements.nodes);
            this.cy.add(elements.edges);
            
            // Apply layout
            this.applyLayout('fcose');
            
            // Show controls and hide empty state
            this.elements.emptyState.style.display = 'none';
            this.elements.graphControls.style.display = 'flex';
            this.elements.legend.style.display = 'block';
            this.elements.graphStats.style.display = 'block';
            
            this.updateStats();
            this.logSuccess(`Graph rendered: ${elements.nodes.length} nodes, ${elements.edges.length} edges`);
            
        } catch (error) {
            this.logError(`Render error: ${error.message}`);
            console.error('Render error:', error, 'Data:', data);
            this.showError(`Failed to render graph: ${error.message}`);
        }
    }
    
    convertToElements(data) {
        const nodes = [];
        const edges = [];
        
        // Try different data formats
        
        // Format 1: {nodes: [...], edges: [...]}
        if (data.nodes && Array.isArray(data.nodes)) {
            data.nodes.forEach(node => {
                nodes.push({
                    data: {
                        id: node.id || node.name || `node_${nodes.length}`,
                        label: node.label || node.name || node.id || `N${nodes.length}`,
                        ...node
                    }
                });
            });
            
            if (data.edges && Array.isArray(data.edges)) {
                data.edges.forEach(edge => {
                    const edgeType = edge.type || edge.label || 'default';
                    edges.push({
                        data: {
                            id: edge.id || `edge_${edges.length}`,
                            source: edge.source || edge.from,
                            target: edge.target || edge.to,
                            color: EDGE_COLORS[edgeType] || EDGE_COLORS.default,
                            label: edge.label || edgeType,
                            ...edge
                        }
                    });
                });
            }
        }
        // Format 2: {events: [...], relations: [...]}
        else if (data.events && Array.isArray(data.events)) {
            data.events.forEach(event => {
                nodes.push({
                    data: {
                        id: event.id || `e${nodes.length}`,
                        label: event.label || event.name || `E${nodes.length}`,
                        ...event
                    }
                });
            });
            
            if (data.relations && Array.isArray(data.relations)) {
                data.relations.forEach(rel => {
                    const relType = rel.type || 'default';
                    edges.push({
                        data: {
                            id: `edge_${edges.length}`,
                            source: rel.source || rel.from,
                            target: rel.target || rel.to,
                            color: EDGE_COLORS[relType] || EDGE_COLORS.default,
                            label: relType,
                            ...rel
                        }
                    });
                });
            }
        }
        // Format 3: Array of nodes/edges directly
        else if (Array.isArray(data)) {
            data.forEach(item => {
                if (item.group === 'nodes' || !item.data.source) {
                    nodes.push(item);
                } else {
                    edges.push(item);
                }
            });
        }
        
        return { nodes, edges };
    }
    
    applyLayout(layoutName = 'fcose') {
        this.logInfo(`Applying ${layoutName} layout...`);
        
        const layoutConfigs = {
            fcose: {
                name: 'fcose',
                quality: 'default',
                randomize: true,
                animate: true,
                animationDuration: 500,
                fit: true,
                padding: 50,
                nodeSeparation: 100,
                idealEdgeLength: 150,
                edgeElasticity: 0.45,
                numIter: 2500,
                tile: true,
                tilingPaddingVertical: 10,
                tilingPaddingHorizontal: 10,
                gravity: 0.25,
                gravityRange: 3.8
            },
            'cose-bilkent': {
                name: 'cose-bilkent',
                quality: 'proof',
                randomize: true,
                animate: true,
                animationDuration: 1000,
                fit: true,
                padding: 50,
                nodeDimensionsIncludeLabels: true,
                idealEdgeLength: 150,
                edgeElasticity: 0.45,
                nestingFactor: 0.1,
                gravity: 0.25,
                numIter: 2500,
                tile: true
            },
            breadthfirst: {
                name: 'breadthfirst',
                directed: true,
                spacingFactor: 1.5,
                animate: true,
                animationDuration: 500
            },
            circle: {
                name: 'circle',
                animate: true,
                animationDuration: 500
            },
            grid: {
                name: 'grid',
                animate: true,
                animationDuration: 500
            },
            concentric: {
                name: 'concentric',
                animate: true,
                animationDuration: 500,
                minNodeSpacing: 100
            }
        };
        
        const layout = this.cy.layout(layoutConfigs[layoutName] || layoutConfigs.fcose);
        layout.run();
    }
    
    updateStats() {
        const nodeCount = this.cy.nodes().length;
        const edgeCount = this.cy.edges().length;
        const selectedCount = this.cy.$(':selected').length;
        
        this.elements.nodeCount.textContent = nodeCount;
        this.elements.edgeCount.textContent = edgeCount;
        this.elements.selectedCount.textContent = selectedCount;
    }
    
    exportPNG() {
        const png = this.cy.png({
            output: 'blob',
            bg: '#1e1e1e',
            full: true,
            scale: 2
        });
        
        const url = URL.createObjectURL(png);
        const link = document.createElement('a');
        link.href = url;
        link.download = 'event-structure.png';
        link.click();
        URL.revokeObjectURL(url);
        
        this.logSuccess('Exported PNG');
    }
    
    exportJSON() {
        const json = this.cy.json();
        const blob = new Blob([JSON.stringify(json, null, 2)], { type: 'application/json' });
        const url = URL.createObjectURL(blob);
        const link = document.createElement('a');
        link.href = url;
        link.download = 'event-structure.json';
        link.click();
        URL.revokeObjectURL(url);
        
        this.logSuccess('Exported JSON');
    }
    
    showLoading() {
        this.elements.emptyState.innerHTML = `
            <div class="spinner"></div>
            <p style="margin-top: 1rem;">Computing event structure...</p>
        `;
        this.elements.emptyState.style.display = 'flex';
    }
    
    showError(message) {
        this.elements.emptyState.innerHTML = `
            <p style="color: #f48771;">Error: ${message}</p>
        `;
        this.elements.emptyState.style.display = 'flex';
    }
    
    // Logging
    logMessage(msg, type = 'info') {
        const time = new Date().toLocaleTimeString();
        const className = type === 'error' ? 'error' : type === 'success' ? 'success' : 'info';
        this.elements.log.innerHTML += `<div class="log-entry ${className}">[${time}] ${msg}</div>`;
        this.elements.log.scrollTop = this.elements.log.scrollHeight;
    }
    
    logInfo(msg) { this.logMessage(msg, 'info'); }
    logWarning(msg) { this.logMessage(msg, 'warning'); }
    logError(msg) { this.logMessage(msg, 'error'); }
    logSuccess(msg) { this.logMessage(msg, 'success'); }
}

// Initialize when DOM is ready
document.addEventListener('DOMContentLoaded', () => {
    window.graphViz = new GraphVisualizer();
});
