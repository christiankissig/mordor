/**
 * Graph Visualizer for MoRDor
 * Handles visualization and interaction with execution graphs
 */

const EXAMPLES = {
    sb: "name = SB\n%%\n{ x := 1 } ||| { y := 1 }\n%% allow (x = 0 && y = 0) [rc11]",
    mp: "name = MP\n%%\n{ x := 1; y := 1 } ||| { r1 := y; r2 := x }\n%% forbid (r1 = 1 && r2 = 0) [rc11]",
    lb: "name = LB\n%%\n{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }\n%% forbid (r1 = 1 && r2 = 1) [rc11]"
};

// Edge color mapping - moved from backend
const EDGE_COLORS = { 
    po: '#4ec9b0',    // Teal
    rf: '#0e639c',    // Blue
    dp: '#ffa500',    // Orange
    ppo: '#9370db',   // Purple
    rmw: '#f48771',   // Red
    co: '#ffa500',    // Orange
    fr: '#f48771',    // Red
    lo: '#0e639c',    // Blue
    fj: '#89d185',    // Green
    default: '#6a6a6a' 
};

class GraphVisualizer {
    constructor() {
        this.graphs = [];  // Array to store all graphs
        this.currentIndex = 0;
        this.executionCount = 0;

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
                        'shape': 'roundrectangle',
                        'width': 'label',
                        'min-width': '30px',
                        'height': '20px',
                        'padding': '12px',
                        'text-wrap': 'wrap',
                        'text-max-width': '180px'
                    }
                },
                {
                    selector: 'node[isRoot]',
                    style: {
                        'background-color': '#1177bb',
                        'border-width': '3px',
                        'border-color': '#ffffff'
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
                        'arrow-scale': 1.2,
                        'label': 'data(type)',
                        'font-size': '9px',
                        'color': '#cccccc',
                        'text-background-color': '#1e1e1e',
                        'text-background-opacity': 0.8,
                        'text-background-padding': '2px'
                    }
                }
            ],
            layout: { name: 'preset' },
            minZoom: 0.1,
            maxZoom: 3,
            wheelSensitivity: 0.2
        });

        this.setupEventListeners();
        this.setupResizer();
    }

    setupEventListeners() {
        const textarea = document.getElementById('litmus-input');
        const highlight = document.getElementById('litmus-highlight');
        const code = highlight.querySelector('code');
        
        // Update highlighting function
        const updateHighlight = () => {
            code.textContent = textarea.value;
            Prism.highlightElement(code);
        };
        
        // Sync scrolling
        textarea.addEventListener('scroll', () => {
            highlight.scrollTop = textarea.scrollTop;
            highlight.scrollLeft = textarea.scrollLeft;
        });
        
        // Update highlighting on input
        textarea.addEventListener('input', updateHighlight);
        
        document.getElementById('examples').addEventListener('change', (e) => {
            const example = EXAMPLES[e.target.value];
            if (example) {
                textarea.value = example;
                updateHighlight();
                this.log('Example loaded: ' + e.target.options[e.target.selectedIndex].text);
            }
        });

        document.getElementById('visualize-btn').addEventListener('click', () => {
            const program = textarea.value.trim();
            if (!program) {
                this.log('Please enter a litmus test', 'error');
                return;
            }
            this.visualize(program);
        });

        document.getElementById('layout-select').addEventListener('change', (e) => {
            this.applyLayout(e.target.value);
        });

        document.getElementById('fit-btn').addEventListener('click', () => {
            this.cy.fit(null, 50);
            this.log('View reset to fit');
        });

        document.getElementById('export-png-btn').addEventListener('click', () => {
            const png = this.cy.png({ full: true, scale: 2 });
            const link = document.createElement('a');
            link.download = `graph-${this.currentIndex}.png`;
            link.href = png;
            link.click();
            this.log('Graph exported as PNG');
        });

        // Carousel controls
        document.getElementById('prev-btn').addEventListener('click', () => {
            this.navigateTo(this.currentIndex - 1);
        });

        document.getElementById('next-btn').addEventListener('click', () => {
            this.navigateTo(this.currentIndex + 1);
        });
    }

    setupResizer() {
        const resizer = document.getElementById('resizer');
        const leftPanel = document.getElementById('left-panel');
        
        let isResizing = false;
        
        resizer.addEventListener('mousedown', (e) => {
            isResizing = true;
            document.body.style.cursor = 'col-resize';
            document.body.style.userSelect = 'none';
        });
        
        document.addEventListener('mousemove', (e) => {
            if (!isResizing) return;
            
            const containerRect = leftPanel.parentElement.getBoundingClientRect();
            const offsetLeft = e.clientX - containerRect.left;
            const containerWidth = containerRect.width;
            
            let percentage = (offsetLeft / containerWidth) * 100;
            percentage = Math.max(20, Math.min(80, percentage));
            
            leftPanel.style.flex = `0 0 ${percentage}%`;
        });
        
        document.addEventListener('mouseup', () => {
            if (isResizing) {
                isResizing = false;
                document.body.style.cursor = '';
                document.body.style.userSelect = '';
            }
        });
    }

    navigateTo(index) {
        if (index < 0 || index >= this.graphs.length) return;
        
        this.currentIndex = index;
        this.renderGraph(this.graphs[index]);
        this.updateCarouselUI();
    }

    updateCarouselUI() {
        const prevBtn = document.getElementById('prev-btn');
        const nextBtn = document.getElementById('next-btn');
        const indicator = document.getElementById('carousel-indicator');

        prevBtn.disabled = this.currentIndex === 0;
        nextBtn.disabled = this.currentIndex === this.graphs.length - 1;

        if (this.currentIndex === 0) {
            indicator.textContent = 'Event Structure';
        } else {
            indicator.textContent = `Execution ${this.currentIndex}/${this.executionCount}`;
        }
    }

    visualize(program) {
        const steps = parseInt(document.getElementById('step-counter').value) || 5;
        this.log('Starting visualization with ' + steps + ' steps...');
        
        // Reset state
        this.graphs = [];
        this.currentIndex = 0;
        this.executionCount = 0;
        
        document.getElementById('visualize-btn').disabled = true;
        document.getElementById('status').textContent = 'Processing...';

        const params = new URLSearchParams({
            program: program,
            steps: steps.toString()
        });

        const es = new EventSource('/api/visualize/stream?' + params);
        
        es.onmessage = (event) => {
            try {
                const data = JSON.parse(event.data);
                
                if (data.status === 'parsing') {
                    this.log('Parsing litmus test...');
                } else if (data.status === 'interpreting') {
                    this.log('Interpreting program...');
                } else if (data.status === 'visualizing') {
                    this.log('Generating visualizations...');
                } else if (data.type === 'event_structure') {
                    this.log('Received event structure');
                    this.graphs.push(data.graph);
                    if (this.graphs.length === 1) {
                        this.renderGraph(data.graph);
                        this.updateCarouselUI();
                    }
                } else if (data.type === 'execution') {
                    this.log('Received execution ' + data.index);
                    this.graphs.push(data.graph);
                } else if (data.type === 'complete') {
                    this.executionCount = data.total_executions;
                    document.getElementById('execution-count').textContent = this.executionCount;
                    this.log('Visualization complete: ' + this.executionCount + ' executions', 'success');
                    this.updateCarouselUI();
                    document.getElementById('status').textContent = 'Complete';
                    es.close();
                    document.getElementById('visualize-btn').disabled = false;
                } else if (data.error) {
                    this.log('Error: ' + data.error, 'error');
                    this.showError(data.error);
                    es.close();
                    document.getElementById('visualize-btn').disabled = false;
                }
            } catch (e) {
                console.error('Failed to parse SSE message:', e);
                this.log('Parse error: ' + e.message, 'error');
            }
        };

        es.onerror = () => { 
            this.log('Connection error', 'error'); 
            es.close(); 
            document.getElementById('visualize-btn').disabled = false; 
        };
    }

    renderGraph(data) {
        try {
            const graph = data;
            
            this.log('Rendering graph with ' + graph.nodes.length + ' nodes...');

            if (!graph.nodes || graph.nodes.length === 0) {
                this.log('No nodes in graph data', 'error');
                return;
            }

            this.cy.elements().remove();

            // Add nodes
            graph.nodes.forEach(n => {
                let label = '';

                if (n.type && n.location && n.value) {
                    label = n.label + ":" + n.type + ' ' + n.location + ' ' + n.value;
                } else if (n.type && n.location) {
                    label = n.label + ":" + n.type + ' ' + n.location;
                } else if (n.type && n.value) {
                    label = n.label + ":" + n.type + ' ' + n.value;
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
                        label: label,
                        isRoot: n.isRoot
                    }
                });
            });

            // Add edges with color mapping from frontend
            graph.edges.forEach(e => {
                // Extract base edge type (before any " - " predicates)
                const baseType = e.type.split(' - ')[0];
                const color = EDGE_COLORS[baseType] || EDGE_COLORS.default;

                this.cy.add({
                    data: {
                        source: String(e.source),
                        target: String(e.target),
                        type: e.type,
                        color: color
                    }
                });
            });

            // Update stats
            document.getElementById('node-count').textContent = graph.nodes.length;
            document.getElementById('edge-count').textContent = graph.edges.length;

            // Show graph container, hide empty state
            document.getElementById('empty-state').style.display = 'none';
            document.getElementById('carousel-container').style.display = 'flex';
            document.getElementById('graph-controls').style.display = 'flex';
            document.getElementById('graph-stats').style.display = 'block';
            document.getElementById('execution-info').style.display = 'block';

            // Update predicates if available
            if (graph.predicates) {
                document.getElementById('predicates').textContent = graph.predicates;
            } else {
                document.getElementById('predicates').textContent = '⊤';
            }

            this.applyLayout('breadthfirst');
            this.log('Graph rendered successfully');

        } catch (error) {
            this.log('Error rendering graph: ' + error.message, 'error');
            console.error('Render error:', error);
        }
    }

    showError(message) {
        document.getElementById('empty-state').innerHTML = 
            `<div style="color: #f48771; padding: 2rem; text-align: center;">
                <p>${message}</p>
                <p style="margin-top: 1rem; font-size: 0.9rem;">Check the log below for details</p>
            </div>`;
        document.getElementById('empty-state').style.display = 'flex';
        document.getElementById('carousel-container').style.display = 'none';
        document.getElementById('status').textContent = 'Error';
    }

    applyLayout(layoutName) {
        const layouts = {
            breadthfirst: {
                name: 'breadthfirst',
                directed: true,
                padding: 50,
                spacingFactor: 1.2,
                animate: true,
                animationDuration: 500
            },
            fcose: {
                name: 'fcose',
                quality: 'default',
                randomize: false,
                animate: true,
                animationDuration: 500,
                fit: true,
                padding: 50,
                nodeSeparation: 150
            },
            'cose-bilkent': {
                name: 'cose-bilkent',
                randomize: false,
                animate: true,
                animationDuration: 500,
                fit: true,
                padding: 50,
                nodeSeparation: 100
            },
            circle: {
                name: 'circle',
                animate: true,
                animationDuration: 500,
                fit: true,
                padding: 50
            }
        };

        const config = layouts[layoutName] || layouts.breadthfirst;
        const layout = this.cy.layout(config);
        layout.run();

        this.log('Applied ' + layoutName + ' layout');
    }

    log(message, type = 'info') {
        const logDiv = document.getElementById('log');
        const entry = document.createElement('div');
        entry.className = 'log-entry ' + type;
        
        const time = new Date().toLocaleTimeString();
        entry.innerHTML = `<span class="log-time">${time}</span> ${message}`;
        
        logDiv.appendChild(entry);
        logDiv.scrollTop = logDiv.scrollHeight;
    }
}
