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
    uaf: '#ff0000',   // Bright Red for use-after-free
    default: '#6a6a6a' 
};

class GraphVisualizer {
    constructor() {
        this.graphs = [];  // Array to store all graphs
        this.currentIndex = 0;
        this.executionCount = 0;
        this.lastProgram = null; // Store last program for regeneration
        
        // Settings
        this.settings = {
            showUAF: false,
            showUnboundedDeref: false
        };

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
        this.setupGraphInteractions();
    }

    setupGraphInteractions() {
        // Log node label on hover
        this.cy.on('mouseover', 'node', (event) => {
            const node = event.target;
            const label = node.data('label');
            this.log('Node: ' + label, 'info');
        });
    }
    
    openSettingsModal() {
        // Populate current settings
        document.getElementById('show-uaf').checked = this.settings.showUAF;
        document.getElementById('show-unbounded-deref').checked = this.settings.showUnboundedDeref;
        document.getElementById('settings-modal').classList.add('show');
    }
    
    closeSettingsModal() {
        document.getElementById('settings-modal').classList.remove('show');
    }
    
    applySettings() {
        // Read settings from checkboxes
        this.settings.showUAF = document.getElementById('show-uaf').checked;
        this.settings.showUnboundedDeref = document.getElementById('show-unbounded-deref').checked;
        
        this.closeSettingsModal();
        this.log('Settings updated', 'success');
        
        // Regenerate if we have a program
        if (this.lastProgram) {
            this.log('Regenerating graphs with new settings...', 'info');
            this.visualize(this.lastProgram);
        }
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
        
        // Settings modal
        document.getElementById('settings-btn').addEventListener('click', () => {
            this.openSettingsModal();
        });
        
        document.getElementById('close-modal').addEventListener('click', () => {
            this.closeSettingsModal();
        });
        
        document.getElementById('cancel-settings').addEventListener('click', () => {
            this.closeSettingsModal();
        });
        
        document.getElementById('apply-settings').addEventListener('click', () => {
            this.applySettings();
        });
        
        // Close modal on outside click
        document.getElementById('settings-modal').addEventListener('click', (e) => {
            if (e.target.id === 'settings-modal') {
                this.closeSettingsModal();
            }
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

    updateExecutionInfo(data) {
        // Handle case where data might be undefined (event structure)
        if (!data) {
            document.getElementById('predicates').textContent = '⊤';
            document.getElementById('has-uaf').textContent = 'N/A';
            document.getElementById('has-uaf').style.color = '#d4d4d4';
            document.getElementById('has-unbounded-deref').textContent = 'N/A';
            document.getElementById('has-unbounded-deref').style.color = '#d4d4d4';
            return;
        }
        
        console.log('updateExecutionInfo called with data:', data);
        
        // Always update predicates
        const preds = data.preds || "⊤";
        document.getElementById('predicates').textContent = preds;
     
        // undefined_behaviour is an array, so we need to access the first element
        if (data.undefined_behaviour !== undefined && data.undefined_behaviour.length > 0) {
          const ub_reasons = data.undefined_behaviour[0]; // Get first element of array
          console.log('undefined_behaviour:', ub_reasons);

          // Handle UAF with detailed pair information
          const uafSpan = document.getElementById('has-uaf');
          if (ub_reasons.uaf && ub_reasons.uaf.length > 0) {
              console.log('UAF pairs found:', ub_reasons.uaf);
              
              // Get the graph - it should be in data.graph
              const graph = data.graph || this.graphs[this.currentIndex];
              console.log('Graph for UAF lookup:', graph);
              
              // Format UAF pairs as "4:D 三 -> 8:R 三 δ"
              const uafPairs = ub_reasons.uaf.map(pair => {
                  const sourceNode = graph.nodes.find(n => n.id === pair[0]);
                  const targetNode = graph.nodes.find(n => n.id === pair[1]);
                  
                  console.log(`Looking for nodes ${pair[0]} and ${pair[1]}:`, sourceNode, targetNode);
                  
                  let sourceLabel = pair[0];
                  let targetLabel = pair[1];
                  
                  if (sourceNode) {
                      sourceLabel = `${sourceNode.label}:${sourceNode.type}${sourceNode.location ? ' ' + sourceNode.location : ''}`;
                  }
                  if (targetNode) {
                      targetLabel = `${targetNode.label}:${targetNode.type}${targetNode.location ? ' ' + targetNode.location : ''}${targetNode.value ? ' ' + targetNode.value : ''}`;
                  }
                  
                  return `${sourceLabel} → ${targetLabel}`;
              }).join(', ');
              
              console.log('UAF pairs formatted:', uafPairs);
              uafSpan.textContent = uafPairs;
              uafSpan.style.color = '#ff6b6b';
          } else {
              // No UAF in this execution
              uafSpan.textContent = 'No';
              uafSpan.style.color = '#89d185';
          }

          // Handle unbounded deref
          const unboundedSpan = document.getElementById('has-unbounded-deref');
          if (ub_reasons.unbounded_deref) {
              unboundedSpan.textContent = 'Yes';
              unboundedSpan.style.color = '#ff6b6b';
          } else {
              unboundedSpan.textContent = 'No';
              unboundedSpan.style.color = '#89d185';
          }
        } else {
            // No undefined behaviour data - reset to "No" for executions
            const uafSpan = document.getElementById('has-uaf');
            uafSpan.textContent = 'No';
            uafSpan.style.color = '#89d185';
            
            const unboundedSpan = document.getElementById('has-unbounded-deref');
            unboundedSpan.textContent = 'No';
            unboundedSpan.style.color = '#89d185';
        }
    }

    navigateTo(index) {
        if (index < 0 || index >= this.graphs.length) return;
        
        this.currentIndex = index;
        
        // For event structure (index 0), don't pass undefined_behaviour
        if (index === 0) {
            this.renderGraph(this.graphs[index], null);
            // Reset execution info for event structure
            document.getElementById('predicates').textContent = '⊤';
            document.getElementById('has-uaf').textContent = 'N/A';
            document.getElementById('has-uaf').style.color = '#d4d4d4';
            document.getElementById('has-unbounded-deref').textContent = 'N/A';
            document.getElementById('has-unbounded-deref').style.color = '#d4d4d4';
        } else {
            // For executions, pass undefined_behaviour data if available (it's an array, so get first element)
            const undefinedBehaviour = (this.data[index]?.undefined_behaviour && this.data[index].undefined_behaviour.length > 0) 
                ? this.data[index].undefined_behaviour[0] 
                : null;
            this.renderGraph(this.graphs[index], undefinedBehaviour);
            this.updateExecutionInfo(this.data[index]);
        }
        
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
        
        // Store program for regeneration
        this.lastProgram = program;
        
        // Reset state
        this.graphs = [];
        this.data = [];
        this.currentIndex = 0;
        this.executionCount = 0;
        
        // Clear execution info fields
        document.getElementById('predicates').textContent = '⊤';
        document.getElementById('has-uaf').textContent = 'N/A';
        document.getElementById('has-uaf').style.color = '#d4d4d4';
        document.getElementById('has-unbounded-deref').textContent = 'N/A';
        document.getElementById('has-unbounded-deref').style.color = '#d4d4d4';
        
        // Clear graph stats
        document.getElementById('node-count').textContent = '0';
        document.getElementById('edge-count').textContent = '0';
        document.getElementById('execution-count').textContent = '0';
        
        document.getElementById('visualize-btn').disabled = true;
        document.getElementById('status').textContent = 'Processing...';

        const params = new URLSearchParams({
            program: program,
            steps: steps.toString(),
            show_uaf: this.settings.showUAF.toString(),
            show_unbounded_deref: this.settings.showUnboundedDeref.toString()
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
                    this.data.push(data);
                    if (this.graphs.length === 1) {
                        this.renderGraph(data.graph);
                        this.updateCarouselUI();
                    }
                } else if (data.type === 'execution') {
                    this.log('Received execution ' + data.index);
                    this.graphs.push(data.graph);
                    this.data.push(data);
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

    renderGraph(graph, undefinedBehaviour = null) {
        try {
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

            // Add UAF edges if undefined_behaviour data is provided
            let uafEdgeCount = 0;
            if (undefinedBehaviour && undefinedBehaviour.uaf && undefinedBehaviour.uaf.length > 0) {
                console.log('Adding UAF edges for pairs:', undefinedBehaviour.uaf);
                undefinedBehaviour.uaf.forEach(pair => {
                    console.log(`Adding UAF edge from ${pair[0]} to ${pair[1]}`);
                    this.cy.add({
                        data: {
                            source: String(pair[0]),
                            target: String(pair[1]),
                            type: 'uaf',
                            color: EDGE_COLORS.uaf
                        }
                    });
                    uafEdgeCount++;
                });
                this.log(`Added ${uafEdgeCount} UAF edge(s)`, 'info');
            } else {
                console.log('No UAF edges to add. undefinedBehaviour:', undefinedBehaviour);
            }

            // Update stats (including UAF edges in edge count)
            document.getElementById('node-count').textContent = graph.nodes.length;
            document.getElementById('edge-count').textContent = graph.edges.length + uafEdgeCount;

            // Show graph container, hide empty state
            document.getElementById('empty-state').style.display = 'none';
            document.getElementById('carousel-container').style.display = 'flex';
            document.getElementById('graph-controls').style.display = 'flex';
            document.getElementById('graph-stats').style.display = 'block';
            document.getElementById('execution-info').style.display = 'block';

            this.applyLayout('breadthfirst');
            
            // Fit the first graph automatically
            if (this.currentIndex === 0) {
                this.cy.fit(null, 50);
            }
            
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
