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
        this.highlightMarker = null; // Store current highlight element
        this.loops = []; // Store loop information
        this.episodicityResults = {}; // Store episodicity results by loop_id
        this.assertionResults = null; // Store assertion results
        this.currentEndpoint = '/api/visualize/stream'; // Default endpoint
        this.currentAction = 'visualize'; // Default action
        this.visibleRelations = null; // null means all visible
        this.availableRelations = new Set(); // track which relation types exist

        // Settings
        this.settings = {
            showUAF: false,
            showUnboundedDeref: false,
            loopSemantics: 'step-counter',  // 'step-counter' or 'symbolic'
            stepCounter: 2
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
        // Highlight source code on node hover
        this.cy.on('mouseover', 'node', (event) => {
            const node = event.target;
            const nodeData = node.data();
            
            this.log('Node: ' + nodeData.label, 'info');
            
            // Highlight corresponding source code if span information exists
            if (nodeData.source_start_line !== undefined && 
                nodeData.source_start_col !== undefined &&
                nodeData.source_end_line !== undefined &&
                nodeData.source_end_col !== undefined) {
                this.highlightSourceSpan(
                    nodeData.source_start_line,
                    nodeData.source_start_col,
                    nodeData.source_end_line,
                    nodeData.source_end_col
                );
            }
        });
        
        // Remove highlight when mouse leaves node
        this.cy.on('mouseout', 'node', () => {
            this.clearSourceHighlight();
        });
    }
    
    highlightSourceSpan(startLine, startCol, endLine, endCol, color = 'rgba(255, 215, 0, 0.25)', borderColor = 'rgba(255, 215, 0, 0.5)') {
        // Clear any existing highlight
        this.clearSourceHighlight();
        
        const textarea = document.getElementById('litmus-input');
        const highlightPre = document.getElementById('litmus-highlight');
        
        if (!textarea || !highlightPre) return;
        
        const lines = textarea.value.split('\n');
        
        // Validate line numbers
        if (startLine < 1 || startLine > lines.length || endLine < 1 || endLine > lines.length) {
            console.warn('Invalid line numbers:', startLine, endLine);
            return;
        }
        
        // Create a container for highlight overlays
        if (!this.highlightContainer) {
            this.highlightContainer = document.createElement('div');
            this.highlightContainer.id = 'source-highlight-overlay';
            this.highlightContainer.style.cssText = `
                position: absolute;
                top: 1em;
                left: 5.5em;
                right: 0;
                bottom: 0;
                pointer-events: none;
                z-index: 2;
                margin: 0 !important;
                padding: 1rem 1rem 1rem 5.5em !important;
                font-family: 'Consolas', 'Courier New', monospace !important;
                font-size: 0.95rem !important;
                line-height: 1.5 !important;
                white-space: pre-wrap;
                word-wrap: break-word;
                overflow: hidden;
                background: transparent !important;
            `;
            document.querySelector('.editor-wrapper').appendChild(this.highlightContainer);
        }
        
        // Calculate line height
        const lineHeight = parseFloat(window.getComputedStyle(textarea).lineHeight) || 21.6; // 0.95rem * 1.5 * 16px
        
        // Handle single-line vs multi-line highlights
        if (startLine === endLine) {
            // Single line highlight
            const marker = document.createElement('div');
            marker.className = 'highlight-marker';
            
            const lineText = lines[startLine - 1];
            const beforeText = lineText.substring(0, startCol);
            const highlightText = lineText.substring(startCol, endCol);
            
            // Calculate character width (approximate for monospace)
            const charWidth = 9.5 * 0.95; // Rough estimate for Consolas at 0.95rem
            
            const topPos = (startLine - 1) * lineHeight;
            const leftPos = beforeText.length * charWidth;
            const width = highlightText.length * charWidth;
            
            marker.style.cssText = `
                position: absolute;
                top: ${topPos}px;
                left: ${leftPos}px;
                width: ${width}px;
                height: ${lineHeight}px;
                background-color: ${color};
                border: 1px solid ${borderColor};
                box-sizing: border-box;
            `;
            
            this.highlightContainer.appendChild(marker);
            this.highlightMarkers = [marker];
        } else {
            // Multi-line highlight
            this.highlightMarkers = [];
            
            for (let lineNum = startLine; lineNum <= endLine; lineNum++) {
                const marker = document.createElement('div');
                marker.className = 'highlight-marker';
                
                const lineText = lines[lineNum - 1];
                let startColForLine, endColForLine;
                
                if (lineNum === startLine) {
                    startColForLine = startCol;
                    endColForLine = lineText.length;
                } else if (lineNum === endLine) {
                    startColForLine = 0;
                    endColForLine = endCol;
                } else {
                    startColForLine = 0;
                    endColForLine = lineText.length;
                }
                
                const beforeText = lineText.substring(0, startColForLine);
                const highlightText = lineText.substring(startColForLine, endColForLine);
                
                const charWidth = 9.5 * 0.95;
                const topPos = (lineNum - 1) * lineHeight;
                const leftPos = beforeText.length * charWidth;
                const width = highlightText.length * charWidth;
                
                marker.style.cssText = `
                    position: absolute;
                    top: ${topPos}px;
                    left: ${leftPos}px;
                    width: ${width}px;
                    height: ${lineHeight}px;
                    background-color: ${color};
                    border: 1px solid ${borderColor};
                    box-sizing: border-box;
                `;
                
                this.highlightContainer.appendChild(marker);
                this.highlightMarkers.push(marker);
            }
        }
        
        // Scroll the highlighted area into view
        const topPos = (startLine - 1) * lineHeight;
        const containerHeight = textarea.clientHeight;
        const scrollTop = Math.max(0, topPos - containerHeight / 3);
        
        textarea.scrollTop = scrollTop;
        highlightPre.scrollTop = scrollTop;
    }
    
    clearSourceHighlight() {
        if (this.highlightMarkers) {
            this.highlightMarkers.forEach(marker => {
                if (marker.parentElement) {
                    marker.parentElement.removeChild(marker);
                }
            });
            this.highlightMarkers = null;
        }
        if (this.highlightContainer) {
            this.highlightContainer.innerHTML = '';
        }
    }
    
    renderLoops() {
        const loopsContent = document.getElementById('loops-content');
        
        if (!this.loops || this.loops.length === 0) {
            loopsContent.innerHTML = '<p style="padding: 1rem; color: #6a6a6a;">No loops detected</p>';
            return;
        }
        
        let html = '<div style="padding: 0.5rem;">';
        this.loops.forEach(loop => {
            const episodicityData = this.episodicityResults[loop.id];
            
            html += `
                <div class="loop-item" 
                     data-loop-id="${loop.id}"
                     data-start-line="${loop.start_line}" 
                     data-start-col="${loop.start_col}"
                     data-end-line="${loop.end_line}" 
                     data-end-col="${loop.end_col}"
                     style="padding: 0.75rem; margin: 0.5rem 0; background: #252526; border: 1px solid #3e3e42; border-radius: 4px; cursor: pointer; transition: background 0.2s;">
                    <div class="loop-header" style="display: flex; justify-content: space-between; align-items: center;">
                        <div style="display: flex; align-items: center; gap: 0.75rem;">
                            <strong style="color: #4ec9b0;">Loop ${loop.id}</strong>
                            ${episodicityData ? `<span style="font-size: 0.85rem; color: ${episodicityData.is_episodic ? '#89d185' : '#f48771'}; font-weight: bold;">${episodicityData.is_episodic ? '✓ Episodic' : '✗ Non-episodic'}</span>` : ''}
                        </div>
                        ${episodicityData ? '<span class="loop-toggle">▼</span>' : ''}
                    </div>
                    <div style="font-size: 0.85rem; color: #6a6a6a; margin-top: 0.25rem;">
                        Lines ${loop.start_line}:${loop.start_col} - ${loop.end_line}:${loop.end_col}
                    </div>
            `;
            
            // Add episodicity conditions if available
            if (episodicityData) {
                html += '<div class="loop-conditions" style="margin-top: 0.75rem; padding-top: 0.75rem; border-top: 1px solid #3e3e42;">';
                html += '<div style="font-size: 0.85rem; color: #cccccc; margin-bottom: 0.5rem; font-weight: bold;">Episodicity Conditions:</div>';
                
                ['condition1', 'condition2', 'condition3', 'condition4'].forEach((condName, index) => {
                    const cond = episodicityData[condName];
                    if (cond) {
                        const satisfied = cond.satisfied;
                        const icon = satisfied ? '✓' : '✗';
                        const color = satisfied ? '#89d185' : '#f48771';
                        const hasViolations = !satisfied && cond.violations && cond.violations.length > 0;
                        
                        html += `
                            <div class="episodicity-condition" data-condition="${condName}" style="margin: 0.4rem 0; padding: 0.4rem; background: #1e1e1e; border-radius: 3px;">
                                <div class="condition-header" style="display: flex; align-items: center; justify-content: space-between; gap: 0.5rem;">
                                    <div style="display: flex; align-items: center; gap: 0.5rem;">
                                        <span style="color: ${color}; font-weight: bold; min-width: 20px;">${icon}</span>
                                        <span style="color: #d4d4d4; font-size: 0.85rem;">Condition ${index + 1}</span>
                                    </div>
                                    ${hasViolations ? '<span class="condition-toggle">▼</span>' : ''}
                                </div>
                        `;
                        
                        // Show violations if any
                        if (hasViolations) {
                            html += '<div class="condition-violations">';
                            cond.violations.forEach(violation => {
                                const violationType = violation[0];
                                const violationDetails = violation[1];
                                
                                html += `<div style="font-size: 0.8rem; color: #f48771; margin: 0.2rem 0;">`;
                                
                                if (Array.isArray(violationDetails)) {
                                    const [reason, register, span] = violationDetails;
                                    html += `${this.formatViolationType(violationType)}: ${reason}`;
                                    if (register) {
                                        html += ` (${register})`;
                                    }
                                    if (span && span.start_line) {
                                        html += ` at ${span.start_line}:${span.start_col}`;
                                    }
                                } else {
                                    html += `${this.formatViolationType(violationType)}`;
                                }
                                
                                html += '</div>';
                            });
                            html += '</div>';
                        }
                        
                        html += '</div>';
                    }
                });
                
                html += '</div>';
            }
            
            html += '</div>';
        });
        html += '</div>';
        
        loopsContent.innerHTML = html;
        
        // Add click listeners for collapsible loops
        const loopHeaders = loopsContent.querySelectorAll('.loop-header');
        loopHeaders.forEach(header => {
            header.addEventListener('click', (e) => {
                e.stopPropagation();
                const loopItem = header.closest('.loop-item');
                loopItem.classList.toggle('expanded');
            });
        });
        
        // Add click listeners for collapsible conditions
        const conditionHeaders = loopsContent.querySelectorAll('.condition-header');
        conditionHeaders.forEach(header => {
            header.addEventListener('click', (e) => {
                e.stopPropagation();
                const condition = header.closest('.episodicity-condition');
                condition.classList.toggle('expanded');
            });
        });
        
        // Add hover listeners to loop items
        const loopItems = loopsContent.querySelectorAll('.loop-item');
        loopItems.forEach(item => {
            item.addEventListener('mouseenter', () => {
                const startLine = parseInt(item.getAttribute('data-start-line'));
                const startCol = parseInt(item.getAttribute('data-start-col'));
                const endLine = parseInt(item.getAttribute('data-end-line'));
                const endCol = parseInt(item.getAttribute('data-end-col'));
                
                // Highlight with green color
                this.highlightSourceSpan(
                    startLine, 
                    startCol, 
                    endLine, 
                    endCol,
                    'rgba(76, 201, 176, 0.25)',  // Green background
                    'rgba(76, 201, 176, 0.5)'     // Green border
                );
                
                // Visual feedback on the loop item
                item.style.background = '#2d2d30';
            });
            
            item.addEventListener('mouseleave', () => {
                this.clearSourceHighlight();
                item.style.background = '#252526';
            });
        });
    }
    
    formatViolationType(type) {
        // Convert camelCase/PascalCase to readable format
        return type.replace(/([A-Z])/g, ' $1').trim();
    }
    
    renderAssertions() {
        const assertionsContent = document.getElementById('assertions-content');
        
        if (!this.assertionResults) {
            assertionsContent.innerHTML = '<p style="padding: 1rem; color: #6a6a6a;">No assertion results available.</p>';
            return;
        }
        
        let html = '';
        
        // Add overall validity status
        const validityClass = this.assertionResults.valid ? 'valid' : 'invalid';
        const validityIcon = this.assertionResults.valid ? '✓' : '✗';
        const validityText = this.assertionResults.valid ? 'Valid' : 'Invalid';
        
        html += `
            <div class="assertion-validity ${validityClass}">
                <span class="assertion-validity-icon">${validityIcon}</span>
                <span><strong>Overall Validity:</strong> ${validityText}</span>
            </div>
        `;
        
        // Render each assertion instance
        html += '<div style="max-height: 400px; overflow-y: auto;">';
        
        if (this.assertionResults.instances && this.assertionResults.instances.length > 0) {
            this.assertionResults.instances.forEach((instance, index) => {
                const [type, data] = instance;
                const detail = data.detail;
                const execId = data.exec_id;
                
                // Determine the type and styling
                let typeClass = type.toLowerCase();
                let typeIcon = '';
                switch(type) {
                    case 'Witnessed':
                        typeIcon = '✓';
                        break;
                    case 'Contradicted':
                        typeIcon = '✗';
                        break;
                    case 'Confirmed':
                        typeIcon = '✓✓';
                        break;
                    case 'Refuted':
                        typeIcon = '✗✗';
                        break;
                }
                
                html += `
                    <div class="assertion-item" data-exec-id="${execId}">
                        <div class="assertion-header">
                            <span class="assertion-type ${typeClass}">${typeIcon} ${type}</span>
                            <span class="assertion-exec-id">Execution ${execId}</span>
                        </div>
                `;
                
                // Show instantiated expression if available
                if (detail.instantiated_expr) {
                    html += `
                        <div class="assertion-expr">${this.escapeHtml(detail.instantiated_expr)}</div>
                    `;
                }
                
                // Show result
                const resultClass = detail.result ? 'true' : 'false';
                const resultIcon = detail.result ? '✓' : '✗';
                html += `
                    <div class="assertion-result ${resultClass}">
                        <span class="assertion-result-icon">${resultIcon}</span>
                        <span>Result: ${detail.result ? 'True' : 'False'}</span>
                    </div>
                `;
                
                // Show set memberships if any
                if (detail.set_memberships && detail.set_memberships.length > 0) {
                    html += `
                        <div class="assertion-memberships">
                            <div class="assertion-memberships-title">Set Memberships:</div>
                    `;
                    
                    detail.set_memberships.forEach(membership => {
                        const memberClass = membership.member ? 'true' : 'false';
                        const memberIcon = membership.member ? '∈' : '∉';
                        const [evt1, evt2] = membership.event_pair;
                        
                        html += `
                            <div class="membership-item">
                                <span class="membership-pair">(${evt1}, ${evt2})</span>
                                <span class="membership-relation">.${membership.relation_name}</span>
                                <span class="membership-result ${memberClass}">${memberIcon}</span>
                            </div>
                        `;
                    });
                    
                    html += '</div>';
                }
                
                html += '</div>';
            });
        } else {
            html += '<p style="padding: 1rem; color: #6a6a6a;">No assertion instances to display.</p>';
        }
        
        html += '</div>';
        
        assertionsContent.innerHTML = html;
        
        // Add click listeners to assertion items to navigate to execution
        const assertionItems = assertionsContent.querySelectorAll('.assertion-item');
        assertionItems.forEach(item => {
            item.addEventListener('click', () => {
                const execId = parseInt(item.getAttribute('data-exec-id'));
                // Find the carousel index whose data.index matches the execution id
                const carouselIndex = this.data.findIndex(d => d.index > 0 && d.index === execId);
                if (carouselIndex >= 0) {
                    this.navigateTo(carouselIndex);
                }
            });
            
            // Visual feedback on hover
            item.addEventListener('mouseenter', () => {
                item.style.background = '#2d2d30';
            });
            
            item.addEventListener('mouseleave', () => {
                item.style.background = '';
            });
        });
    }
    
    escapeHtml(text) {
        const div = document.createElement('div');
        div.textContent = text;
        return div.innerHTML;
    }
    
    openSettingsModal() {
        // Populate current settings
        document.getElementById('show-uaf').checked = this.settings.showUAF;
        document.getElementById('show-unbounded-deref').checked = this.settings.showUnboundedDeref;
        
        // Populate loop semantics settings
        if (this.settings.loopSemantics === 'step-counter') {
            document.getElementById('step-counter-semantics').checked = true;
        } else {
            document.getElementById('symbolic-semantics').checked = true;
        }
        document.getElementById('step-counter').value = this.settings.stepCounter;
        
        // Enable/disable step counter input based on selection
        this.updateStepCounterState();
        
        document.getElementById('settings-modal').classList.add('active');
    }
    
    closeSettingsModal() {
        document.getElementById('settings-modal').classList.remove('active');
    }
    
    applySettings() {
        // Read settings from checkboxes
        this.settings.showUAF = document.getElementById('show-uaf').checked;
        this.settings.showUnboundedDeref = document.getElementById('show-unbounded-deref').checked;
        
        // Read loop semantics settings
        if (document.getElementById('step-counter-semantics').checked) {
            this.settings.loopSemantics = 'step-counter';
            this.settings.stepCounter = parseInt(document.getElementById('step-counter').value) || 2;
        } else {
            this.settings.loopSemantics = 'symbolic';
        }
        
        this.closeSettingsModal();
        this.log('Settings updated: ' + this.settings.loopSemantics + 
                 (this.settings.loopSemantics === 'step-counter' ? ' (' + this.settings.stepCounter + ' steps)' : ''), 
                 'success');
        
        // Regenerate if we have a program
        if (this.lastProgram) {
            this.log('Regenerating graphs with new settings...', 'info');
            this.visualize(this.lastProgram);
        }
    }
    
    updateStepCounterState() {
        const stepCounterInput = document.getElementById('step-counter');
        const isStepCounterMode = document.getElementById('step-counter-semantics').checked;
        stepCounterInput.disabled = !isStepCounterMode;
        stepCounterInput.style.opacity = isStepCounterMode ? '1' : '0.5';
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

        // Split button functionality
        const actionBtn = document.getElementById('action-btn');
        const dropdownToggle = document.getElementById('dropdown-toggle');
        const splitButton = document.querySelector('.split-button');
        const dropdownItems = document.querySelectorAll('.dropdown-content button');
        
        // Main action button - executes the current action
        actionBtn.addEventListener('click', () => {
            const program = textarea.value.trim();
            if (!program) {
                this.log('Please enter a litmus test', 'error');
                return;
            }
            this.visualize(program);
        });
        
        // Toggle button - shows/hides dropdown
        dropdownToggle.addEventListener('click', (e) => {
            e.stopPropagation();
            splitButton.classList.toggle('active');
        });
        
        // Close dropdown when clicking outside
        document.addEventListener('click', () => {
            splitButton.classList.remove('active');
        });
        
        // Handle dropdown item selection
        dropdownItems.forEach(item => {
            item.addEventListener('click', (e) => {
                e.stopPropagation();
                const action = item.getAttribute('data-action');
                const endpoint = item.getAttribute('data-endpoint');
                
                // Update button text and store current endpoint
                actionBtn.textContent = item.textContent;
                this.currentEndpoint = endpoint;
                this.currentAction = action;
                
                // Close dropdown
                splitButton.classList.remove('active');
                
                // Log the selection
                this.log('Action changed to: ' + action, 'info');
            });
        });

        const layoutWrapper = document.getElementById('layout-dropdown-wrapper');
        const layoutBtn = document.getElementById('layout-dropdown-btn');
        const layoutContent = document.getElementById('layout-dropdown-content');

        layoutBtn.addEventListener('click', (e) => {
            e.stopPropagation();
            const isOpen = layoutWrapper.classList.contains('open');
            if (!isOpen) {
                layoutWrapper.classList.add('open');
                layoutBtn.textContent = layoutBtn.textContent.replace('▲', '▼');
                const rect = layoutBtn.getBoundingClientRect();
                requestAnimationFrame(() => {
                    layoutContent.style.top = (rect.top - layoutContent.offsetHeight - 4) + 'px';
                    layoutContent.style.left = rect.left + 'px';
                });
            } else {
                layoutWrapper.classList.remove('open');
                layoutBtn.textContent = layoutBtn.textContent.replace('▼', '▲');
            }
        });

        document.addEventListener('click', (e) => {
            if (!layoutWrapper.contains(e.target)) {
                layoutWrapper.classList.remove('open');
                layoutBtn.textContent = layoutBtn.textContent.replace('▼', '▲');
            }
        });

        layoutContent.querySelectorAll('.layout-option').forEach(option => {
            option.addEventListener('click', (e) => {
                e.stopPropagation();
                const value = option.dataset.value;
                const label = option.textContent;
                layoutContent.querySelectorAll('.layout-option').forEach(o => o.classList.remove('active'));
                option.classList.add('active');
                layoutBtn.textContent = label + ' ▲';
                layoutWrapper.classList.remove('open');
                this.applyLayout(value);
            });
        });

        // Set initial active
        layoutContent.querySelector('.layout-option[data-value="breadthfirst"]').classList.add('active');

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
        
        // Add listeners for loop semantics radio buttons
        document.getElementById('step-counter-semantics').addEventListener('change', () => {
            this.updateStepCounterState();
        });
        
        document.getElementById('symbolic-semantics').addEventListener('change', () => {
            this.updateStepCounterState();
        });
        
        // Close modal on outside click
        document.getElementById('settings-modal').addEventListener('click', (e) => {
            if (e.target.id === 'settings-modal') {
                this.closeSettingsModal();
            }
        });

        // Relations filter dropdown
        const relationsWrapper = document.getElementById('relations-dropdown-wrapper');
        const relationsBtn = document.getElementById('relations-dropdown-btn');
        const relationsContent = document.getElementById('relations-dropdown-content');

        relationsBtn.addEventListener('click', (e) => {
            e.stopPropagation();
            const isOpen = relationsWrapper.classList.contains('open');
            if (!isOpen) {
                relationsWrapper.classList.add('open');
                relationsBtn.textContent = 'Relations ▼';
                // Position using fixed coords so it escapes any overflow:hidden parent
                const rect = relationsBtn.getBoundingClientRect();
                // Open upward: position after render so we know the height
                requestAnimationFrame(() => {
                    relationsContent.style.top = (rect.top - relationsContent.offsetHeight - 4) + 'px';
                    relationsContent.style.left = (rect.right - relationsContent.offsetWidth) + 'px';
                });
            } else {
                relationsWrapper.classList.remove('open');
                relationsBtn.textContent = 'Relations ▲';
            }
        });

        document.addEventListener('click', (e) => {
            if (!relationsWrapper.contains(e.target)) {
                relationsWrapper.classList.remove('open');
                relationsBtn.textContent = 'Relations ▲';
            }
        });

        document.getElementById('relations-select-all').addEventListener('click', (e) => {
            e.stopPropagation();
            this.availableRelations.forEach(rel => {
                const cb = document.getElementById('rel-cb-' + rel);
                if (cb) cb.checked = true;
            });
            this.visibleRelations = null;
            this.applyRelationFilter();
        });

        document.getElementById('relations-select-none').addEventListener('click', (e) => {
            e.stopPropagation();
            this.availableRelations.forEach(rel => {
                const cb = document.getElementById('rel-cb-' + rel);
                if (cb) cb.checked = false;
            });
            this.visibleRelations = new Set();
            this.applyRelationFilter();
        });
    }

    updateRelationsDropdown(relations) {
        // relations: array of base type strings
        const container = document.getElementById('relations-checkboxes');
        container.innerHTML = '';

        // Update available set, preserving existing visibility state
        relations.forEach(rel => this.availableRelations.add(rel));

        [...this.availableRelations].sort().forEach(rel => {
            const color = EDGE_COLORS[rel] || EDGE_COLORS.default;
            const isChecked = this.visibleRelations === null || this.visibleRelations.has(rel);

            const item = document.createElement('label');
            item.className = 'relation-checkbox-item';

            const cb = document.createElement('input');
            cb.type = 'checkbox';
            cb.id = 'rel-cb-' + rel;
            cb.checked = isChecked;
            cb.addEventListener('change', (e) => {
                e.stopPropagation();
                if (this.visibleRelations === null) {
                    // Clone all relations into set first
                    this.visibleRelations = new Set(this.availableRelations);
                }
                if (cb.checked) {
                    this.visibleRelations.add(rel);
                } else {
                    this.visibleRelations.delete(rel);
                }
                // If all checked, reset to null (all visible)
                if (this.visibleRelations.size === this.availableRelations.size) {
                    this.visibleRelations = null;
                }
                this.applyRelationFilter();
            });

            const dot = document.createElement('span');
            dot.className = 'relation-color-dot';
            dot.style.background = color;

            const lbl = document.createElement('span');
            lbl.textContent = rel;
            lbl.style.color = '#d4d4d4';
            lbl.style.fontSize = '13px';
            lbl.style.cursor = 'pointer';

            item.appendChild(cb);
            item.appendChild(dot);
            item.appendChild(lbl);
            item.addEventListener('click', (e) => {
                if (e.target !== cb) cb.click();
            });
            container.appendChild(item);
        });
    }

    applyRelationFilter() {
        if (this.visibleRelations === null) {
            // Show all edges
            this.cy.edges().style('display', 'element');
        } else {
            this.cy.edges().forEach(edge => {
                const baseType = edge.data('type').split(' - ')[0];
                edge.style('display', this.visibleRelations.has(baseType) ? 'element' : 'none');
            });
        }
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

            const containerWidth = document.querySelector('.main-content').offsetWidth;
            const newWidth = (e.clientX / containerWidth) * 100;

            if (newWidth > 20 && newWidth < 80) {
                leftPanel.style.flex = `0 0 ${newWidth}%`;
            }
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
        const currentData = this.data[index];
        
        // Render the graph
        const undefined_behaviour =
         currentData && currentData.undefined_behaviour && currentData.undefined_behaviour.length > 0 ?
          currentData.undefined_behaviour[0] :
          null;
        this.renderGraph(currentData.graph, undefined_behaviour);
        
        // Update execution info
        this.updateExecutionInfo(currentData);
        
        // Update carousel UI
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
            indicator.textContent = `Execution ${this.currentIndex} of ${this.executionCount}`;
        }
        
        document.getElementById('carousel-container').classList.add('active');
    }
    
    async visualize(program) {
        this.log('Starting ' + this.currentAction + ' with ' + this.settings.loopSemantics + ' semantics...');

        // Store program for regeneration
        this.lastProgram = program;
        
        // Reset state
        this.graphs = [];
        this.data = [];
        this.currentIndex = 0;
        this.executionCount = 0;
        this.loops = [];
        this.episodicityResults = {};
        this.assertionResults = null;
        this.visibleRelations = null; // reset to show all
        this.availableRelations = new Set();
        document.getElementById('relations-checkboxes').innerHTML = '';

        // Update UI
        document.getElementById('status').textContent = 'Processing...';
        document.getElementById('action-btn').disabled = true;
        document.getElementById('empty-state').style.display = 'none';
        document.getElementById('carousel-container').style.display = 'none';
        document.getElementById('graph-controls').style.display = 'none';
        document.getElementById('graph-stats').style.display = 'none';
        document.getElementById('execution-info').style.display = 'none';

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

        document.getElementById('action-btn').disabled = true;

        this.log('Sending request to backend...');

        // Prepare POST body with settings
        const params = {
            program: program,
            loop_semantics: this.settings.loopSemantics.toString(),
            steps: this.settings.stepCounter.toString(),
            allow_uaf: this.settings.showUAF.toString(),
            allow_unbounded_deref: this.settings.showUnboundedDeref.toString(),
        };

        // Use fetch POST to avoid URL length limits, then read SSE stream manually
        const abortController = new AbortController();

        const handleMessage = (data) => {
            if (data.status === 'interpreting') {
                this.log('Interpreting program...');
            } else if (data.status === 'visualizing') {
                this.log('Generating visualizations...');
            } else if (data.type === 'loop-info') {
                this.log('Received loop information');
                this.loops = data.loops || [];
                this.renderLoops();
            } else if (data.type === 'episodicity-results') {
                this.log('Received episodicity results');
                if (data.loop_episodicity_results) {
                    data.loop_episodicity_results.forEach(result => {
                        this.episodicityResults[result.loop_id] = result;
                    });
                }
                this.renderLoops();
            } else if (data.valid !== undefined || data.instances !== undefined) {
                this.log('Received assertion results');
                this.assertionResults = {
                    valid: data.valid,
                    instances: data.instances || []
                };
                this.renderAssertions();
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
                this.log(this.currentAction.charAt(0).toUpperCase() + this.currentAction.slice(1) + ' complete: ' + this.executionCount + ' executions', 'success');
                this.updateCarouselUI();
                document.getElementById('status').textContent = 'Complete';
                abortController.abort();
                document.getElementById('action-btn').disabled = false;
            } else if (data.error) {
                this.log('Error: ' + data.error, 'error');
                this.showError(data.error);
                abortController.abort();
                document.getElementById('action-btn').disabled = false;
            }
        };

        fetch(this.currentEndpoint, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(params),
            signal: abortController.signal,
        }).then(async (response) => {
            if (!response.ok) {
                throw new Error('Server error: ' + response.status);
            }
            const reader = response.body.getReader();
            const decoder = new TextDecoder();
            let buffer = '';

            while (true) {
                const { done, value } = await reader.read();
                if (done) break;

                buffer += decoder.decode(value, { stream: true });

                // SSE messages are separated by double newlines
                const parts = buffer.split('\n\n');
                buffer = parts.pop(); // keep incomplete trailing chunk

                for (const part of parts) {
                    for (const line of part.split('\n')) {
                        if (line.startsWith('data: ')) {
                            try {
                                const data = JSON.parse(line.slice(6));
                                handleMessage(data);
                            } catch (e) {
                                console.error('Failed to parse SSE message:', e);
                                this.log('Parse error: ' + e.message, 'error');
                            }
                        }
                    }
                }
            }
        }).catch((err) => {
            if (err.name === 'AbortError') return; // clean close, not an error
            this.log('Connection error: ' + err.message, 'error');
            document.getElementById('action-btn').disabled = false;
        });
    }

    renderGraph(graph, undefinedBehaviour = null) {
        try {
            this.log('Rendering graph with ' + graph.nodes.length + ' nodes...');

            if (!graph.nodes || graph.nodes.length === 0) {
                this.log('No nodes in graph data', 'error');
                return;
            }

            this.cy.elements().remove();

            // Add nodes with source span information
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

                // Store source span information in node data
                this.cy.add({
                    data: {
                        id: String(n.id),
                        label: label,
                        isRoot: n.isRoot,
                        source_start_line: n.source_start_line,
                        source_start_col: n.source_start_col,
                        source_end_line: n.source_end_line,
                        source_end_col: n.source_end_col
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

            // Collect relation types from this graph and update filter dropdown
            const relTypes = [...new Set(graph.edges.map(e => e.type.split(' - ')[0]))];
            this.updateRelationsDropdown(relTypes);

          console.log('Graph nodes and edges added. Now processing UAF edges if any.');
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
                this.updateRelationsDropdown(['uaf']);
            } else {
                console.log('No UAF edges to add. undefinedBehaviour:', undefinedBehaviour);
            }

            // Re-apply relation filter to newly rendered graph
            this.applyRelationFilter();

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
