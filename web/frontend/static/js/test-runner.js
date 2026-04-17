/**
 * Test Runner for MoRDor Litmus Tests + Episodicity Tests
 * Provides UI overlay for running and viewing test results
 */

class TestRunner {
    constructor() {
        this.litmusTests = [];
        this.episodicityTests = [];
        this.programTests = [];
        this.results = {};
        this.runningTests = new Set();
        this.currentView = 'overview'; // 'overview' or 'detail'
        this.selectedTest = null;
        this.selectedTestType = null; // 'litmus' or 'episodicity' or 'program'

        this.init();
    }

    get tests() {
        return [...this.litmusTests, ...this.episodicityTests, ...this.programTests];
    }

    init() {
        this.createOverlay();
        this.setupEventListeners();
        this.loadTestLists();
    }

    createOverlay() {
        const overlay = document.createElement('div');
        overlay.id = 'test-runner-overlay';
        overlay.className = 'test-overlay';
        overlay.innerHTML = `
            <div class="test-modal">
                <div class="test-header">
                    <h2>🧪 Test Runner</h2>
                    <button class="test-close" id="close-test-runner">&times;</button>
                </div>
                <div class="test-toolbar">
                    <button class="btn-primary" id="run-all-tests">▶ Run All Tests</button>
                    <button class="btn-secondary" id="refresh-tests">🔄 Refresh</button>
                    <button class="btn-secondary" id="clear-results">🗑️ Clear Results</button>
                    <button class="btn-secondary" id="view-summary" style="display: none;">📊 View Summary</button>
                    <div class="test-stats">
                        <span id="test-count">0 tests</span>
                        <span id="test-passed" class="stat-passed">0 passed</span>
                        <span id="test-failed" class="stat-failed">0 failed</span>
                        <span id="test-running" class="stat-running">0 running</span>
                    </div>
                </div>
                <div class="test-content">
                    <div class="test-sidebar">
                        <div class="test-search">
                            <input type="text" id="test-search-input" placeholder="Filter tests..." />
                        </div>
                        <div class="test-list" id="test-list">
                            <div class="test-loading">Loading tests...</div>
                        </div>
                    </div>
                    <div class="test-main">
                        <div id="test-overview" class="test-view active">
                            <div class="test-welcome">
                                <h3>Welcome to Test Runner</h3>
                                <p>Select a test from the list to view details or run all tests.</p>
                            </div>
                        </div>
                        <div id="test-detail" class="test-view">
                            <div class="test-detail-header">
                                <button class="btn-back" id="back-to-overview">← Back</button>
                                <h3 id="detail-test-name"></h3>
                                <div class="test-detail-actions">
                                    <button class="btn-primary" id="run-single-test">▶ Run Test</button>
                                    <button class="btn-secondary" id="load-test-editor">📝 Load in Editor</button>
                                </div>
                            </div>
                            <div class="test-detail-content">
                                <div class="test-output-section">
                                    <h4>
                                        <span>Test Output</span>
                                        <button class="btn-copy" id="copy-output-btn" title="Copy output">📋 Copy</button>
                                    </h4>
                                    <pre id="test-output" class="test-output"></pre>
                                </div>
                                <div class="test-source-section">
                                    <h4>
                                        <span>Source Code</span>
                                        <button class="btn-copy" id="copy-source-btn" title="Copy source">📋 Copy</button>
                                    </h4>
                                    <pre id="test-source" class="test-source"></pre>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        `;

        document.body.appendChild(overlay);
    }

    setupEventListeners() {
        document.getElementById('close-test-runner').addEventListener('click', () => this.hide());

        document.getElementById('test-runner-overlay').addEventListener('click', (e) => {
            if (e.target.id === 'test-runner-overlay') this.hide();
        });

        document.getElementById('run-all-tests').addEventListener('click', () => this.runAllTests());
        document.getElementById('refresh-tests').addEventListener('click', () => this.loadTestLists());
        document.getElementById('clear-results').addEventListener('click', () => this.clearResults());
        document.getElementById('view-summary').addEventListener('click', () => this.showOverview());
        document.getElementById('test-search-input').addEventListener('input', (e) => this.filterTests(e.target.value));
        document.getElementById('back-to-overview').addEventListener('click', () => this.showOverview());

        document.getElementById('run-single-test').addEventListener('click', () => {
            if (this.selectedTest) this.runTest(this.selectedTest, this.selectedTestType);
        });

        document.getElementById('load-test-editor').addEventListener('click', () => {
            if (this.selectedTest) this.loadTestInEditor(this.selectedTest, this.selectedTestType);
        });

        document.getElementById('copy-output-btn').addEventListener('click', () => {
            this.copyToClipboard('test-output', 'copy-output-btn');
        });

        document.getElementById('copy-source-btn').addEventListener('click', () => {
            this.copyToClipboard('test-source', 'copy-source-btn');
        });
    }

    async loadTestLists() {
        const testList = document.getElementById('test-list');
        testList.innerHTML = '<div class="test-loading">Loading tests...</div>';

        try {
            const [litmusResp, episodicityResp, programResp] = await Promise.all([
                fetch('/api/tests/list'),
                fetch('/api/episodicity/list'),
                fetch('/api/program/list')
            ]);

            if (!litmusResp.ok) throw new Error('Failed to load litmus test list');
            if (!episodicityResp.ok) throw new Error('Failed to load episodicity test list');
            if (!programResp.ok) throw new Error('Failed to load program list');

            const litmusData = await litmusResp.json();
            const episodicityData = await episodicityResp.json();
            const programData = await programResp.json();

            this.litmusTests = litmusData.tests || [];
            this.episodicityTests = episodicityData.tests || [];
            this.programTests = programData.programs || [];

            this.renderTestList();
            this.updateStats();
        } catch (error) {
            console.error('Error loading tests:', error);
            testList.innerHTML = `<div class="test-error">Error loading tests: ${error.message}</div>`;
        }
    }

    buildTestTree(tests, stripPrefix) {
        const root = {};
        for (const testPath of tests) {
            const escapedPrefix = stripPrefix
                ? stripPrefix.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
                : null;
            const displayPath = (stripPrefix && escapedPrefix)
                ? testPath.replace(new RegExp('^' + escapedPrefix + '/?'), '')
                : testPath;
            const parts = displayPath.split('/');
            let node = root;
            for (let i = 0; i < parts.length - 1; i++) {
                const dir = parts[i];
                if (!node[dir]) node[dir] = { __children: {} };
                node = node[dir].__children;
            }
            const fileName = parts[parts.length - 1];
            node[fileName] = { __testPath: testPath };
        }
        return root;
    }

    renderTestTree(node, depth, testType) {
        return Object.entries(node)
            .sort(([aKey, aVal], [bKey, bVal]) => {
                const aIsDir = !aVal.__testPath;
                const bIsDir = !bVal.__testPath;
                if (aIsDir !== bIsDir) return aIsDir ? -1 : 1;
                return aKey.localeCompare(bKey);
            })
            .map(([key, val]) => {
                if (val.__testPath) {
                    const testPath = val.__testPath;
                    const resultKey = this._resultKey(testPath, testType);
                    const result = this.results[resultKey];
                    const isRunning = this.runningTests.has(resultKey);
                    const statusClass = result
                        ? (result.success ? 'test-passed' : 'test-failed')
                        : isRunning ? 'test-running' : '';
                    const statusIcon = result
                        ? (result.success ? '✓' : '✗')
                        : isRunning ? '⟳' : '○';
                    return `
                        <div class="test-item ${statusClass}" data-test="${testPath}" data-test-type="${testType}" style="padding-left: ${depth * 14 + 8}px">
                            <div class="test-item-header">
                                <span class="test-status-icon">${statusIcon}</span>
                                <span class="test-name">${key}</span>
                                <button class="test-run-btn" data-test="${testPath}" data-test-type="${testType}" title="Run test">▶</button>
                            </div>
                            ${result ? `<div class="test-item-result">${this.formatResultSummary(result, testType)}</div>` : ''}
                        </div>
                    `;
                } else {
                    const allPaths = this.collectPaths(val.__children);
                    const anyRunning = allPaths.some(p => this.runningTests.has(this._resultKey(p, testType)));
                    const results = allPaths.map(p => this.results[this._resultKey(p, testType)]).filter(Boolean);
                    const dirStatusClass = anyRunning
                        ? 'test-running'
                        : results.length === 0 ? ''
                        : results.every(r => r.success) ? 'test-passed' : 'test-failed';
                    const dirIcon = anyRunning ? '⟳'
                        : results.length === 0 ? '📁'
                        : results.every(r => r.success) ? '✓' : '✗';
                    const nodeId = `tree-node-${testType}-${depth}-${key.replace(/\W/g, '_')}`;
                    const childrenHtml = this.renderTestTree(val.__children, depth + 1, testType);
                    return `
                        <div class="test-tree-dir">
                            <div class="test-dir-header ${dirStatusClass}" style="padding-left: ${depth * 14 + 8}px" data-toggle="${nodeId}">
                                <span class="test-dir-toggle">▾</span>
                                <span class="test-dir-icon">${dirIcon}</span>
                                <span class="test-dir-name">${key}</span>
                                <span class="test-dir-count">${allPaths.length}</span>
                            </div>
                            <div class="test-dir-children" id="${nodeId}">
                                ${childrenHtml}
                            </div>
                        </div>
                    `;
                }
            }).join('');
    }

    collectPaths(node) {
        const paths = [];
        for (const [, val] of Object.entries(node)) {
            if (val.__testPath) {
                paths.push(val.__testPath);
            } else if (val.__children) {
                paths.push(...this.collectPaths(val.__children));
            }
        }
        return paths;
    }

    _resultKey(testPath, testType) {
        return `${testType}::${testPath}`;
    }

    renderTestList(filter = '') {
        const testList = document.getElementById('test-list');

        if (this.litmusTests.length === 0 && this.episodicityTests.length === 0 && this.programTests.length === 0) {
            testList.innerHTML = '<div class="test-empty">No tests found</div>';
            return;
        }

        // Save which nodes are currently collapsed so we can restore after re-render
        const collapsedIds = new Set();
        testList.querySelectorAll('.test-dir-children').forEach(el => {
            if (el.style.display === 'none') collapsedIds.add(el.id);
        });

        const filteredLitmus = filter
            ? this.litmusTests.filter(t => t.toLowerCase().includes(filter.toLowerCase()))
            : this.litmusTests;

        const filteredEpisodicity = filter
            ? this.episodicityTests.filter(t => t.toLowerCase().includes(filter.toLowerCase()))
            : this.episodicityTests;

        const filteredProgram = filter
            ? this.programTests.filter(t => t.toLowerCase().includes(filter.toLowerCase()))
            : this.programTests;

        const litmusTree = this.buildTestTree(filteredLitmus, 'litmus-tests');
        const episodicityTree = this.buildTestTree(filteredEpisodicity, 'programs/episodicity');
        const programTree = this.buildTestTree(filteredProgram, 'programs');

        const litmusId = 'top-level-litmus';
        const episodicityId = 'top-level-episodicity';
        const programId = 'top-level-program';

        testList.innerHTML = `
            <div class="test-tree-dir">
                <div class="test-dir-header test-top-level" style="padding-left: 8px" data-toggle="${litmusId}">
                    <span class="test-dir-toggle">▾</span>
                    <span class="test-dir-icon">📋</span>
                    <span class="test-dir-name">Litmus Tests</span>
                    <span class="test-dir-count">${filteredLitmus.length}</span>
                </div>
                <div class="test-dir-children" id="${litmusId}">
                    ${this.renderTestTree(litmusTree, 1, 'litmus')}
                </div>
            </div>
            <div class="test-tree-dir">
                <div class="test-dir-header test-top-level" style="padding-left: 8px" data-toggle="${episodicityId}">
                    <span class="test-dir-toggle">▾</span>
                    <span class="test-dir-icon">🔁</span>
                    <span class="test-dir-name">Episodicity Tests</span>
                    <span class="test-dir-count">${filteredEpisodicity.length}</span>
                </div>
                <div class="test-dir-children" id="${episodicityId}">
                    ${this.renderTestTree(episodicityTree, 1, 'episodicity')}
                </div>
            </div>
            <div class="test-tree-dir">
                <div class="test-dir-header test-top-level" style="padding-left: 8px" data-toggle="${programId}">
                    <span class="test-dir-toggle">▾</span>
                    <span class="test-dir-icon">📋</span>
                    <span class="test-dir-name">Programs</span>
                    <span class="test-dir-count">${filteredProgram.length}</span>
                </div>
                <div class="test-dir-children" id="${programId}">
                    ${this.renderTestTree(programTree, 1, 'programs')}
                </div>
            </div>
        `;

        // Restore collapsed state from before the re-render
        collapsedIds.forEach(id => {
            const el = document.getElementById(id);
            if (el) {
                el.style.display = 'none';
                const header = testList.querySelector(`[data-toggle="${id}"]`);
                const toggle = header?.querySelector('.test-dir-toggle');
                if (toggle) toggle.textContent = '▸';
            }
        });

        // Collapse/expand directory nodes
        testList.querySelectorAll('.test-dir-header').forEach(header => {
            header.addEventListener('click', (e) => {
                if (e.target.classList.contains('test-run-btn')) return;
                const targetId = header.dataset.toggle;
                const childrenEl = document.getElementById(targetId);
                const toggle = header.querySelector('.test-dir-toggle');
                if (childrenEl) {
                    const collapsed = childrenEl.style.display === 'none';
                    childrenEl.style.display = collapsed ? '' : 'none';
                    if (toggle) toggle.textContent = collapsed ? '▾' : '▸';
                }
            });
        });

        // Click on test item to show detail
        testList.querySelectorAll('.test-item').forEach(item => {
            item.addEventListener('click', (e) => {
                if (!e.target.classList.contains('test-run-btn')) {
                    this.showTestDetail(item.dataset.test, item.dataset.testType);
                }
            });
        });

        // Run button on individual test
        testList.querySelectorAll('.test-run-btn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.stopPropagation();
                this.runTest(btn.dataset.test, btn.dataset.testType);
            });
        });
    }

    getTestName(path) {
        return path.split('/').pop();
    }

    formatResultSummary(result, testType) {
        if (testType === 'episodicity') {
            if (!result.success) return 'Error';
            if (result.loops_analyzed !== undefined) {
                return `Loops: ${result.loops_analyzed} | ${result.all_episodic ? '✓ All episodic' : '✗ Non-episodic'}`;
            }
            return result.success ? 'OK' : 'Failed';
        }
        // Litmus
        if (!result.parsed) return 'Parse error';
        const parts = [];
        if (result.valid !== undefined) parts.push(`Valid: ${result.valid ? 'Yes' : 'No'}`);
        if (result.executions !== undefined) parts.push(`Execs: ${result.executions}`);
        if (result.undefined_behaviour) parts.push('⚠ UB');
        return parts.join(' | ');
    }

    filterTests(filter) {
        this.renderTestList(filter);
    }

    async runAllTests() {
        const runBtn = document.getElementById('run-all-tests');
        runBtn.disabled = true;
        runBtn.textContent = '⟳ Running...';

        for (const test of this.litmusTests) {
            await this.runTest(test, 'litmus', false);
        }
        for (const test of this.episodicityTests) {
            await this.runTest(test, 'episodicity', false);
        }

        runBtn.disabled = false;
        runBtn.textContent = '▶ Run All Tests';
        this.showOverview();
    }

    async runTest(testPath, testType, showDetail = true) {
        const resultKey = this._resultKey(testPath, testType);
        this.runningTests.add(resultKey);
        this.updateStats();
        this.renderTestList();

        try {
            const result = testType === 'episodicity'
                ? await this._runEpisodicity(testPath)
                : await this._runLitmus(testPath);

            this.results[resultKey] = result;
            this.runningTests.delete(resultKey);
            this.updateStats();
            this.renderTestList();

            if (showDetail) {
                this.showTestDetail(testPath, testType);
            }
        } catch (error) {
            console.error('Error running test:', error);
            this.results[resultKey] = {
                success: false,
                error: error.message,
                output: error.message
            };
            this.runningTests.delete(resultKey);
            this.updateStats();
            this.renderTestList();
        }
    }

    async _runLitmus(testPath) {
        const response = await fetch('/api/tests/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ test: testPath })
        });
        if (!response.ok) throw new Error('Test execution failed');
        return await response.json();
    }

    async _runEpisodicity(testPath) {
        const response = await fetch('/api/episodicity/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ test: testPath })
        });
        if (!response.ok) throw new Error('Episodicity execution failed');
        return await response.json();
    }

    // Sync the main action button when an episodicity test is selected
    _syncActionButton(testType) {
        const actionBtn = document.getElementById('action-btn');
        if (!actionBtn) return;

        if (testType === 'episodicity') {
            actionBtn.textContent = 'Episodicity';
            actionBtn.dataset.action = 'episodicity';
            actionBtn.dataset.endpoint = '/api/episodicity/stream';
            if (window._graphVisualizer) {
                window._graphVisualizer.currentEndpoint = '/api/episodicity/stream';
                window._graphVisualizer.currentAction = 'episodicity';
            }
        } else if (testType === 'litmus') {
            actionBtn.textContent = 'Assertions';
            actionBtn.dataset.action = 'assertions';
            actionBtn.dataset.endpoint = '/api/assertions/stream';
            if (window._graphVisualizer) {
                window._graphVisualizer.currentEndpoint = '/api/assertions/stream';
                window._graphVisualizer.currentAction = 'assertions';
            }
        }
    }

    async showTestDetail(testPath, testType) {
        this.selectedTest = testPath;
        this.selectedTestType = testType;
        this.currentView = 'detail';

        // Update main action button
        this._syncActionButton(testType);

        document.getElementById('test-overview').classList.remove('active');
        document.getElementById('test-detail').classList.add('active');
        document.getElementById('detail-test-name').textContent = this.getTestName(testPath);

        const resultKey = this._resultKey(testPath, testType);
        const result = this.results[resultKey];
        const outputEl = document.getElementById('test-output');

        if (result) {
            outputEl.textContent = this._formatOutput(result, testType);
            outputEl.className = result.success ? 'test-output success' : 'test-output error';
        } else {
            outputEl.textContent = 'Test not run yet. Click "Run Test" to execute.';
            outputEl.className = 'test-output';
        }

        // Load test source from the correct endpoint
        const sourceEndpoint = testType === 'episodicity'
            ? `/api/episodicity/source?test=${encodeURIComponent(testPath)}`
            : `/api/tests/source?test=${encodeURIComponent(testPath)}`;

        try {
            const response = await fetch(sourceEndpoint);
            if (response.ok) {
                const data = await response.json();
                document.getElementById('test-source').textContent = data.source;
            } else {
                document.getElementById('test-source').textContent = 'Failed to load source';
            }
        } catch (error) {
            document.getElementById('test-source').textContent = `Error: ${error.message}`;
        }
    }

    _formatOutput(result, testType) {
        if (testType !== 'episodicity' || !result.results) {
            return result.output || 'No output';
        }

        // Pretty-print structured episodicity results
        const lines = [];
        lines.push(`Exit code: ${result.exit_code}`);
        lines.push(`Loops analysed: ${result.loops_analyzed}`);
        lines.push(`All episodic: ${result.all_episodic ? 'Yes' : 'No'}`);
        lines.push('');

        result.results.forEach(loop => {
            lines.push(`Loop ${loop.loop_id}: ${loop.is_episodic ? '✓ Episodic' : '✗ Non-episodic'}`);
            loop.conditions.forEach(c => {
                const icon = c.satisfied ? '  ✓' : '  ✗';
                const detail = c.satisfied
                    ? 'satisfied'
                    : `violated (${c.violation_count} violation${c.violation_count !== 1 ? 's' : ''})`;
                lines.push(`${icon} Condition ${c.condition_num}: ${detail}`);
            });
            lines.push('');
        });

        if (result.output) {
            lines.push('--- Raw output ---');
            lines.push(result.output);
        }

        return lines.join('\n');
    }

    showOverview() {
        this.currentView = 'overview';
        this.selectedTest = null;
        this.selectedTestType = null;

        document.getElementById('test-detail').classList.remove('active');
        document.getElementById('test-overview').classList.add('active');

        this.renderOverview();
    }

    renderOverview() {
        const overview = document.getElementById('test-overview');
        const totalTests = this.tests.length;
        const resultsCount = Object.keys(this.results).length;

        if (resultsCount === 0) {
            overview.innerHTML = `
                <div class="test-welcome">
                    <h3>Welcome to Test Runner</h3>
                    <p>You have ${this.litmusTests.length} litmus test(s) and ${this.episodicityTests.length} episodicity test(s) available.</p>
                    <p>Click "Run All Tests" or select individual tests to run.</p>
                </div>
            `;
            return;
        }

        const passed = Object.values(this.results).filter(r => r.success).length;
        const failed = Object.values(this.results).filter(r => !r.success).length;

        overview.innerHTML = `
            <div class="test-summary">
                <h3>Test Results Summary</h3>
                <div class="summary-stats">
                    <div class="summary-stat">
                        <div class="stat-value">${totalTests}</div>
                        <div class="stat-label">Total Tests</div>
                    </div>
                    <div class="summary-stat success">
                        <div class="stat-value">${passed}</div>
                        <div class="stat-label">Passed</div>
                    </div>
                    <div class="summary-stat failed">
                        <div class="stat-value">${failed}</div>
                        <div class="stat-label">Failed</div>
                    </div>
                    <div class="summary-stat">
                        <div class="stat-value">${resultsCount}</div>
                        <div class="stat-label">Run</div>
                    </div>
                </div>
                <div class="test-results-list">
                    ${this.renderResultsList()}
                </div>
            </div>
        `;

        overview.querySelectorAll('.result-item').forEach(item => {
            item.addEventListener('click', () => {
                const testPath = item.getAttribute('data-test');
                const testType = item.getAttribute('data-test-type');
                if (testPath && testType) this.showTestDetail(testPath, testType);
            });
        });
    }

    renderResultsList() {
        return Object.entries(this.results)
            .sort(([, a], [, b]) => {
                if (a.success === b.success) return 0;
                return a.success ? 1 : -1;
            })
            .map(([key, result]) => {
                const sepIdx = key.indexOf('::');
                const testType = key.substring(0, sepIdx);
                const testPath = key.substring(sepIdx + 2);
                const badge = testType === 'episodicity'
                    ? '<span style="font-size:0.75rem;color:#9cdcfe;margin-left:4px;">[episodicity]</span>'
                    : '<span style="font-size:0.75rem;color:#4ec9b0;margin-left:4px;">[litmus]</span>';
                return `
                    <div class="result-item ${result.success ? 'success' : 'failed'}" data-test="${testPath}" data-test-type="${testType}" style="cursor: pointer;">
                        <span class="result-icon">${result.success ? '✓' : '✗'}</span>
                        <span class="result-name">${this.getTestName(testPath)}${badge}</span>
                        <span class="result-summary">${this.formatResultSummary(result, testType)}</span>
                    </div>
                `;
            }).join('');
    }

    updateStats() {
        const passed = Object.values(this.results).filter(r => r.success).length;
        const failed = Object.values(this.results).filter(r => !r.success).length;
        const running = this.runningTests.size;

        document.getElementById('test-count').textContent = `${this.tests.length} tests`;
        document.getElementById('test-passed').textContent = `${passed} passed`;
        document.getElementById('test-failed').textContent = `${failed} failed`;
        document.getElementById('test-running').textContent = `${running} running`;

        const viewSummaryBtn = document.getElementById('view-summary');
        viewSummaryBtn.style.display = Object.keys(this.results).length > 0 ? 'inline-block' : 'none';
    }

    clearResults() {
        if (!confirm('Clear all test results?')) return;
        this.results = {};
        this.runningTests.clear();
        this.updateStats();
        this.renderTestList();
        this.showOverview();
    }

    async loadTestInEditor(testPath, testType) {
        const sourceEndpoint = testType === 'episodicity'
            ? `/api/episodicity/source?test=${encodeURIComponent(testPath)}`
            : `/api/tests/source?test=${encodeURIComponent(testPath)}`;

        try {
            const response = await fetch(sourceEndpoint);
            if (!response.ok) throw new Error('Failed to load test source');

            const data = await response.json();
            const editor = document.getElementById('litmus-input');
            if (editor) {
                editor.value = data.source;
                editor.dispatchEvent(new Event('input', { bubbles: true }));
            }

            // Sync the action button
            this._syncActionButton(testType);

            this.hide();

            const status = document.getElementById('status');
            if (status) {
                status.textContent = `Loaded: ${this.getTestName(testPath)}`;
                status.className = 'status success';
                setTimeout(() => { status.className = 'status'; }, 3000);
            }
        } catch (error) {
            alert(`Failed to load test: ${error.message}`);
        }
    }

    async copyToClipboard(elementId, buttonId) {
        const element = document.getElementById(elementId);
        const button = document.getElementById(buttonId);
        if (!element || !button) return;

        try {
            await navigator.clipboard.writeText(element.textContent);
            button.classList.add('copied');
            const originalText = button.textContent;
            button.textContent = 'Copied!';
            setTimeout(() => {
                button.classList.remove('copied');
                button.textContent = originalText;
            }, 2000);
        } catch (error) {
            console.error('Failed to copy:', error);
            alert('Failed to copy to clipboard');
        }
    }

    show() {
        document.getElementById('test-runner-overlay').classList.add('active');
    }

    hide() {
        document.getElementById('test-runner-overlay').classList.remove('active');
    }

    toggle() {
        const overlay = document.getElementById('test-runner-overlay');
        if (overlay.classList.contains('active')) {
            this.hide();
        } else {
            this.show();
        }
    }
}

window.TestRunner = TestRunner;
