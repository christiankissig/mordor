/**
 * Test Runner for MoRDor Litmus Tests
 * Provides UI overlay for running and viewing test results
 */

class TestRunner {
    constructor() {
        this.tests = [];
        this.results = {};
        this.runningTests = new Set();
        this.currentView = 'overview'; // 'overview' or 'detail'
        this.selectedTest = null;
        
        this.init();
    }

    init() {
        this.createOverlay();
        this.setupEventListeners();
        this.loadTestList();
    }

    createOverlay() {
        const overlay = document.createElement('div');
        overlay.id = 'test-runner-overlay';
        overlay.className = 'test-overlay';
        overlay.innerHTML = `
            <div class="test-modal">
                <div class="test-header">
                    <h2>🧪 Litmus Test Runner</h2>
                    <button class="test-close" id="close-test-runner">&times;</button>
                </div>
                <div class="test-toolbar">
                    <button class="btn-primary" id="run-all-tests">▶ Run All Tests</button>
                    <button class="btn-secondary" id="refresh-tests">🔄 Refresh</button>
                    <button class="btn-secondary" id="clear-results">🗑️ Clear Results</button>
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
        // Close overlay
        document.getElementById('close-test-runner').addEventListener('click', () => {
            this.hide();
        });

        // Close on background click
        document.getElementById('test-runner-overlay').addEventListener('click', (e) => {
            if (e.target.id === 'test-runner-overlay') {
                this.hide();
            }
        });

        // Run all tests
        document.getElementById('run-all-tests').addEventListener('click', () => {
            this.runAllTests();
        });

        // Refresh test list
        document.getElementById('refresh-tests').addEventListener('click', () => {
            this.loadTestList();
        });

        // Clear results
        document.getElementById('clear-results').addEventListener('click', () => {
            this.clearResults();
        });

        // Search/filter tests
        document.getElementById('test-search-input').addEventListener('input', (e) => {
            this.filterTests(e.target.value);
        });

        // Back to overview
        document.getElementById('back-to-overview').addEventListener('click', () => {
            this.showOverview();
        });

        // Run single test
        document.getElementById('run-single-test').addEventListener('click', () => {
            if (this.selectedTest) {
                this.runTest(this.selectedTest);
            }
        });

        // Load test in editor
        document.getElementById('load-test-editor').addEventListener('click', () => {
            if (this.selectedTest) {
                this.loadTestInEditor(this.selectedTest);
            }
        });

        // Copy output button
        document.getElementById('copy-output-btn').addEventListener('click', () => {
            this.copyToClipboard('test-output', 'copy-output-btn');
        });

        // Copy source button
        document.getElementById('copy-source-btn').addEventListener('click', () => {
            this.copyToClipboard('test-source', 'copy-source-btn');
        });
    }

    async loadTestList() {
        const testList = document.getElementById('test-list');
        testList.innerHTML = '<div class="test-loading">Loading tests...</div>';

        try {
            const response = await fetch('/api/tests/list');
            if (!response.ok) throw new Error('Failed to load test list');
            
            const data = await response.json();
            this.tests = data.tests || [];
            
            this.renderTestList();
            this.updateStats();
        } catch (error) {
            console.error('Error loading tests:', error);
            testList.innerHTML = `<div class="test-error">Error loading tests: ${error.message}</div>`;
        }
    }

    renderTestList(filter = '') {
        const testList = document.getElementById('test-list');
        
        if (this.tests.length === 0) {
            testList.innerHTML = '<div class="test-empty">No tests found</div>';
            return;
        }

        const filtered = filter 
            ? this.tests.filter(t => t.toLowerCase().includes(filter.toLowerCase()))
            : this.tests;

        const html = filtered.map(testPath => {
            const result = this.results[testPath];
            const isRunning = this.runningTests.has(testPath);
            const statusClass = result 
                ? (result.success ? 'test-passed' : 'test-failed')
                : isRunning ? 'test-running' : '';
            
            const statusIcon = result
                ? (result.success ? '✓' : '✗')
                : isRunning ? '⟳' : '○';

            return `
                <div class="test-item ${statusClass}" data-test="${testPath}">
                    <div class="test-item-header">
                        <span class="test-status-icon">${statusIcon}</span>
                        <span class="test-name">${this.getTestName(testPath)}</span>
                        <button class="test-run-btn" data-test="${testPath}" title="Run test">▶</button>
                    </div>
                    ${result ? `<div class="test-item-result">${this.formatResultSummary(result)}</div>` : ''}
                </div>
            `;
        }).join('');

        testList.innerHTML = html;

        // Add click handlers
        testList.querySelectorAll('.test-item').forEach(item => {
            item.addEventListener('click', (e) => {
                if (!e.target.classList.contains('test-run-btn')) {
                    this.showTestDetail(item.dataset.test);
                }
            });
        });

        testList.querySelectorAll('.test-run-btn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.stopPropagation();
                this.runTest(btn.dataset.test);
            });
        });
    }

    getTestName(path) {
        return path.replace('litmus-tests/', '');
    }

    formatResultSummary(result) {
        if (!result.parsed) return 'Parse error';
        
        const parts = [];
        if (result.valid !== undefined) {
            parts.push(`Valid: ${result.valid ? 'Yes' : 'No'}`);
        }
        if (result.executions !== undefined) {
            parts.push(`Execs: ${result.executions}`);
        }
        if (result.undefined_behaviour) {
            parts.push('⚠ UB');
        }
        
        return parts.join(' | ');
    }

    filterTests(filter) {
        this.renderTestList(filter);
    }

    async runAllTests() {
        const runBtn = document.getElementById('run-all-tests');
        runBtn.disabled = true;
        runBtn.textContent = '⟳ Running...';

        for (const test of this.tests) {
            await this.runTest(test, false);
        }

        runBtn.disabled = false;
        runBtn.textContent = '▶ Run All Tests';
        this.showOverview();
    }

    async runTest(testPath, showDetail = true) {
        this.runningTests.add(testPath);
        this.updateStats();
        this.renderTestList();

        try {
            const response = await fetch('/api/tests/run', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ test: testPath })
            });

            if (!response.ok) throw new Error('Test execution failed');

            const result = await response.json();
            this.results[testPath] = result;
            
            this.runningTests.delete(testPath);
            this.updateStats();
            this.renderTestList();

            if (showDetail) {
                this.showTestDetail(testPath);
            }
        } catch (error) {
            console.error('Error running test:', error);
            this.results[testPath] = {
                success: false,
                error: error.message,
                output: error.message
            };
            
            this.runningTests.delete(testPath);
            this.updateStats();
            this.renderTestList();
        }
    }

    async showTestDetail(testPath) {
        this.selectedTest = testPath;
        this.currentView = 'detail';

        document.getElementById('test-overview').classList.remove('active');
        document.getElementById('test-detail').classList.add('active');

        document.getElementById('detail-test-name').textContent = this.getTestName(testPath);

        // Load test output if available
        const result = this.results[testPath];
        const outputEl = document.getElementById('test-output');
        
        if (result) {
            outputEl.textContent = result.output || 'No output';
            outputEl.className = result.success ? 'test-output success' : 'test-output error';
        } else {
            outputEl.textContent = 'Test not run yet. Click "Run Test" to execute.';
            outputEl.className = 'test-output';
        }

        // Load test source
        try {
            const response = await fetch(`/api/tests/source?test=${encodeURIComponent(testPath)}`);
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

    showOverview() {
        this.currentView = 'overview';
        this.selectedTest = null;

        document.getElementById('test-detail').classList.remove('active');
        document.getElementById('test-overview').classList.add('active');

        // Update overview with summary
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
                    <p>You have ${totalTests} test(s) available.</p>
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
    }

    renderResultsList() {
        const results = Object.entries(this.results)
            .sort(([, a], [, b]) => {
                if (a.success === b.success) return 0;
                return a.success ? 1 : -1;
            });

        return results.map(([test, result]) => `
            <div class="result-item ${result.success ? 'success' : 'failed'}" data-test="${test}">
                <span class="result-icon">${result.success ? '✓' : '✗'}</span>
                <span class="result-name">${this.getTestName(test)}</span>
                <span class="result-summary">${this.formatResultSummary(result)}</span>
            </div>
        `).join('');
    }

    updateStats() {
        const passed = Object.values(this.results).filter(r => r.success).length;
        const failed = Object.values(this.results).filter(r => !r.success).length;
        const running = this.runningTests.size;

        document.getElementById('test-count').textContent = `${this.tests.length} tests`;
        document.getElementById('test-passed').textContent = `${passed} passed`;
        document.getElementById('test-failed').textContent = `${failed} failed`;
        document.getElementById('test-running').textContent = `${running} running`;
    }

    clearResults() {
        if (!confirm('Clear all test results?')) return;
        
        this.results = {};
        this.runningTests.clear();
        this.updateStats();
        this.renderTestList();
        this.showOverview();
    }

    async loadTestInEditor(testPath) {
        try {
            const response = await fetch(`/api/tests/source?test=${encodeURIComponent(testPath)}`);
            if (!response.ok) throw new Error('Failed to load test source');
            
            const data = await response.json();
            
            // Load into editor (assuming there's a global editor or function)
            const editor = document.getElementById('litmus-input');
            if (editor) {
                editor.value = data.source;
                // Trigger any syntax highlighting update
                const event = new Event('input', { bubbles: true });
                editor.dispatchEvent(event);
            }

            // Close overlay
            this.hide();
            
            // Show success message
            const status = document.getElementById('status');
            if (status) {
                status.textContent = `Loaded: ${this.getTestName(testPath)}`;
                status.className = 'status success';
                setTimeout(() => {
                    status.className = 'status';
                }, 3000);
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
            const text = element.textContent;
            await navigator.clipboard.writeText(text);
            
            // Visual feedback
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

// Export for use in main application
window.TestRunner = TestRunner;
