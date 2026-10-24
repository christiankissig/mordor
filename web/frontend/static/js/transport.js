// How the frontend reaches MoRDor (W5, #181): the web server (mordor-web), or
// the browser build's Web Worker (wasm/README.md) when the page is served as
// static files. window.MORDOR_CONFIG (config.js) chooses:
//
//   { transport: 'server' }
//   { transport: 'worker', worker: 'mordor/worker_boot.js', data: 'data/' }
//
// MordorTransport.stream(endpoint, params, onMessage, signal) runs a pipeline:
// endpoint is the server's /api/<pipeline>/stream, params its JSON body, and
// onMessage gets each message the server would send over SSE, parsed. It
// resolves when the answer is complete. Aborting signal cancels the run: the
// server's connection is closed, or the worker terminated and a new one
// started.
//
// MordorTransport.getJSON(url) answers the server's GET endpoints the
// frontend uses: from the server, or from the static build's data files.
//
// MordorTransport.runTest(kind, path) is the test runner's run of a file
// (kind 'litmus' or 'episodicity'), as /api/tests/run and /api/episodicity/run
// answer it; the worker builds that answer from a pipeline's messages.
(function () {
  const config = window.MORDOR_CONFIG || { transport: 'server' };

  // The SSE frames of a streamed response, parsed, to onMessage.
  async function readSSE(response, onMessage) {
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
          if (line.startsWith('data: ')) onMessage(JSON.parse(line.slice(6)));
        }
      }
    }
  }

  const server = {
    mode: 'server',
    async stream(endpoint, params, onMessage, signal) {
      const response = await fetch(endpoint, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(params),
        signal,
      });
      if (!response.ok) throw new Error('Server error: ' + response.status);
      await readSSE(response, onMessage);
    },
    async getJSON(url) {
      const response = await fetch(url);
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    },
    async runTest(kind, path) {
      const response = await fetch(
        kind === 'episodicity' ? '/api/episodicity/run' : '/api/tests/run', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ test: path }),
        });
      if (!response.ok) throw new Error('Test execution failed');
      return response.json();
    },
  };

  // One worker answers one request at a time, in order; the rest wait their
  // turn. Cancelling terminates the worker, which fails what it was running
  // and everything waiting, and starts a fresh one (loading Z3 again).
  function workerTransport() {
    let worker = null;
    let current = null; // { onMessage, resolve, reject }
    const queue = [];

    function start() {
      worker = new Worker(config.worker);
      worker.onmessage = (event) => {
        if (!current) return;
        if (event.data === null) {
          const done = current;
          current = null;
          done.resolve();
          next();
          return;
        }
        try {
          const message = JSON.parse(event.data);
          if (message.type === 'complete' || message.type === 'error') current.ended = true;
          current.onMessage(message);
        } catch (e) {
          console.error('Failed to handle a message from the worker:', e);
        }
      };
      worker.onerror = (event) => {
        restart(new Error('The worker failed: ' + (event.message || 'unknown error')));
      };
    }

    function next() {
      if (current || queue.length === 0) return;
      current = queue.shift();
      worker.postMessage(current.request);
    }

    function restart(error) {
      worker.terminate();
      const failed = (current ? [current] : []).concat(queue.splice(0));
      current = null;
      start();
      failed.forEach((job) => job.reject(error));
    }

    function stream(endpoint, params, onMessage, signal) {
      const pipeline = endpoint.replace(/^.*\/api\/([^/]+)\/stream$/, '$1');
      return new Promise((resolve, reject) => {
        const job = {
          request: JSON.stringify({ ...params, pipeline }),
          onMessage,
          resolve,
          reject,
        };
        if (signal) {
          if (signal.aborted) {
            reject(new DOMException('Aborted', 'AbortError'));
            return;
          }
          signal.addEventListener('abort', () => {
            const waiting = queue.indexOf(job);
            if (waiting >= 0) queue.splice(waiting, 1);
            const abort = new DOMException('Aborted', 'AbortError');
            // The frontend aborts on a run's last message, complete or error,
            // to close the server's connection; the worker has nothing to
            // close then, and is not restarted.
            if (current === job && !job.ended) restart(abort);
            else if (waiting >= 0) reject(abort);
          });
        }
        queue.push(job);
        next();
      });
    }

    let data = null;
    function staticData() {
      if (!data) {
        const base = config.data || 'data/';
        data = Promise.all([
          fetch(base + 'examples.json').then((r) => r.json()),
          fetch(base + 'tests.json').then((r) => r.json()),
        ]).then(([examples, tests]) => ({ examples, tests }));
      }
      return data;
    }

    async function getJSON(url) {
      const { examples, tests } = await staticData();
      const path = url.split('?')[0];
      const test = new URLSearchParams(url.split('?')[1] || '').get('test');
      switch (path) {
        case '/api/examples': return examples;
        case '/api/tests/list': return { tests: tests.tests };
        case '/api/episodicity/list': return { tests: tests.episodicity };
        case '/api/program/list': return { programs: tests.programs };
        case '/api/tests/source':
        case '/api/episodicity/source':
          if (!(test in tests.sources)) throw new Error('No such test: ' + test);
          return { source: tests.sources[test] };
        default: throw new Error('Not in the static build: ' + url);
      }
    }

    // The test runner's result, from the messages of the pipeline the server
    // would run for it: what the CLI would print, summarised.
    async function runTest(kind, path) {
      const { source } = await getJSON('/api/tests/source?test=' + encodeURIComponent(path));
      const messages = [];
      const pipeline = kind === 'episodicity' ? 'episodicity' : 'assertions';
      await stream(`/api/${pipeline}/stream`, { program: source }, (m) => messages.push(m));
      const error = messages.find((m) => m.type === 'error');
      const lines = messages
        .filter((m) => m.type === 'error' || 'valid' in m || m.type === 'complete')
        .map((m) => JSON.stringify(m));
      if (kind === 'episodicity') {
        const found = messages.find((m) => m.type === 'episodicity-results');
        const results = ((found && found.loop_episodicity_results) || []).map((loop) => {
          const conditions = Object.keys(loop)
            .filter((k) => /^condition\d+$/.test(k))
            .map((k) => ({
              condition_num: Number(k.slice('condition'.length)),
              satisfied: loop[k].satisfied,
              violation_count: (loop[k].violations || []).length,
            }));
          return {
            loop_id: loop.loop_id,
            is_episodic: conditions.every((c) => c.satisfied),
            conditions,
          };
        });
        return {
          success: !error && results.length > 0,
          exit_code: error ? 1 : 0,
          output: error ? error.message : lines.join('\n'),
          loops_analyzed: results.length,
          all_episodic: results.length > 0 && results.every((r) => r.is_episodic),
          results,
        };
      }
      const verdict = messages.find((m) => 'valid' in m);
      const complete = messages.find((m) => m.type === 'complete');
      return {
        success: !error && !(verdict && verdict.valid === false),
        exit_code: error ? 1 : 0,
        output: error ? error.message : lines.join('\n'),
        parsed: !error,
        valid: verdict ? verdict.valid : null,
        undefined_behaviour: null,
        executions: complete ? complete.total_executions : null,
        events: null,
      };
    }

    start();
    return { mode: 'worker', stream, getJSON, runTest };
  }

  window.MordorTransport = config.transport === 'worker' ? workerTransport() : server;
})();
