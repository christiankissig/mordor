// Drives wasm/worker.bc.js as a page would: posts one request, collects the
// messages until the worker posts null, and prints them as SSE frames, as
// node_main.bc.js does, so the two can be compared.
//
//   node wasm/test/worker_test.mjs WORKER_JS PIPELINE < request.json
import { Worker } from 'node:worker_threads';
import { readFileSync } from 'node:fs';

const [workerJs, pipeline] = process.argv.slice(2);
const body = JSON.parse(readFileSync(0, 'utf8') || '{}');
// A browser worker's globals, over node's worker_threads.
const shim = `
  const { parentPort, workerData } = require('node:worker_threads');
  globalThis.self = globalThis;
  globalThis.onmessage = null; // exists, and starts null, in a real worker
  globalThis.postMessage = (m) => parentPort.postMessage(m);
  parentPort.on('message', (data) => self.onmessage && self.onmessage({ data }));
  require(workerData);
`;
const worker = new Worker(shim, { eval: true, workerData: workerJs });
worker.on('message', (m) => {
  if (m === null) { worker.terminate(); return; }
  process.stdout.write(`data: ${m}\n\n`);
});
worker.on('error', (e) => { console.error(e); process.exit(1); });
worker.postMessage(JSON.stringify({ pipeline, ...body }));
