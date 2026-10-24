// Drives the browser build's worker as a page would: starts DIST/worker_boot.js
// (wasm/dist.sh's directory), posts one request, collects the messages until
// the worker posts null, and prints them as SSE frames, as node_main.bc.js
// does, so the two can be compared.
//
//   node wasm/test/worker_test.mjs DIST PIPELINE < request.json
import { Worker } from 'node:worker_threads';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const [dist, pipeline] = process.argv.slice(2);
const body = JSON.parse(readFileSync(0, 'utf8') || '{}');
// A browser worker's globals, over node's worker_threads: importScripts loads
// a script, and self.location is where the worker was started from.
const shim = `
  const { parentPort, workerData } = require('node:worker_threads');
  globalThis.self = globalThis;
  globalThis.onmessage = null; // exists, and starts null, in a real worker
  globalThis.postMessage = (m) => parentPort.postMessage(m);
  globalThis.importScripts = (file) => require(file);
  globalThis.location = { href: workerData };
  parentPort.on('message', (data) => self.onmessage && self.onmessage({ data }));
  require(workerData);
`;
const worker = new Worker(shim, {
  eval: true,
  workerData: resolve(dist, 'worker_boot.js'),
});
worker.on('message', (m) => {
  if (m === null) { worker.terminate(); return; }
  process.stdout.write(`data: ${m}\n\n`);
});
worker.on('error', (e) => { console.error(e); process.exit(1); });
worker.postMessage(JSON.stringify({ pipeline, ...body }));
