// The browser build's Web Worker (W4, #180): the script a page starts,
//
//   new Worker('worker_boot.js')
//
// with z3_shim.js, z3.js, z3.wasm and worker.bc.js next to it. Loading Z3 is
// the one asynchronous step: this script loads it, then worker.bc.js (W3,
// #179), which answers requests synchronously from then on. A request posted
// while Z3 loads waits for it; if Z3 cannot load, every request is answered
// with an error message, in the protocol worker.bc.js speaks: JSON strings,
// then null.
(function () {
  const base = self.location.href.replace(/\/[^/]*$/, '');
  const waiting = [];
  self.onmessage = (event) => waiting.push(event);
  importScripts(base + '/z3_shim.js');
  self
    .loadZ3(base)
    .then(() => {
      importScripts(base + '/worker.bc.js');
      waiting.forEach((event) => self.onmessage(event));
    })
    .catch((e) => {
      const message = JSON.stringify({
        type: 'error',
        message: 'Z3 could not be loaded: ' + e,
      });
      self.onmessage = () => {
        self.postMessage(message);
        self.postMessage(null);
      };
      waiting.forEach((event) => self.onmessage(event));
    });
})();
