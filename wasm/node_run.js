// The browser build under node, for testing (W4, #180): loads Z3, then runs
// node_main.bc.js, which reads a request body on stdin and prints the answer
// as the server's SSE stream frames it.
//
//   node wasm/node_run.js Z3DIR NODE_MAIN_JS PIPELINE < request.json
//
// Z3DIR holds z3.js and z3.wasm (wasm/z3/build.sh's out/).
const path = require('path');
const { loadZ3 } = require('./z3/z3_shim.js');

const [dir, program, ...args] = process.argv.slice(2);
loadZ3(path.resolve(dir))
  .then(() => {
    process.argv = [process.argv[0], path.resolve(program), ...args];
    require(path.resolve(program));
  })
  .catch((e) => {
    console.error(e);
    process.exit(2);
  });
