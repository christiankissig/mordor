// globalThis.mordorZ3: the synchronous solver interface of the browser build's
// Smt_backend (wasm/platform/smt_backend.ml), over Z3 compiled to wasm by
// build.sh (W4, #180; the route WS2, #176, chose).
//
//   const z3 = await loadZ3(dir)          // dir holds z3.js and z3.wasm
//   const s = z3.solver()
//   z3.assert(s, "(declare-fun |x| () Int) (assert (> |x| 0))")
//   z3.check(s)                           // 1 sat, -1 unsat, 0 unknown
//   z3.model(s, ["x"])                    // ["1"], or null if no model
//
// It drives Z3's C API the way the native backend's OCaml bindings do: one
// reference-counted context, a Z3_mk_solver per MoRDor solver, push/pop, and
// model evaluation with completion. The only difference is that terms arrive
// as SMT-LIB text (Z3_parse_smtlib2_string) instead of being built call by
// call, so no AST handle ever has to live on the OCaml side. Z3 is built
// without threads, so every call runs on the calling thread and returns its
// answer: MoRDor, in a Web Worker, blocks on it as it does on native Z3.
//
// Works under node (require) and in a classic Web Worker (importScripts).
//
// The C functions used (build_z3_wasm.sh exports these lines):
// export: _Z3_mk_config _Z3_del_config _Z3_mk_context_rc _Z3_set_error_handler
// export: _Z3_get_error_code _Z3_get_error_msg _Z3_get_full_version
// export: _Z3_mk_solver _Z3_solver_inc_ref _Z3_solver_dec_ref
// export: _Z3_solver_push _Z3_solver_pop _Z3_solver_assert _Z3_solver_check
// export: _Z3_solver_get_model _Z3_model_inc_ref _Z3_model_dec_ref _Z3_model_eval
// export: _Z3_parse_smtlib2_string _Z3_ast_vector_size _Z3_ast_vector_get
// export: _Z3_ast_vector_inc_ref _Z3_ast_vector_dec_ref
// export: _Z3_inc_ref _Z3_dec_ref _Z3_ast_to_string
// export: _Z3_mk_string_symbol _Z3_mk_int_sort _Z3_mk_const
// export: _Z3_solver_get_statistics _Z3_stats_inc_ref _Z3_stats_dec_ref
// export: _Z3_stats_to_string _Z3_solver_get_reason_unknown

(function (root) {
  const isNode =
    typeof process === 'object' && process.versions && process.versions.node;

  function load(file) {
    if (isNode) return require(file);
    importScripts(file);
    return null;
  }

  // MZ_LOG=FILE (node only): a trace of every call -- solver, push, pop,
  // assert (its text), check (its answer), value (each model value).
  const log =
    isNode && process.env.MZ_LOG
      ? (line) => require('fs').appendFileSync(process.env.MZ_LOG, line + '\n')
      : null;

  function api(em) {
    const enc = new TextEncoder();
    const cfg = em._Z3_mk_config();
    const ctx = em._Z3_mk_context_rc(cfg);
    em._Z3_del_config(cfg);
    // No error handler: an error only sets the error code, checked below.
    em._Z3_set_error_handler(ctx, 0);

    function fail() {
      const e = em._Z3_get_error_code(ctx);
      if (e !== 0)
        throw new Error('Z3: ' + em.UTF8ToString(em._Z3_get_error_msg(ctx, e)));
    }
    function withStr(s, f) {
      const bytes = enc.encode(s);
      const p = em._malloc(bytes.length + 1);
      em.HEAPU8.set(bytes, p);
      em.HEAPU8[p + bytes.length] = 0;
      try {
        return f(p);
      } finally {
        em._free(p);
      }
    }
    const intSort = em._Z3_mk_int_sort(ctx);
    em._Z3_inc_ref(ctx, intSort);
    // A MoRDor solver is dropped, never closed, and a Z3 solver costs about
    // a megabyte of wasm memory that the JS garbage collector cannot see:
    // releasing them from a FinalizationRegistry let 3000 queries grow the
    // heap to 2.7 GB. So at most LIVE Z3 solvers exist at a time, the most
    // recently used. A solver keeps its assertions as text, in its scopes,
    // and an evicted one is rebuilt from them -- the same pushes and
    // assertions, minus what was popped -- when it is used again.
    const LIVE = 64;
    const live = new Map(); // id -> solver, least recently used first
    let ids = 0;

    function parseAssert(h, text) {
      const v = withStr(text, (p) =>
        em._Z3_parse_smtlib2_string(ctx, p, 0, 0, 0, 0, 0, 0));
      fail();
      em._Z3_ast_vector_inc_ref(ctx, v);
      try {
        const n = em._Z3_ast_vector_size(ctx, v);
        for (let i = 0; i < n; i++)
          em._Z3_solver_assert(ctx, h, em._Z3_ast_vector_get(ctx, v, i));
        fail();
      } finally {
        em._Z3_ast_vector_dec_ref(ctx, v);
      }
    }
    // The Z3 solver of [s], made or rebuilt if need be.
    function z3solver(s) {
      if (s.h) {
        live.delete(s.id);
        live.set(s.id, s);
        return s.h;
      }
      const h = em._Z3_mk_solver(ctx);
      fail();
      em._Z3_solver_inc_ref(ctx, h);
      s.frames.forEach((frame, i) => {
        if (i > 0) em._Z3_solver_push(ctx, h);
        frame.forEach((text) => parseAssert(h, text));
      });
      s.h = h;
      live.set(s.id, s);
      if (live.size > LIVE) {
        const [oldId, old] = live.entries().next().value;
        live.delete(oldId);
        em._Z3_solver_dec_ref(ctx, old.h);
        old.h = 0;
        rebuilt.evicted++;
      }
      if (s.used) rebuilt.rebuilt++;
      s.used = true;
      return h;
    }
    const rebuilt = { evicted: 0, rebuilt: 0 };

    return {
      counts: () => rebuilt,
      version: () => {
        // Z3_get_full_version has no context; it returns a static string
        return em.UTF8ToString(em._Z3_get_full_version());
      },
      solver() {
        const s = { id: ++ids, h: 0, frames: [[]], used: false };
        if (log) log('solver\t' + s.id);
        z3solver(s);
        return s;
      },
      push(s) {
        if (log) log('push\t' + s.id);
        em._Z3_solver_push(ctx, z3solver(s));
        fail();
        s.frames.push([]);
      },
      pop(s) {
        if (log) log('pop\t' + s.id);
        em._Z3_solver_pop(ctx, z3solver(s), 1);
        fail();
        s.frames.pop();
      },
      // Asserts every (assert ...) of [text], which declares what it names.
      assert(s, text) {
        if (log) log('assert\t' + s.id + '\t' + text.replace(/\n/g, ' '));
        parseAssert(z3solver(s), text);
        s.frames[s.frames.length - 1].push(text);
      },
      check(s) {
        const r = em._Z3_solver_check(ctx, z3solver(s));
        fail();
        s.reason = r === 0
          ? em.UTF8ToString(em._Z3_solver_get_reason_unknown(ctx, z3solver(s)))
          : null;
        if (log) log('check\t' + s.id + '\t' + ({ 1: 'sat', '-1': 'unsat', 0: 'unknown' })[r]);
        return r;
      },
      // Why the last check of [s] said unknown.
      reasonUnknown: (s) => s.reason,
      // The value of each integer constant [names] in the last model, as
      // Z3_ast_to_string prints it; null if there is no model.
      model(s, names) {
        // An evicted solver lost its model: rebuild it and check again.
        if (!s.h) em._Z3_solver_check(ctx, z3solver(s));
        const m = em._Z3_solver_get_model(ctx, z3solver(s));
        if (em._Z3_get_error_code(ctx) !== 0 || m === 0) return null;
        em._Z3_model_inc_ref(ctx, m);
        const out = em._malloc(4);
        try {
          return names.map((name) => {
            const sym = withStr(name, (p) => em._Z3_mk_string_symbol(ctx, p));
            const c = em._Z3_mk_const(ctx, sym, intSort);
            em._Z3_inc_ref(ctx, c);
            try {
              if (!em._Z3_model_eval(ctx, m, c, 1, out)) return null;
              const r = em.HEAP32[out >> 2];
              em._Z3_inc_ref(ctx, r);
              const str = em.UTF8ToString(em._Z3_ast_to_string(ctx, r));
              if (log) log('value\t' + s.id + '\t' + name + '\t' + str);
              em._Z3_dec_ref(ctx, r);
              return str;
            } finally {
              em._Z3_dec_ref(ctx, c);
            }
          });
        } finally {
          em._free(out);
          em._Z3_model_dec_ref(ctx, m);
        }
      },
      statistics(s) {
        const st = em._Z3_solver_get_statistics(ctx, z3solver(s));
        em._Z3_stats_inc_ref(ctx, st);
        const str = em.UTF8ToString(em._Z3_stats_to_string(ctx, st));
        em._Z3_stats_dec_ref(ctx, st);
        return str;
      },
      memoryBytes: () => em.HEAPU8.length,
      memoryKind: () => em.HEAPU8.buffer.constructor.name,
    };
  }

  async function loadZ3(dir) {
    const init = load(dir + '/z3.js') || root.initMordorZ3;
    const em = await init({ locateFile: (f) => dir + '/' + f });
    const z3 = api(em);
    root.mordorZ3 = z3;
    return z3;
  }

  if (typeof module === 'object' && module.exports) module.exports = { loadZ3 };
  root.loadZ3 = loadZ3;
})(typeof globalThis !== 'undefined' ? globalThis : this);
