#!/usr/bin/env node
/**
 * MoRDor web-UI demo recorder.
 *
 * Drives the MoRDor web UI with Playwright, records a video, and converts it
 * into a GIF (for the GitHub README) and an MP4 (for the website).
 *
 *   node demo/demo.mjs                 # build+start server, record, write demo/out/
 *   node demo/demo.mjs --headed        # watch it happen
 *   node demo/demo.mjs --no-server     # reuse a server already on :8080
 *
 * See demo/README.md for all flags.
 */

import { chromium } from 'playwright';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import fs from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import { fileURLToPath } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(HERE, '..');

/* ------------------------------------------------------------------ */
/* options                                                             */
/* ------------------------------------------------------------------ */

const DEFAULTS = {
  url: 'http://localhost:8080',
  serverCmd: 'dune exec mordor-web',
  server: true, // start the server ourselves if it is not already up
  serverTimeout: 600, // seconds to wait for `dune exec` to build + listen
  out: path.join(HERE, 'out'),
  name: 'mordor-demo',
  width: 1440,
  height: 810,
  theme: 'dark',
  headed: false,
  speed: 1, // >1 = faster demo (all pauses divided by this)
  typeDelay: 20, // ms per keystroke
  leftPanel: 30, // % of the window given to the source editor
  fps: 11,
  gifWidth: 800,
  colors: 96,
  gif: true,
  mp4: true,
  cards: true, // title / end cards
  keepVideo: false,
  timeout: 120, // seconds to wait for an analysis run to complete
};

function parseArgs(argv) {
  const o = { ...DEFAULTS };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const next = () => argv[++i];
    switch (a) {
      case '--url': o.url = next(); break;
      case '--server-cmd': o.serverCmd = next(); break;
      case '--no-server': o.server = false; break;
      case '--server-timeout': o.serverTimeout = Number(next()); break;
      case '--out': o.out = path.resolve(next()); break;
      case '--name': o.name = next(); break;
      case '--width': o.width = Number(next()); break;
      case '--height': o.height = Number(next()); break;
      case '--theme': o.theme = next(); break;
      case '--headed': o.headed = true; break;
      case '--speed': o.speed = Number(next()); break;
      case '--type-delay': o.typeDelay = Number(next()); break;
      case '--left-panel': o.leftPanel = Number(next()); break;
      case '--fps': o.fps = Number(next()); break;
      case '--gif-width': o.gifWidth = Number(next()); break;
      case '--colors': o.colors = Number(next()); break;
      case '--no-gif': o.gif = false; break;
      case '--no-mp4': o.mp4 = false; break;
      case '--no-cards': o.cards = false; break;
      case '--keep-video': o.keepVideo = true; break;
      case '--timeout': o.timeout = Number(next()); break;
      case '-h': case '--help': printHelp(); process.exit(0);
      default:
        console.error(`unknown flag: ${a}  (try --help)`);
        process.exit(2);
    }
  }
  return o;
}

function printHelp() {
  console.log(`mordor demo recorder

usage: node demo/demo.mjs [flags]

  --url <url>            MoRDor web URL            (${DEFAULTS.url})
  --server-cmd <cmd>     command that starts it    (${DEFAULTS.serverCmd})
  --no-server            never start a server; fail if --url is not reachable
  --server-timeout <s>   wait this long for the build+boot (${DEFAULTS.serverTimeout})
  --out <dir>            output directory          (demo/out)
  --name <base>          output basename           (${DEFAULTS.name})
  --width/--height <px>  recording size            (${DEFAULTS.width}x${DEFAULTS.height})
  --theme dark|light     UI theme                  (${DEFAULTS.theme})
  --headed               run the browser visibly
  --speed <n>            playback speed multiplier (${DEFAULTS.speed})
  --type-delay <ms>      per-keystroke delay       (${DEFAULTS.typeDelay})
  --left-panel <pct>     editor width, % of window (${DEFAULTS.leftPanel})
  --fps <n>              GIF frame rate            (${DEFAULTS.fps})
  --gif-width <px>       GIF width, height auto    (${DEFAULTS.gifWidth})
  --colors <n>           GIF palette size          (${DEFAULTS.colors})
  --no-gif / --no-mp4    skip an output format
  --no-cards             skip the title/end cards
  --keep-video           keep the raw .webm
  --timeout <s>          per-analysis timeout      (${DEFAULTS.timeout})
`);
}

/* ------------------------------------------------------------------ */
/* the demo programs                                                   */
/* ------------------------------------------------------------------ */

/** Racy reclamation: thread 1 frees rC once it observes rcu = 0, thread 2
 *  reads *rC and then relaxes-stores rcu = 0 — nothing orders the two. */
const BUGGY = `rC := malloc(1);
*rC := 0;
rcu := malloc(1);
*rcu := 1;
fence(relacq);
{
  rtemp := *rcu;
  if (rtemp = 0) {
    free(rC)
  }
}
|||
{
  rv := *rC;
  *rcu := 0
}`;

/* ------------------------------------------------------------------ */
/* browser-side overlay: fake cursor, captions, title cards            */
/* ------------------------------------------------------------------ */

function overlayScript(theme) {
  return `(() => {
  const install = () => {
    if (document.getElementById('__demo_style')) return;
    const style = document.createElement('style');
    style.id = '__demo_style';
    style.textContent = \`
      #__demo_cursor {
        position: fixed; left: 0; top: 0; width: 22px; height: 22px;
        margin: -11px 0 0 -11px; border-radius: 50%;
        border: 2px solid rgba(255,255,255,.92);
        background: rgba(255,255,255,.18);
        box-shadow: 0 0 0 1px rgba(0,0,0,.45), 0 2px 10px rgba(0,0,0,.5);
        pointer-events: none; z-index: 2147483647;
        transition: transform .09s ease-out, opacity .2s;
        opacity: 0;
      }
      #__demo_cursor.down { transform: scale(.72); background: rgba(255,255,255,.5); }
      .__demo_ripple {
        position: fixed; width: 18px; height: 18px; margin: -9px 0 0 -9px;
        border-radius: 50%; border: 2px solid rgba(255,255,255,.85);
        pointer-events: none; z-index: 2147483646;
        animation: __demo_ripple .5s ease-out forwards;
      }
      @keyframes __demo_ripple {
        to { transform: scale(3.2); opacity: 0; }
      }
      #__demo_caption {
        position: fixed; left: 50%; bottom: var(--demo-caption-bottom, 26px);
        transform: translateX(-50%) translateY(8px);
        max-width: 78%; padding: .62rem 1.15rem;
        background: rgba(8,10,14,.86); color: #f2f4f8;
        border: 1px solid rgba(255,255,255,.14); border-radius: 10px;
        backdrop-filter: blur(6px);
        font: 500 17px/1.35 ui-sans-serif, -apple-system, "Segoe UI", Roboto, sans-serif;
        letter-spacing: .1px; text-align: center;
        box-shadow: 0 8px 28px rgba(0,0,0,.45);
        opacity: 0; transition: opacity .28s ease, transform .28s ease;
        pointer-events: none; z-index: 2147483645;
      }
      #__demo_caption.show { opacity: 1; transform: translateX(-50%) translateY(0); }
      #__demo_caption b { color: #7fd1c1; font-weight: 600; }
      #__demo_card {
        position: fixed; inset: 0; display: flex; flex-direction: column;
        align-items: center; justify-content: center; gap: .9rem;
        background: ${theme === 'light' ? 'rgba(250,250,252,.97)' : 'rgba(10,11,15,.97)'};
        color: ${theme === 'light' ? '#14161c' : '#f4f6fa'};
        font-family: ui-sans-serif, -apple-system, "Segoe UI", Roboto, sans-serif;
        opacity: 0; transition: opacity .45s ease; pointer-events: none;
        z-index: 2147483644;
      }
      #__demo_card.show { opacity: 1; }
      #__demo_card .t { font-size: 46px; font-weight: 650; letter-spacing: -.5px; }
      #__demo_card .s { font-size: 20px; opacity: .72; font-weight: 450; }
      #__demo_card .rule { width: 74px; height: 3px; border-radius: 2px; background: #7fd1c1; }
    \`;
    document.head.appendChild(style);

    const cursor = document.createElement('div');
    cursor.id = '__demo_cursor';
    const caption = document.createElement('div');
    caption.id = '__demo_caption';
    const card = document.createElement('div');
    card.id = '__demo_card';
    card.innerHTML = '<div class="t"></div><div class="rule"></div><div class="s"></div>';
    document.body.append(cursor, caption, card);

    addEventListener('mousemove', (e) => {
      cursor.style.opacity = '1';
      cursor.style.left = e.clientX + 'px';
      cursor.style.top = e.clientY + 'px';
    }, true);
    addEventListener('mousedown', (e) => {
      cursor.classList.add('down');
      const r = document.createElement('div');
      r.className = '__demo_ripple';
      r.style.left = e.clientX + 'px';
      r.style.top = e.clientY + 'px';
      document.body.appendChild(r);
      setTimeout(() => r.remove(), 600);
    }, true);
    addEventListener('mouseup', () => cursor.classList.remove('down'), true);

    // Float the caption over the app's activity log strip, so it never covers
    // the graph or its controls.
    const placeCaption = () => {
      const log = document.getElementById('log');
      const h = log ? log.getBoundingClientRect().height : 0;
      document.documentElement.style.setProperty(
        '--demo-caption-bottom', Math.max(24, Math.round(h / 2) - 26) + 'px');
    };
    placeCaption();
    addEventListener('resize', placeCaption);

    window.__demo = {
      caption(html) {
        placeCaption();
        caption.innerHTML = html || '';
        caption.classList.toggle('show', !!html);
      },
      card(title, subtitle) {
        card.querySelector('.t').textContent = title || '';
        card.querySelector('.s').textContent = subtitle || '';
        card.classList.add('show');
      },
      hideCard() { card.classList.remove('show'); },
      hideCursor() { cursor.style.opacity = '0'; },
    };
  };
  if (document.body) install();
  else addEventListener('DOMContentLoaded', install);
})();`;
}

/* ------------------------------------------------------------------ */
/* small helpers                                                       */
/* ------------------------------------------------------------------ */

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function healthy(url) {
  try {
    const res = await fetch(new URL('/health', url), {
      signal: AbortSignal.timeout(2000),
    });
    return res.ok;
  } catch {
    return false;
  }
}

/** Start the web server (unless one is already listening) and return a stop fn. */
async function ensureServer(opts) {
  if (await healthy(opts.url)) {
    console.log(`• server already up at ${opts.url}`);
    return async () => {};
  }
  if (!opts.server) {
    throw new Error(`no server at ${opts.url} and --no-server was given`);
  }

  console.log(`• starting server: ${opts.serverCmd}  (cwd ${REPO_ROOT})`);
  const child = spawn(opts.serverCmd, {
    cwd: REPO_ROOT,
    shell: true,
    detached: true, // own process group, so we can kill dune *and* the exe
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  let log = '';
  const keep = (buf) => {
    log = (log + buf.toString()).slice(-4000);
  };
  child.stdout.on('data', keep);
  child.stderr.on('data', keep);

  let exited = false;
  child.on('exit', () => { exited = true; });

  const stop = async () => {
    if (exited) return;
    try { process.kill(-child.pid, 'SIGTERM'); } catch {}
    await Promise.race([once(child, 'exit'), sleep(4000)]);
    try { process.kill(-child.pid, 'SIGKILL'); } catch {}
  };

  const deadline = Date.now() + opts.serverTimeout * 1000;
  process.stdout.write('  waiting for build + boot ');
  while (Date.now() < deadline) {
    if (exited) {
      process.stdout.write('\n');
      throw new Error(`server command exited early:\n${log}`);
    }
    if (await healthy(opts.url)) {
      process.stdout.write(' up\n');
      return stop;
    }
    process.stdout.write('.');
    await sleep(1500);
  }
  process.stdout.write('\n');
  await stop();
  throw new Error(`server did not come up within ${opts.serverTimeout}s:\n${log}`);
}

function run(cmd, args, { cwd } = {}) {
  return new Promise((resolve, reject) => {
    const p = spawn(cmd, args, { cwd, stdio: ['ignore', 'pipe', 'pipe'] });
    let err = '';
    p.stderr.on('data', (b) => { err += b.toString(); });
    p.on('error', reject);
    p.on('exit', (code) =>
      code === 0
        ? resolve()
        : reject(new Error(`${cmd} exited ${code}\n${err.slice(-3000)}`)));
  });
}

async function haveFfmpeg() {
  try {
    await run('ffmpeg', ['-version']);
    return true;
  } catch {
    return false;
  }
}

/* ------------------------------------------------------------------ */
/* the director: page-driving helpers used by the scenes                */
/* ------------------------------------------------------------------ */

function director(page, opts) {
  const scale = (ms) => Math.max(0, Math.round(ms / opts.speed));

  const d = {
    page,

    /** Hold the frame for `ms` (scaled by --speed). */
    beat: (ms = 700) => page.waitForTimeout(scale(ms)),

    /** Show a subtitle; pass '' to clear. Simple <b> markup is allowed. */
    async say(html, hold = 0) {
      await page.evaluate((h) => window.__demo?.caption(h), html);
      if (hold) await d.beat(hold);
    },

    async card(title, subtitle, hold = 1600) {
      if (!opts.cards) return;
      await page.evaluate(([t, s]) => window.__demo?.card(t, s), [title, subtitle]);
      await d.beat(hold);
      await page.evaluate(() => window.__demo?.hideCard());
      await d.beat(500);
    },

    /** Glide the pointer to the centre of `selector`. */
    async moveTo(selector, { steps = 26 } = {}) {
      const box = await page.locator(selector).first().boundingBox();
      if (!box) throw new Error(`no bounding box for ${selector}`);
      const x = box.x + box.width / 2;
      const y = box.y + box.height / 2;
      await page.mouse.move(x, y, { steps });
      await d.beat(220);
      return { x, y };
    },

    /** Glide, then click — so the fake cursor is visible doing it. */
    async click(selector, { pre = 240, post = 420 } = {}) {
      await d.moveTo(selector);
      await d.beat(pre);
      await page.mouse.down();
      await d.beat(90);
      await page.mouse.up();
      await d.beat(post);
    },

    /** Type into a field one key at a time. */
    async type(selector, text, { delay = opts.typeDelay } = {}) {
      const el = page.locator(selector);
      await el.click();
      await el.pressSequentially(text, { delay: Math.round(delay / opts.speed) });
    },

    /**
     * Select `needle` inside a textarea (last occurrence by default) so the
     * highlight is visible, then optionally type over it.
     */
    async selectIn(selector, needle, { last = true } = {}) {
      await page.locator(selector).click();
      await page.evaluate(
        ([sel, n, useLast]) => {
          const ta = document.querySelector(sel);
          const i = useLast ? ta.value.lastIndexOf(n) : ta.value.indexOf(n);
          if (i < 0) throw new Error('substring not found: ' + n);
          ta.focus();
          ta.setSelectionRange(i, i + n.length);
        },
        [selector, needle, last],
      );
      await d.beat(700);
    },

    /** Kick off the current action and wait for the run to finish. */
    async runAnalysis() {
      await d.click('#action-btn');
      await page.waitForFunction(
        () => document.getElementById('status')?.textContent === 'Complete',
        undefined,
        { timeout: opts.timeout * 1000 },
      );
      await d.beat(600);
    },

    /** Open a sidebar accordion if it is not already open. */
    async openAccordion(targetId) {
      const open = await page.evaluate(
        (id) => document.getElementById(id)?.classList.contains('active'),
        targetId,
      );
      if (!open) await d.click(`.accordion-header[data-target="${targetId}"]`);
    },

    /** Read the little stats strip under the graph. */
    stats: () =>
      page.evaluate(() => ({
        nodes: document.getElementById('node-count')?.textContent,
        edges: document.getElementById('edge-count')?.textContent,
        executions: document.getElementById('execution-count')?.textContent,
      })),
  };
  return d;
}

/* ------------------------------------------------------------------ */
/* the storyboard                                                      */
/* ------------------------------------------------------------------ */

/**
 * Each scene is `{ title, run }`. Reorder, drop or add scenes freely — the
 * recorder just plays them in order.
 */
const SCENES = [
  {
    title: 'open',
    async run(d) {
      await d.card('MoRDor', 'Symbolic weak-memory analysis, in the browser', 1500);
      await d.say('A litmus test in — event structures and executions out.', 900);
    },
  },

  {
    title: 'write the program',
    async run(d) {
      await d.say('Reclamation guarded only by <b>relaxed</b> accesses…');
      await d.type('#litmus-input', BUGGY);
      await d.beat(500);
      await d.say('Thread 1 frees <b>rC</b> once it sees <b>rcu = 0</b>; '
                + 'thread 2 reads <b>*rC</b> first — or does it?', 1400);
    },
  },

  {
    title: 'analyse',
    async run(d) {
      await d.say('Run the pipeline: parse → interpret → elaborate → execute.');
      await d.runAnalysis();
      const s = await d.stats();
      await d.say(`Event structure: <b>${s.nodes}</b> events, `
                + `<b>${s.edges}</b> relations.`, 1100);
    },
  },

  {
    title: 'browse executions',
    async run(d) {
      const s = await d.stats();
      await d.say(`<b>${s.executions}</b> consistent executions under SMRD — `
                + 'step through them.');
      for (let i = 0; i < 2; i++) {
        await d.click('#next-btn', { post: 800 });
      }
    },
  },

  {
    title: 'the bug',
    async run(d) {
      await d.say('Every execution is checked for undefined behaviour.');
      await d.openAccordion('uaf-content');
      await d.beat(500);
      await d.say('<b>Use-after-free</b>: nothing stops the read of <b>*rC</b> '
                + 'from landing after the free.', 700);
      await d.click('.uaf-item', { post: 900 });
      await d.say('Click the finding to jump to the offending execution.', 1500);
    },
  },

  {
    title: 'the fix',
    async run(d) {
      await d.say('Fix it where the ordering is actually missing.');
      await d.selectIn('#litmus-input', ':=');
      await d.say('Make the flag store a <b>release</b>.', 300);
      await d.page.keyboard.type(':rel=', { delay: 110 });
      await d.beat(900);
    },
  },

  {
    title: 'verified',
    async run(d) {
      await d.say('Re-run it.');
      await d.runAnalysis();
      await d.click('#fit-btn', { post: 500 }); // settle the fresh layout
      await d.openAccordion('uaf-content');
      await d.beat(400);
      const s = await d.stats();
      await d.say(`<b>${s.executions}</b> executions, no use-after-free — `
                + 'the race is gone.', 2000);
    },
  },

  {
    title: 'close',
    async run(d) {
      await d.say('');
      await d.page.evaluate(() => window.__demo?.hideCursor());
      await d.card('MoRDor', 'github.com/christiankissig/mordor', 1800);
    },
  },
];

/* ------------------------------------------------------------------ */
/* record + encode                                                     */
/* ------------------------------------------------------------------ */

async function record(opts) {
  const videoDir = await fs.mkdtemp(path.join(os.tmpdir(), 'mordor-demo-'));
  const browser = await chromium.launch({ headless: !opts.headed });
  const context = await browser.newContext({
    viewport: { width: opts.width, height: opts.height },
    deviceScaleFactor: 1,
    colorScheme: opts.theme === 'light' ? 'light' : 'dark',
    recordVideo: { dir: videoDir, size: { width: opts.width, height: opts.height } },
  });

  // Theme is remembered in localStorage and applied before first paint.
  await context.addInitScript(
    (t) => { try { localStorage.setItem('mordor-theme', t); } catch {} },
    opts.theme,
  );
  await context.addInitScript(overlayScript(opts.theme));

  const page = await context.newPage();
  const consoleErrors = [];
  page.on('pageerror', (e) => consoleErrors.push(String(e)));

  await page.goto(opts.url, { waitUntil: 'domcontentloaded' });

  // The graph view needs cytoscape, which the page pulls from a CDN.
  try {
    await page.waitForFunction(() => !!window.cytoscape, undefined, { timeout: 20000 });
  } catch {
    throw new Error(
      'cytoscape never loaded — index.html fetches it from unpkg.com, so the '
      + 'demo needs network access (or a vendored copy of the CDN scripts).',
    );
  }
  await page.waitForFunction(() => !!window.__demo, undefined, { timeout: 10000 });

  // Give the editor a bit more room than the default split — same thing the
  // resizer does, just without spending demo seconds dragging it.
  await page.evaluate((pct) => {
    const left = document.getElementById('left-panel');
    if (left) left.style.flex = `0 0 ${pct}%`;
  }, opts.leftPanel);

  await page.mouse.move(opts.width / 2, opts.height - 60);
  await sleep(700); // let the first video frames settle

  const d = director(page, opts);
  for (const scene of SCENES) {
    process.stdout.write(`  ▸ ${scene.title}\n`);
    await scene.run(d);
  }
  await d.beat(700);

  const video = page.video();
  await context.close(); // flushes the video file
  const raw = await video.path();
  await browser.close();

  if (consoleErrors.length) {
    console.warn(`! page errors during the run:\n   ${consoleErrors.join('\n   ')}`);
  }

  await fs.mkdir(opts.out, { recursive: true });
  const webm = path.join(opts.out, `${opts.name}.webm`);
  await fs.copyFile(raw, webm);
  await fs.rm(videoDir, { recursive: true, force: true });
  return webm;
}

async function encode(webm, opts) {
  const made = [];

  if (opts.gif) {
    const gif = path.join(opts.out, `${opts.name}.gif`);
    const filter =
      `fps=${opts.fps},scale=${opts.gifWidth}:-2:flags=lanczos,split[a][b];`
      + `[a]palettegen=max_colors=${opts.colors}:stats_mode=diff[p];`
      + `[b][p]paletteuse=dither=bayer:bayer_scale=5:diff_mode=rectangle`;
    await run('ffmpeg', ['-y', '-i', webm, '-filter_complex', filter, '-loop', '0', gif]);
    made.push(gif);
  }

  if (opts.mp4) {
    const mp4 = path.join(opts.out, `${opts.name}.mp4`);
    await run('ffmpeg', [
      '-y', '-i', webm,
      // yuv420p + even dimensions: what browsers and QuickTime will actually play
      '-vf', 'scale=trunc(iw/2)*2:trunc(ih/2)*2,format=yuv420p',
      '-c:v', 'libx264', '-preset', 'slow', '-crf', '24',
      '-movflags', '+faststart', '-an', mp4,
    ]);
    made.push(mp4);
  }

  return made;
}

/* ------------------------------------------------------------------ */

async function main() {
  const opts = parseArgs(process.argv.slice(2));

  if ((opts.gif || opts.mp4) && !(await haveFfmpeg())) {
    console.error('ffmpeg not found on PATH — install it, or pass --no-gif --no-mp4.');
    process.exit(1);
  }

  const stopServer = await ensureServer(opts);
  let webm;
  try {
    console.log(`• recording ${opts.width}x${opts.height} (${opts.theme} theme)`);
    webm = await record(opts);
  } finally {
    await stopServer();
  }

  const made = await encode(webm, opts);
  // Never throw the recording away if it is the only thing we produced.
  if (opts.keepVideo || made.length === 0) made.unshift(webm);
  else await fs.rm(webm, { force: true });

  console.log('\n✔ done');
  for (const f of made) {
    const { size } = await fs.stat(f);
    console.log(`   ${path.relative(process.cwd(), f)}  ${(size / 1e6).toFixed(2)} MB`);
  }
}

main().catch((err) => {
  console.error(`\n✖ ${err.message}`);
  process.exit(1);
});
