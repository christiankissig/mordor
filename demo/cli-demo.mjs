#!/usr/bin/env node
/**
 * MoRDor CLI demo recorder.
 *
 * The sibling of demo.mjs: same story, same look, same output pipeline, told at
 * the command line instead of in the browser.
 *
 *   node demo/cli-demo.mjs              # build, record, write demo/out/
 *   node demo/cli-demo.mjs --headed     # watch it type
 *   node demo/cli-demo.mjs --no-build   # reuse the binary that is already built
 *
 * Why a browser to record a terminal: none of the terminal recorders (vhs,
 * asciinema+agg, termtosvg) are dependencies of this repo, while Playwright and
 * ffmpeg already are — demo.mjs needs both. Rendering the session into a
 * terminal-styled page and recording that reuses the whole pipeline, and gives
 * the two clips a matching frame, palette and card styling for free.
 *
 * Every command shown is really run: the output on screen is captured from
 * `mordor` itself, not transcribed. If a command starts failing, or its output
 * stops containing what a caption claims, the recording fails loudly rather
 * than quietly publishing a stale demo. That is the same contract demo.mjs has
 * with the web UI.
 *
 * See demo/README.md.
 */

import { chromium } from 'playwright';
import { spawn } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { run, haveFfmpeg, encode } from './record.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(HERE, '..');

/* ------------------------------------------------------------------ */
/* options                                                             */
/* ------------------------------------------------------------------ */

const DEFAULTS = {
  exe: '_build/default/cli/main.exe',
  build: true,
  buildTimeout: 900,      // seconds for `dune build cli/main.exe`
  out: path.join(HERE, 'out'),
  name: 'mordor-cli-demo',
  width: 1200,
  height: 720,
  theme: 'dark',
  headed: false,
  speed: 1,               // >1 = faster demo (all pauses divided by this)
  typeDelay: 42,          // ms per keystroke of the command line
  lineDelay: 55,          // ms between output lines as they stream in
  maxLines: 26,           // output lines shown per command before eliding
  fps: 11,
  gifWidth: 800,
  colors: 96,
  gif: true,
  mp4: true,
  cards: true,
  keepVideo: false,
  timeout: 300,           // seconds any single mordor invocation may take
};

function parseArgs(argv) {
  const o = { ...DEFAULTS };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const next = () => argv[++i];
    switch (a) {
      case '--exe': o.exe = next(); break;
      case '--no-build': o.build = false; break;
      case '--build-timeout': o.buildTimeout = Number(next()); break;
      case '--out': o.out = path.resolve(next()); break;
      case '--name': o.name = next(); break;
      case '--width': o.width = Number(next()); break;
      case '--height': o.height = Number(next()); break;
      case '--theme': o.theme = next(); break;
      case '--headed': o.headed = true; break;
      case '--speed': o.speed = Number(next()); break;
      case '--type-delay': o.typeDelay = Number(next()); break;
      case '--line-delay': o.lineDelay = Number(next()); break;
      case '--max-lines': o.maxLines = Number(next()); break;
      case '--fps': o.fps = Number(next()); break;
      case '--gif-width': o.gifWidth = Number(next()); break;
      case '--colors': o.colors = Number(next()); break;
      case '--no-gif': o.gif = false; break;
      case '--no-mp4': o.mp4 = false; break;
      case '--no-cards': o.cards = false; break;
      case '--keep-video': o.keepVideo = true; break;
      case '--timeout': o.timeout = Number(next()); break;
      case '-h':
      case '--help': usage(); process.exit(0); break;
      default:
        console.error(`unknown option: ${a}`);
        usage();
        process.exit(2);
    }
  }
  return o;
}

function usage() {
  console.log(`
mordor CLI demo recorder

  node demo/cli-demo.mjs [options]

  --exe <path>          mordor binary (default ${DEFAULTS.exe})
  --no-build            skip \`dune build cli/main.exe\`
  --build-timeout <s>   seconds to allow for the build (default ${DEFAULTS.buildTimeout})
  --out <dir>           output directory (default demo/out)
  --name <base>         output basename (default ${DEFAULTS.name})
  --width/--height <n>  recording size (default ${DEFAULTS.width}x${DEFAULTS.height})
  --theme dark|light    terminal palette (default ${DEFAULTS.theme})
  --headed              show the browser doing the typing
  --speed <n>           divide every pause by n
  --type-delay <ms>     per-keystroke delay (default ${DEFAULTS.typeDelay})
  --line-delay <ms>     delay between streamed output lines (default ${DEFAULTS.lineDelay})
  --max-lines <n>       output lines per command before eliding (default ${DEFAULTS.maxLines})
  --fps/--gif-width/--colors    GIF encode knobs
  --no-gif / --no-mp4 / --no-cards / --keep-video
  --timeout <s>         per-command timeout (default ${DEFAULTS.timeout})
`.trim());
}

/* ------------------------------------------------------------------ */
/* running the real thing                                              */
/* ------------------------------------------------------------------ */

/**
 * Run one mordor invocation and hand back what it printed.
 *
 * The banner line is dropped: it is on every command and says nothing, and the
 * frame is only so tall.
 */
function capture(cmd, args, opts, { allowExit = [0] } = {}) {
  return new Promise((resolve, reject) => {
    const p = spawn(cmd, args, {
      cwd: REPO_ROOT,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let out = '';
    let err = '';
    const label = `${path.basename(cmd)} ${args.join(' ')}`;
    const timer = setTimeout(() => {
      p.kill('SIGKILL');
      reject(new Error(`${label} timed out after ${opts.timeout}s`));
    }, opts.timeout * 1000);

    p.stdout.on('data', (b) => { out += b.toString(); });
    p.stderr.on('data', (b) => { err += b.toString(); });
    p.on('error', (e) => { clearTimeout(timer); reject(e); });
    p.on('exit', (code) => {
      clearTimeout(timer);
      if (!allowExit.includes(code)) {
        reject(new Error(`${label} exited ${code}\n${err.slice(-2000)}`));
        return;
      }
      const lines = out
        .split('\n')
        .filter((l) => !/^MoRDor - Symbolic Modular Relaxed Dependencies$/.test(l));
      while (lines.length && lines[lines.length - 1].trim() === '') lines.pop();
      resolve(lines);
    });
  });
}

/* ------------------------------------------------------------------ */
/* the terminal page                                                   */
/* ------------------------------------------------------------------ */

/**
 * A terminal, as a page.
 *
 * The palettes are lifted from web/frontend/static/css/mordor.css so the two
 * recordings look like the same product. Everything the director needs is
 * exposed on `window.__term`.
 */
function terminalPage(opts) {
  const dark = {
    bg: '#1e1e1e', chrome: '#252526', border: '#3e3e42', text: '#d4d4d4',
    dim: '#858585', accent: '#4ec9b0', path: '#569cd6', flag: '#dcdcaa',
    good: '#89d185', bad: '#f48771', rule: '#3e3e42', cardBg: 'rgba(30,30,30,0.94)',
  };
  const light = {
    bg: '#ffffff', chrome: '#f3f3f3', border: '#d0d0d4', text: '#2b2b2b',
    dim: '#6a6a6a', accent: '#128071', path: '#0000ff', flag: '#795e26',
    good: '#2f8a3e', bad: '#c0392b', rule: '#d0d0d4', cardBg: 'rgba(255,255,255,0.94)',
  };
  const c = opts.theme === 'light' ? light : dark;

  return `<!doctype html>
<meta charset="utf-8">
<title>mordor</title>
<style>
  * { box-sizing: border-box; }
  html, body { margin: 0; height: 100%; background: ${c.bg}; }
  body {
    font: 15px/1.5 "DejaVu Sans Mono", "Liberation Mono", "Courier New", monospace;
    color: ${c.text};
    display: flex; flex-direction: column;
  }
  #chrome {
    background: ${c.chrome}; border-bottom: 1px solid ${c.border};
    padding: 8px 12px; display: flex; align-items: center; gap: 8px;
    font-size: 12px; color: ${c.dim}; flex: none;
  }
  .dot { width: 11px; height: 11px; border-radius: 50%; }
  #title { flex: 1; text-align: center; }
  #screen { flex: 1; min-height: 0; overflow: hidden; padding: 14px 18px; position: relative; }
  #scroll { position: absolute; left: 18px; right: 18px; bottom: 14px; }
  .line { white-space: pre-wrap; word-break: break-word; }
  .prompt { color: ${c.accent}; }
  .cwd { color: ${c.path}; }
  .cmd { color: ${c.text}; }
  .flag { color: ${c.flag}; }
  .dim { color: ${c.dim}; }
  .good { color: ${c.good}; font-weight: bold; }
  .bad { color: ${c.bad}; font-weight: bold; }
  .rule { color: ${c.rule}; }
  #cursor {
    display: inline-block; width: 8px; height: 1.05em; background: ${c.text};
    vertical-align: text-bottom; animation: blink 1s steps(1) infinite;
  }
  @keyframes blink { 50% { opacity: 0; } }
  /* In flow, not fixed: the verdict is the last thing a run prints, and a
     floating caption bar sat on top of it. */
  #caption {
    flex: none; padding: 10px 18px;
    background: ${c.chrome}; border-top: 1px solid ${c.border};
    font-size: 15px; color: ${c.text}; display: none;
  }
  #caption b { color: ${c.accent}; }
  #card {
    position: fixed; inset: 0; background: ${c.cardBg};
    display: none; flex-direction: column; align-items: center; justify-content: center;
    gap: 10px; text-align: center;
  }
  #card h1 { margin: 0; font-size: 44px; letter-spacing: 1px; color: ${c.accent}; }
  #card p  { margin: 0; font-size: 18px; color: ${c.dim}; }
</style>
<div id="chrome">
  <span class="dot" style="background:#f48771"></span>
  <span class="dot" style="background:#dcdcaa"></span>
  <span class="dot" style="background:#89d185"></span>
  <span id="title">mordor — ~/workspace/mordor</span>
</div>
<div id="screen"><div id="scroll"></div></div>
<div id="caption"></div>
<div id="card"><h1></h1><p></p></div>
<script>
  const scroll = document.getElementById('scroll');
  const caption = document.getElementById('caption');
  const card = document.getElementById('card');

  const esc = (s) => s.replace(/[&<>]/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[ch]));

  // Colour the lines that carry the verdict. Everything else stays plain: the
  // point of the demo is what mordor says, not how much of it we can paint.
  function classify(text) {
    if (/^(===|---)/.test(text)) return 'rule';
    if (/(Undefined Behavior|Valid):\\s*true/.test(text)) {
      return /Undefined Behavior/.test(text) ? 'bad' : 'good';
    }
    if (/(Undefined Behavior|Valid):\\s*false/.test(text)) {
      return /Undefined Behavior/.test(text) ? 'good' : 'bad';
    }
    if (/^(Events|Executions|Assertion Instances):/.test(text)) return 'dim';
    if (/^\\+/.test(text)) return 'good';
    if (/^-/.test(text)) return 'bad';
    if (/^@@/.test(text)) return 'dim';
    return '';
  }

  window.__term = {
    /** Start a new prompt line and return nothing; type() fills it in. */
    prompt() {
      const el = document.createElement('div');
      el.className = 'line';
      el.innerHTML = '<span class="cwd">~/mordor</span> <span class="prompt">❯</span> <span class="cmd"></span><span id="cursor"></span>';
      scroll.appendChild(el);
      window.__term._cmd = el.querySelector('.cmd');
    },
    /** Append one character to the command being typed. */
    key(ch) {
      const cmd = window.__term._cmd;
      if (!cmd) return;
      // flags in a colour, so a long command line stays readable
      cmd.insertAdjacentHTML('beforeend', esc(ch));
      const t = cmd.textContent;
      cmd.innerHTML = esc(t).replace(/(\\s)(--?[a-z][a-z-]*)/g, '$1<span class="flag">$2</span>');
    },
    /** Retire the cursor from the command line — it has been submitted. */
    enter() {
      const cur = document.getElementById('cursor');
      if (cur) cur.remove();
      window.__term._cmd = null;
    },
    /** Append one output line. */
    out(text) {
      const el = document.createElement('div');
      const cls = classify(text);
      el.className = 'line' + (cls ? ' ' + cls : '');
      el.textContent = text === '' ? ' ' : text;
      scroll.appendChild(el);
    },
    /** Drop everything above, so a long run does not push the frame off. */
    clear() { scroll.innerHTML = ''; },
    caption(html) {
      caption.innerHTML = html || '';
      caption.style.display = html ? 'block' : 'none';
    },
    card(title, subtitle) {
      card.querySelector('h1').textContent = title;
      card.querySelector('p').textContent = subtitle || '';
      card.style.display = 'flex';
    },
    hideCard() { card.style.display = 'none'; },
  };
</script>`;
}

/* ------------------------------------------------------------------ */
/* the director                                                        */
/* ------------------------------------------------------------------ */

function director(page, opts) {
  const scale = (ms) => Math.max(0, Math.round(ms / opts.speed));

  const d = {
    page,

    beat: (ms = 700) => page.waitForTimeout(scale(ms)),

    async say(html, hold = 0) {
      await page.evaluate((h) => window.__term.caption(h), html);
      if (hold) await d.beat(hold);
    },

    async card(title, subtitle, hold = 1600) {
      if (!opts.cards) return;
      await page.evaluate(([t, s]) => window.__term.card(t, s), [title, subtitle]);
      await d.beat(hold);
      await page.evaluate(() => window.__term.hideCard());
      await d.beat(400);
    },

    clear: () => page.evaluate(() => window.__term.clear()),

    /** Type a command at the prompt, a keystroke at a time. */
    async typeCommand(text) {
      await page.evaluate(() => window.__term.prompt());
      for (const ch of text) {
        await page.evaluate((c) => window.__term.key(c), ch);
        await page.waitForTimeout(scale(opts.typeDelay));
      }
      await d.beat(420);
      await page.evaluate(() => window.__term.enter());
    },

    /**
     * Stream lines into the terminal as if they were arriving.
     *
     * Output too long for the frame is elided in the middle, never at the end:
     * the verdict a run is being shown for -- Valid, Undefined Behavior -- is
     * the last thing it prints, and trimming the tail would cut exactly the
     * lines the caption is talking about.
     */
    async printLines(lines, { maxLines = opts.maxLines } = {}) {
      const TAIL = 7;
      let shown = lines;
      let elided = 0;
      if (lines.length > maxLines) {
        const head = Math.max(1, maxLines - TAIL - 1);
        elided = lines.length - head - TAIL;
        shown = [...lines.slice(0, head), null, ...lines.slice(-TAIL)];
      }
      for (const line of shown) {
        if (line === null) {
          await page.evaluate((n) => window.__term.out(`… ${n} lines`), elided);
        } else {
          await page.evaluate((l) => window.__term.out(l), line);
        }
        await page.waitForTimeout(scale(opts.lineDelay));
      }
    },

    /**
     * Type `mordor <args>`, really run it, print what it printed.
     *
     * `expect` is a list of substrings the output has to contain. It is the
     * thing that keeps this demo honest: if a verdict changes, the caption
     * claiming it is now wrong, and the recording stops rather than shipping.
     */
    async command(args, opts2 = {}) {
      return d.shell(path.resolve(REPO_ROOT, opts.exe), args, {
        ...opts2,
        display: opts2.display ?? `mordor ${args.join(' ')}`,
      });
    },

    /** The same, for a command that is not mordor. */
    async shell(cmd, args, {
      expect = [], display = null, maxLines, allowExit = [0], filter = null,
    } = {}) {
      const shown = display ?? `${path.basename(cmd)} ${args.join(' ')}`;
      await d.typeCommand(shown);
      let lines = await capture(cmd, args, opts, { allowExit });
      if (filter) lines = lines.filter(filter);
      const text = lines.join('\n');
      for (const needle of expect) {
        if (!text.includes(needle)) {
          throw new Error(
            `expected ${JSON.stringify(needle)} in the output of \`${shown}\`, `
            + `got:\n${text.slice(0, 1500)}`,
          );
        }
      }
      await d.printLines(lines, { maxLines });
      return lines;
    },
  };
  return d;
}

/* ------------------------------------------------------------------ */
/* the storyboard                                                      */
/* ------------------------------------------------------------------ */

/**
 * The same story demo.mjs tells in the browser: a reclamation program whose
 * flag is written with a relaxed store has a use-after-free; making the store a
 * release store removes it. Reorder, drop or add scenes freely.
 */
const SCENES = [
  {
    title: 'open',
    async run(d) {
      await d.card('MoRDor', 'Symbolic weak-memory analysis, from the terminal', 1600);
      await d.say('A litmus test in — event structures, executions and verdicts out.', 1100);
    },
  },
  {
    title: 'interpret',
    async run(d) {
      await d.say('<b>interpret</b> turns the program into a symbolic event structure.', 700);
      await d.command(['interpret', '--single', 'programs/uaf-bug.lit'], {
        expect: ['Events:'],
      });
      await d.beat(1300);
    },
  },
  {
    title: 'the bug',
    async run(d) {
      await d.clear();
      await d.say('<b>run</b> takes it through elaboration, execution and coherence.', 700);
      const lines = await d.command(['run', '--single', 'programs/uaf-bug.lit'], {
        expect: ['Undefined Behavior: true'],
        // the echoed program is most of this output; the verdict is the point
        maxLines: 18,
      });
      const execs = (lines.find((l) => l.startsWith('Executions:')) || '').split(':')[1]?.trim();
      await d.beat(900);
      await d.say(
        `${execs} executions — and one of them frees the cell another thread is `
        + 'still reading: <b>use-after-free</b>.',
        2400,
      );
    },
  },
  {
    title: 'the fix',
    async run(d) {
      await d.clear();
      await d.say('The flag is written with a <b>relaxed</b> store. One character changes that.', 1500);
      // Shown as a real diff rather than described: the changed line is the
      // whole point, and it is exactly what the program echo elides away.
      await d.shell('diff', ['-u', 'programs/uaf-bug.lit', 'programs/uaf-bug-fixed.lit'], {
        expect: [':rel='],
        allowExit: [0, 1],
        maxLines: 14,
        // the ---/+++ header is absolute paths and mtimes: noise here, and
        // different on every machine
        filter: (l) => !/^(---|\+\+\+) /.test(l),
      });
      await d.beat(1800);
      await d.say('A <b>release</b> store. Same program otherwise.', 1200);
      await d.command(['run', '--single', 'programs/uaf-bug-fixed.lit'], {
        expect: ['Undefined Behavior: false'],
        maxLines: 18,
      });
      await d.beat(900);
      await d.say('Fewer executions, and no undefined behaviour left.', 2200);
    },
  },
  {
    title: 'graphs',
    async run(d) {
      await d.clear();
      await d.say('Every stage can be exported — here the event structure as Graphviz.', 800);
      await d.command(['visual-es', '--single', 'programs/simple-if.lit', '--output-mode', 'dot'], {
        expect: ['digraph G {'],
      });
      await d.beat(1500);
      await d.say('Pipe it to <b>dot</b>, or open the same graph in the web UI.', 2000);
    },
  },
  {
    title: 'close',
    async run(d) {
      await d.say('');
      await d.card('MoRDor', 'github.com/christiankissig/mordor', 1900);
    },
  },
];

/* ------------------------------------------------------------------ */
/* recording                                                           */
/* ------------------------------------------------------------------ */

async function record(opts) {
  await fs.mkdir(opts.out, { recursive: true });
  const videoDir = path.join(opts.out, '.video');
  await fs.rm(videoDir, { recursive: true, force: true });

  const browser = await chromium.launch({ headless: !opts.headed });
  const context = await browser.newContext({
    viewport: { width: opts.width, height: opts.height },
    recordVideo: { dir: videoDir, size: { width: opts.width, height: opts.height } },
    deviceScaleFactor: 1,
  });
  const page = await context.newPage();
  await page.setContent(terminalPage(opts), { waitUntil: 'load' });

  const d = director(page, opts);
  await d.beat(600);

  try {
    for (const scene of SCENES) {
      console.log(`  · ${scene.title}`);
      await scene.run(d);
    }
    await d.beat(600);
  } finally {
    await context.close();
    await browser.close();
  }

  const files = await fs.readdir(videoDir);
  const raw = files.find((f) => f.endsWith('.webm'));
  if (!raw) throw new Error('playwright produced no video');
  const webm = path.join(opts.out, `${opts.name}.webm`);
  await fs.copyFile(path.join(videoDir, raw), webm);
  await fs.rm(videoDir, { recursive: true, force: true });
  return webm;
}

/* ------------------------------------------------------------------ */

async function main() {
  const opts = parseArgs(process.argv.slice(2));

  if ((opts.gif || opts.mp4) && !(await haveFfmpeg())) {
    console.error('ffmpeg not found on PATH — install it, or pass --no-gif --no-mp4.');
    process.exit(1);
  }

  if (opts.build) {
    console.log('• building cli/main.exe');
    await run('dune', ['build', 'cli/main.exe'], { cwd: REPO_ROOT });
  }
  await fs.access(path.resolve(REPO_ROOT, opts.exe));

  console.log(`• recording ${opts.width}x${opts.height} (${opts.theme} theme)`);
  const webm = await record(opts);

  const made = await encode(webm, opts);
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
