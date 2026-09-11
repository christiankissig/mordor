# Demo recorders

Two recorders, one story, told on the two surfaces MoRDor has:

| script | surface | outputs |
|---|---|---|
| `demo.mjs`     | the web UI  | `out/mordor-demo-{dark,light}.gif` / `.mp4` |
| `cli-demo.mjs` | the CLI     | `out/mordor-cli-demo.gif` / `.mp4` |

Both drive Playwright, record a `.webm`, and hand it to the shared encoder in
`record.mjs` — so the two clips come out with the same frame rate, palette and
card styling, and read as a set.

`cli-demo.mjs` records a terminal by rendering one as a page. None of the
terminal recorders (vhs, asciinema + agg, termtosvg) are dependencies of this
repo, while Playwright and ffmpeg already are, so this reuses the whole pipeline
rather than adding a toolchain. Every command in it is really run and its real
output streamed in; if a command starts failing, or stops printing what a
caption claims, the recording stops instead of publishing a stale demo.

## The web-UI story (`demo.mjs`), in ~35 seconds:

1. type a reclamation program whose flag is written with a **relaxed** store;
2. run the pipeline and step through the executions MoRDor derives;
3. open the **Use-After-Free** panel — MoRDor flags one execution, click it to
   see the offending graph;
4. change the store to `:rel=`;
5. re-run: two executions, no use-after-free.

## The CLI story (`cli-demo.mjs`), in ~45 seconds

1. `mordor interpret` on the same reclamation program — the event structure;
2. `mordor run` — 3 executions and **Undefined Behavior: true**;
3. `diff -u` against the fixed program — one character, `:=` to `:rel=`;
4. `mordor run` on the fixed one — 2 executions, no undefined behaviour;
5. `mordor visual-es --output-mode dot` — the event structure as Graphviz.

## Setup

```bash
cd demo
npm install          # also downloads the Chromium build Playwright needs
```

Also needs `ffmpeg` on `PATH` (for the GIF/MP4 encode), and network access —
the UI loads cytoscape and Prism from CDNs.

## Recording

From the repository root:

```bash
node demo/demo.mjs            # build + start mordor-web, record, encode
node demo/demo.mjs --theme light   # the same in the light theme
node demo/cli-demo.mjs        # build cli/main.exe, record, encode
make demo                     # the web one, in both themes
make demo-cli                 # the CLI one
```

Outputs land in `demo/out/`:

| file                    | what for                                  |
|-------------------------|-------------------------------------------|
| `mordor-demo-dark.gif`  | 800px wide, ~4.5 MB — README / docs       |
| `mordor-demo-dark.mp4`  | h264, ~1.5 MB — website, slides           |
| `mordor-demo-light.gif` | 800px wide, ~4 MB — README / docs         |
| `mordor-demo-light.mp4` | h264, ~1.5 MB — website, slides           |
| `mordor-cli-demo.gif`   | 800px wide, ~3 MB — README / docs         |
| `mordor-cli-demo.mp4`   | h264, ~1 MB — website, slides             |

`demo.mjs` starts `dune exec mordor-web` itself and shuts it down afterwards; if
a server is already listening on the URL it just uses that one. `cli-demo.mjs`
runs `dune build cli/main.exe` and then the binary directly — no server.

Useful flags — most are common to both:

```bash
node demo/demo.mjs --headed          # watch the browser drive itself
node demo/demo.mjs --no-server       # reuse an already-running server
node demo/cli-demo.mjs --no-build    # reuse the binary already built
node demo/cli-demo.mjs --speed 1.5   # shorten every pause
node demo/cli-demo.mjs --theme light # light-theme recording
node demo/cli-demo.mjs --max-lines 18  # tighter per-command output budget
node demo/cli-demo.mjs --help        # everything else
```

## Using the output

GitHub README, showing the recording in the reader's theme:

```html
<picture>
  <source media="(prefers-color-scheme: light)" srcset="demo/out/mordor-demo-light.gif">
  <img alt="MoRDor finding a use-after-free and verifying the fix" src="demo/out/mordor-demo-dark.gif">
</picture>
```

```markdown
![The same, from the command line](demo/out/mordor-cli-demo.gif)
```

Website (`christian-kissig-org`, projects page bundle):

```bash
cp demo/out/mordor-demo-dark.gif ~/workspace/christian-kissig-org/content/projects/mordor-demo.gif
```

## Editing the demos

Both scripts are built the same way: a `SCENES` array of `{ title, run(d) }`,
played in order, with `d` a director. Adding, reordering or dropping a scene is
a local change.

`demo.mjs`:

- `BUGGY` — the litmus program that gets typed in.
- director: `say`, `card`, `beat`, `click`, `type`, `selectIn`, `runAnalysis`,
  `openAccordion`, `stats`.

`cli-demo.mjs`:

- director: `say`, `card`, `beat`, `clear`, `typeCommand`, `printLines`,
  `command` (a mordor invocation) and `shell` (anything else, e.g. `diff`).
- `command`/`shell` take `expect: [...]` — substrings the output has to contain.
  That is what keeps a caption honest: if a verdict changes, the run fails with
  the actual output rather than recording a caption that no longer matches.
- They also take `maxLines`, and long output is elided **in the middle**, never
  at the end — the verdict a run is being shown for is the last thing it prints.

Every step waits on real UI state (`status` reaching `Complete`, elements
becoming visible) rather than on fixed sleeps, so the recording stays correct
when MoRDor gets faster or slower. If a selector disappears from the frontend
the run fails loudly instead of quietly recording a broken demo — which is the
point of re-running it after changes.

`demo.mjs` also nudges the editor/graph split wider (`--left-panel`) before
recording, the same thing dragging the resizer would do, so the source panel
header is not cramped at 1440×810.

The terminal palettes in `cli-demo.mjs` are lifted from
`web/frontend/static/css/mordor.css`, so a change to the UI theme has a matching
edit here.
