# Demo recorder

`demo.mjs` drives the MoRDor web UI with Playwright, records the session, and
encodes it as a GIF (for the GitHub README) and an MP4 (for the website).

The story it tells, in ~35 seconds:

1. type a reclamation program whose flag is written with a **relaxed** store;
2. run the pipeline and step through the executions MoRDor derives;
3. open the **Use-After-Free** panel — MoRDor flags one execution, click it to
   see the offending graph;
4. change the store to `:rel=`;
5. re-run: two executions, no use-after-free.

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
make demo                     # same thing
```

Outputs land in `demo/out/`:

| file                    | what for                                  |
|-------------------------|-------------------------------------------|
| `mordor-demo.gif`       | 800px wide, ~4 MB — README / docs         |
| `mordor-demo.mp4`       | h264, ~1 MB — website, slides             |

The script starts `dune exec mordor-web` itself and shuts it down afterwards.
If a server is already listening on the URL it just uses that one.

Useful flags:

```bash
node demo/demo.mjs --headed          # watch the browser drive itself
node demo/demo.mjs --no-server       # reuse an already-running server
node demo/demo.mjs --speed 1.5       # shorten every pause
node demo/demo.mjs --theme light     # light-theme recording
node demo/demo.mjs --keep-video      # keep the raw .webm too
node demo/demo.mjs --help            # everything else
```

## Using the output

GitHub README:

```markdown
![MoRDor finding a use-after-free and verifying the fix](demo/out/mordor-demo.gif)
```

Website (`christian-kissig-org`, projects page bundle):

```bash
cp demo/out/mordor-demo.gif ~/workspace/christian-kissig-org/content/projects/mordor-demo.gif
```

## Editing the demo

Two places, both near the top of `demo.mjs`:

- `BUGGY` — the litmus program that gets typed in.
- `SCENES` — the storyboard. Each scene is `{ title, run(d) }`; `d` is the
  director, with `say`, `card`, `beat`, `click`, `type`, `selectIn`,
  `runAnalysis`, `openAccordion` and `stats`. Scenes play in order, so adding,
  reordering or deleting one is a local change.

Every step waits on real UI state (`status` reaching `Complete`, elements
becoming visible) rather than on fixed sleeps, so the recording stays correct
when MoRDor gets faster or slower. If a selector disappears from the frontend
the run fails loudly instead of quietly recording a broken demo — which is the
point of re-running it after changes.

The recorder also nudges the editor/graph split wider (`--left-panel`) before
recording, the same thing dragging the resizer would do, so the source panel
header is not cramped at 1440×810.
