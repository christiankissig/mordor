/**
 * Recording helpers shared by the demo recorders.
 *
 * `demo.mjs` drives the web UI, `cli-demo.mjs` drives the command line, but
 * both end up with a Playwright .webm that has to become a GIF for the README
 * and an MP4 for the website. That encode is the part worth having exactly one
 * copy of: the two clips are meant to look like a set, and a palette or frame
 * rate that drifts between them shows.
 */

import { spawn } from 'node:child_process';
import path from 'node:path';

/** Run a command to completion, rejecting with its stderr if it fails. */
export function run(cmd, args, { cwd } = {}) {
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

export async function haveFfmpeg() {
  try {
    await run('ffmpeg', ['-version']);
    return true;
  } catch {
    return false;
  }
}

/**
 * Encode a recorded .webm into the artefacts we publish.
 *
 * The GIF palette is generated from the clip itself (`stats_mode=diff`, which
 * weights the pixels that actually change) because a terminal or a graph canvas
 * is mostly flat colour with a little text moving over it, and a generic
 * palette spends its entries on the flat part.
 *
 * @param {string} webm    path to the recording
 * @param {object} opts    { out, name, gif, mp4, fps, gifWidth, colors }
 * @returns {Promise<string[]>} the files written
 */
export async function encode(webm, opts) {
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
