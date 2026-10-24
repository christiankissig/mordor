#!/usr/bin/env python3
"""The browser build's verdicts against the native CLI's (W4, #180).

    python3 -I wasm/test/verdicts.py MORDOR SESSION_NATIVE NODE_MAIN_JS Z3DIR [LIST [JOBS]]

For the CLI's built-in samples (SB, MP, LB) and every litmus test in LIST
(default: wasm/test/litmus_subset.txt; "all" for every litmus-tests/**/*.lit),
JOBS at a time (default 1), compares

  verdict  the browser build's (the `valid` of its assertions answer, through
           wasm/node_run.js and node_main.bc.js with Z3 from Z3DIR) with
           `MORDOR run`'s ("Valid: ..."). A program that states no allow or
           forbid has no verdict on the stream, and the CLI says "true" of it:
           the two agree;
  answer   the browser build's whole assertions answer with the native
           session's (session_native.exe), byte for byte.

Prints one line per program, with the seconds each build took (the native
session's and the browser build's, wall clock, as information), and the
median ratio. Exits non-zero if any verdict or answer differs.
"""
import concurrent.futures
import glob
import json
import os
import re
import statistics
import subprocess
import sys
import time

# cli/main.ml's Examples, as `run --samples` runs them.
SAMPLES = {
    'Store Buffering': '\nname = SB\n%%\n{ x := 1 } ||| { y := 1 }\n%% allow (x = 0 && y = 0) []\n  ',
    'Message Passing': '\nname = MP\n%%\n{ x := 1; y := 1 } ||| { r1 := y; r2 := x }\n%% forbid (r1 = 1 && r2 = 0) []\n  ',
    'Load Buffering': '\nname = LB\n%%\n{ r1 := x; y := 1 } ||| { r2 := y; x := 1 }\n%% forbid (r1 = 1 && r2 = 1) []\n  ',
}
TIMEOUT = 3600


def timed(command, stdin=None):
    t = time.monotonic()
    r = subprocess.run(command, input=stdin, capture_output=True, text=True, timeout=TIMEOUT)
    return r.stdout, time.monotonic() - t


def cli_verdicts(output):
    """{program name: verdict} from `run` output: each "=== Running: NAME ==="
    block's "Valid: ..." line, or 'none' if it has none."""
    verdicts, name = {}, None
    for line in output.splitlines():
        m = re.match(r'=== Running: (.*) ===$', line)
        if m:
            name = m.group(1)
            verdicts[name] = 'none'
        m = re.match(r'Valid: (\S+)$', line)
        if m and name:
            verdicts[name] = m.group(1)
    return verdicts


def stream_verdict(answer):
    for frame in answer.split('\n\n'):
        if frame.startswith('data: '):
            try:
                message = json.loads(frame[len('data: '):])
            except ValueError:
                continue
            if isinstance(message, dict) and 'valid' in message:
                return 'true' if message['valid'] else 'false'
    return 'none'


def states_assertion(text):
    return re.search(r'\b(allow|forbid)\b', text.split('%%')[-1]) is not None


def main(mordor, session_native, node_main, z3dir, listing=None, jobs='1'):
    repo = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    if listing == 'all':
        tests = sorted(os.path.relpath(p, repo) for p in
                       glob.glob(os.path.join(repo, 'litmus-tests/**/*.lit'), recursive=True))
    else:
        listing = listing or os.path.join(repo, 'wasm/test/litmus_subset.txt')
        with open(listing) as f:
            tests = [line.strip() for line in f if line.strip() and not line.startswith('#')]
    node = ['node', os.path.join(repo, 'wasm/node_run.js'), z3dir, node_main, 'assertions']

    programs = []  # (name, program text, CLI verdict)
    expected = cli_verdicts(timed([mordor, 'run', '--samples'])[0])
    for name, text in SAMPLES.items():
        programs.append((name, text, expected.get(name, 'missing')))
    for test in tests:
        with open(os.path.join(repo, test)) as f:
            text = f.read()
        out, _ = timed([mordor, 'run', '--single', os.path.join(repo, test)])
        programs.append((test, text, cli_verdicts(out).get(os.path.basename(test), 'missing')))

    def check(program):
        name, text, cli = program
        body = json.dumps({'program': text})
        native, native_secs = timed([session_native, 'assertions'], body)
        browser, browser_secs = timed(node, body)
        verdict = stream_verdict(browser)
        problems = []
        if verdict != cli and not (verdict == 'none' and cli == 'true'
                                   and not states_assertion(text)):
            problems.append(f'verdict {verdict}, the CLI says {cli}')
        if browser != native:
            problems.append('answer differs from native')
        return name, verdict, native_secs, browser_secs, problems

    failures, ratios = [], []
    with concurrent.futures.ThreadPoolExecutor(int(jobs)) as pool:
        for name, verdict, native_secs, browser_secs, problems in pool.map(check, programs):
            ratios.append(browser_secs / max(native_secs, 1e-3))
            print(f'{name:60} {verdict:6} native {native_secs:7.2f}s browser {browser_secs:7.2f}s'
                  + ('  FAIL: ' + '; '.join(problems) if problems else ''), flush=True)
            failures += [f'{name}: {p}' for p in problems]
    print(f'{len(programs)} programs, {len(failures)} failures; '
          f'browser / native: median {statistics.median(ratios):.1f}x, '
          f'max {max(ratios):.1f}x')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main(*sys.argv[1:]))
