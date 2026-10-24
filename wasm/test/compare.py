#!/usr/bin/env python3
"""The browser build's answers against the native platform's (W3, #179; W4, #180).

    python3 -I wasm/test/compare.py SESSION_NATIVE NODE_MAIN_JS Z3DIR [DIST]

Every pipeline is asked about every program below, natively (Z3 through its
OCaml bindings, through session_native.exe) and under node (the browser
platform, Z3 compiled to wasm from Z3DIR, through wasm/node_run.js and
node_main.bc.js); both print the answer as the server's SSE stream frames it,
and the two must be identical byte for byte. With DIST (wasm/dist.sh's
directory), the Web Worker is driven through worker_test.mjs and must post
exactly what node_main prints, for parse and interpret.

First, hashes_native.exe (next to SESSION_NATIVE) and test/hashes.bc.js (next
to NODE_MAIN_JS) must print the same report: MoRDor's hashes, and the orders
they put sets in, must not depend on the width of int (#193).

Exits non-zero on any difference.
"""
import json
import os
import subprocess
import sys

PROGRAMS = [
    'litmus-tests/test6/MP.lit',
    'litmus-tests/test6/LB.lit',
    'litmus-tests/test6/3.SB.lit',
    'litmus-tests/test6/IRIW.lit',
    'litmus-tests/test6/CoRR1.lit',
    'programs/seqlock-1.lit',
    'programs/uaf-bug.lit',
]
PIPELINES = ['parse', 'interpret', 'episodicity', 'assertions', 'visualize']


def answer(command, pipeline, body):
    r = subprocess.run(command + [pipeline], input=json.dumps(body),
                       capture_output=True, text=True, timeout=600)
    return r.stdout


def hashes(session_native, node_main):
    native = subprocess.run([os.path.join(os.path.dirname(session_native), 'hashes_native.exe')],
                            capture_output=True, text=True, check=True).stdout
    browser = subprocess.run(['node', os.path.join(os.path.dirname(node_main), 'test', 'hashes.bc.js')],
                             capture_output=True, text=True, check=True).stdout
    differ = [n.split(':')[0] for n, b in zip(native.splitlines(), browser.splitlines()) if n != b]
    if native.count('\n') != browser.count('\n'):
        differ.append('the number of lines')
    print('hashes: ' + ('identical' if not differ else 'differ in ' + ', '.join(differ)))
    return [f'hashes: {d}' for d in differ]


def main(session_native, node_main, z3dir, dist=None):
    repo = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    node = ['node', os.path.join(repo, 'wasm/node_run.js'), z3dir, node_main]
    failures = hashes(session_native, node_main)
    for program in PROGRAMS:
        with open(os.path.join(repo, program)) as f:
            body = {'program': f.read()}
        row = []
        for pipeline in PIPELINES:
            native = answer([session_native], pipeline, body)
            browser = answer(node, pipeline, body)
            verdict = 'identical' if native == browser else 'DIFFER'
            if native != browser:
                failures.append(f'{pipeline} {program}: differs from native')
            if dist and pipeline in ('parse', 'interpret'):
                posted = answer(['node', os.path.join(repo, 'wasm/test/worker_test.mjs'), dist],
                                pipeline, body)
                if posted != browser:
                    failures.append(f'{pipeline} {program}: the worker posts something else')
            row.append(f'{pipeline} {verdict}')
        print(f'{program:30} ' + ', '.join(row))
    for f in failures:
        print('FAIL', f)
    print('ok' if not failures else f'{len(failures)} failures')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main(*sys.argv[1:]))
