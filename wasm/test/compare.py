#!/usr/bin/env python3
"""W3 (#179): the browser build's answers against the native platform's.

    python3 -I wasm/test/compare.py SESSION_NATIVE NODE_MAIN_JS [WORKER_JS]

Every pipeline is asked about every program below, natively (Z3, through
session_native.exe) and under node (the browser platform, through
node_main.bc.js); both print the answer as the server's SSE stream frames it.
Each pair is

  identical  byte for byte;
  stopped    the browser build's answer is the native one's up to a message,
             and then the error saying it has no SMT solver;
  FAIL       anything else.

It exits non-zero on any FAIL, or if a pair the browser build must answer in
full is not identical: parse for every program, interpret for the programs
whose conditions are decided without a solver. With WORKER_JS, the Web Worker
is driven through worker_test.mjs and must post exactly what node_main prints.

First, hashes_native.exe (next to SESSION_NATIVE) and test/hashes.bc.js (next
to NODE_MAIN_JS) must print the same report: MoRDor's hashes, and the orders
they put sets in, must not depend on the width of int (#193).
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
# Interpreted without a solver: no condition the interpreter must ask about.
BRANCH_FREE = PROGRAMS[:5]
PIPELINES = ['parse', 'interpret', 'episodicity', 'assertions', 'visualize']
NO_SOLVER = 'This build of MoRDor has no SMT solver yet'


def answer(command, pipeline, body):
    r = subprocess.run(command + [pipeline], input=json.dumps(body),
                       capture_output=True, text=True, timeout=600)
    return r.stdout


def classify(native, browser):
    if native == browser:
        return 'identical'
    messages = [m for m in browser.split('\n\n') if m]
    before = ''.join(m + '\n\n' for m in messages[:-1])
    if messages and NO_SOLVER in messages[-1] and native.startswith(before):
        return 'stopped'
    return 'FAIL'


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


def main(session_native, node_main, worker=None):
    repo = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    failures = hashes(session_native, node_main)
    for program in PROGRAMS:
        with open(os.path.join(repo, program)) as f:
            body = {'program': f.read()}
        row = []
        for pipeline in PIPELINES:
            native = answer([session_native], pipeline, body)
            browser = answer(['node', node_main], pipeline, body)
            verdict = classify(native, browser)
            must = pipeline == 'parse' or (pipeline == 'interpret' and program in BRANCH_FREE)
            if verdict == 'FAIL' or (must and verdict != 'identical'):
                failures.append(f'{pipeline} {program}: {verdict}')
            if worker and pipeline in ('parse', 'interpret'):
                posted = answer(['node', os.path.join(repo, 'wasm/test/worker_test.mjs'), worker],
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
