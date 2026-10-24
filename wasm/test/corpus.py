#!/usr/bin/env python3
"""The W1 corpus (#175) through the browser build's Z3, against native Z3 (W4, #180).

    python3 -I wasm/test/corpus.py CORPUS Z3DIR CORPUS_RUN_JS OUT_DIR [JOBS]

CORPUS is evaluation/w1_smt_corpus/generate.sh's output: one directory per
run, each with index.tsv (digest, caller, answer, seconds) and <digest>.smt2.
Every distinct query is solved once by Z3 compiled to wasm (corpus_run.bc.js,
under wasm/node_run.js, in JOBS processes, default 3) and its answer compared
with the answers MoRDor's native Z3 gave it. A disagreement is sat against
unsat; unknowns and errors are counted apart. Writes OUT_DIR/answers.tsv and
prints a summary; exits non-zero on any disagreement, unknown or error.
"""
import collections
import glob
import os
import statistics
import subprocess
import sys


def main(corpus, z3dir, corpus_run, out_dir, jobs='3'):
    repo = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    native = collections.defaultdict(set)
    seconds = collections.defaultdict(list)
    paths = {}
    for index in sorted(glob.glob(os.path.join(corpus, '*', 'index.tsv'))):
        with open(index) as f:
            for line in f:
                digest, _caller, answer, secs = line.rstrip('\n').split('\t')
                native[digest].add(answer)
                seconds[digest].append(float(secs))
                paths.setdefault(digest, os.path.join(os.path.dirname(index), digest + '.smt2'))
    digests = sorted(paths)
    os.makedirs(out_dir, exist_ok=True)
    jobs = int(jobs)
    procs = []
    for j in range(jobs):
        listing = os.path.join(out_dir, f'list.{j}')
        with open(listing, 'w') as f:
            f.writelines(paths[d] + '\n' for d in digests[j::jobs])
        procs.append(subprocess.Popen(
            ['node', '--max-old-space-size=2048', os.path.join(repo, 'wasm/node_run.js'),
             z3dir, corpus_run, listing, os.path.join(out_dir, f'answers.{j}')]))
    if any(p.wait() for p in procs):
        sys.exit('corpus_run failed')

    digest_of = {p: d for d, p in paths.items()}
    counts = collections.Counter()
    ratios, problems = [], []
    with open(os.path.join(out_dir, 'answers.tsv'), 'w') as out:
        for j in range(jobs):
            with open(os.path.join(out_dir, f'answers.{j}')) as f:
                for line in f:
                    out.write(line)
                    path, answer, secs = line.rstrip('\n').split('\t')
                    d = digest_of[path]
                    if answer in native[d]:
                        counts['agree'] += 1
                        ratios.append(float(secs) / max(statistics.median(seconds[d]), 1e-6))
                    elif answer in ('sat', 'unsat'):
                        counts['disagree'] += 1
                        problems.append(f'{path}: {answer}, native {sorted(native[d])}')
                    else:
                        counts[answer.split(':')[0]] += 1
                        problems.append(f'{path}: {answer}')
    answered = sum(counts.values())
    for p in problems[:20]:
        print(p)
    print(f'distinct queries: {len(digests)}, answered: {answered}, {dict(counts)}')
    if ratios:
        print(f'check seconds, wasm / native (in MoRDor): median {statistics.median(ratios):.2f}')
    return 1 if problems or answered != len(digests) else 0


if __name__ == '__main__':
    sys.exit(main(*sys.argv[1:]))
