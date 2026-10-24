#!/usr/bin/env python3
"""W1 (#175): re-check every distinct query of a corpus with standalone z3.

    python3 -I evaluation/w1_smt_corpus/recheck.py OUT [WORKERS] [SECONDS]

Each distinct query is solved from its .smt2 file alone, and the answer
compared with every answer MoRDor's Z3 gave it. A disagreement is sat against
unsat; an unknown or a timeout on either side is counted, not compared. Exits
non-zero if any query disagrees, or if any file is not a query z3 can solve on
its own.
"""
import collections
import concurrent.futures
import glob
import os
import subprocess
import sys


def solve(path, seconds):
    try:
        r = subprocess.run(['z3', f'-T:{seconds}', path], capture_output=True,
                           text=True, timeout=seconds + 10)
        answer = r.stdout.strip().splitlines()[:1]
        return answer[0] if answer else 'error: ' + r.stderr.strip()[:200]
    except subprocess.TimeoutExpired:
        return 'timeout'


def main(out, workers=4, seconds=60):
    answers = collections.defaultdict(set)
    paths = {}
    for index in glob.glob(os.path.join(out, '*', 'index.tsv')):
        job = os.path.dirname(index)
        with open(index) as f:
            for line in f:
                digest, _, answer, _ = line.rstrip('\n').split('\t')
                answers[digest].add(answer)
                paths.setdefault(digest, os.path.join(job, digest + '.smt2'))

    with concurrent.futures.ThreadPoolExecutor(workers) as pool:
        standalone = dict(zip(paths, pool.map(lambda d: solve(paths[d], seconds), paths)))

    version = subprocess.run(['z3', '--version'], capture_output=True, text=True).stdout.strip()
    disagree = [d for d, a in standalone.items()
                if a in ('sat', 'unsat') and ({'sat', 'unsat'} - {a}) & answers[d]]
    inconsistent = [d for d, a in answers.items() if {'sat', 'unsat'} <= a]
    print(f'standalone: {version}')
    print(f'distinct queries: {len(paths)}')
    print(f'standalone answers: {dict(collections.Counter(standalone.values()))}')
    print(f"MoRDor's answers unknown for {sum('unknown' in a for a in answers.values())} distinct queries")
    print(f'disagreements (sat vs unsat): {len(disagree)}')
    for d in disagree:
        print(f'  {paths[d]}: standalone {standalone[d]}, in MoRDor {sorted(answers[d])}')
    print(f'queries MoRDor answered both sat and unsat: {len(inconsistent)}')
    # A file that z3 cannot solve on its own is not a standalone query.
    unsolved = [d for d, a in standalone.items()
                if a not in ('sat', 'unsat', 'unknown', 'timeout')]
    print(f'files z3 could not solve on their own: {len(unsolved)}')
    for d in unsolved[:10]:
        print(f'  {paths[d]}: {standalone[d]}')
    return 1 if disagree or inconsistent or unsolved else 0


if __name__ == '__main__':
    args = sys.argv[1:]
    sys.exit(main(args[0], *(int(a) for a in args[1:])))
