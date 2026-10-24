#!/usr/bin/env python3
"""W1 (#175): summarise a corpus made by generate.sh, in Markdown.

    python3 -I evaluation/w1_smt_corpus/analyze.py OUT

Queries are counted twice over: as asked (every line of every index.tsv) and as
distinct (one per digest, across all runs). The fragment is read off the
distinct queries' SMT-LIB: every operator that occurs, and which queries are
non-linear (a product of two non-constant terms, or a division or modulus by a
non-constant).
"""
import collections
import glob
import os
import re
import statistics
import sys

TOKEN = re.compile(r'\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()|"]+')


def parse(text):
    """The file's top-level s-expressions, as nested lists of tokens."""
    stack = [[]]
    for tok in TOKEN.findall(re.sub(r';[^\n]*', '', text)):
        if tok == '(':
            stack.append([])
        elif tok == ')':
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def numeral(t):
    return isinstance(t, str) and re.fullmatch(r'-?\d+', t) is not None or (
        isinstance(t, list) and len(t) == 2 and t[0] == '-' and numeral(t[1]))


def head(node):
    h = node[0]
    if isinstance(h, list):  # indexed, e.g. (_ int2bv 64)
        return ' '.join(x for x in h[:2] if isinstance(x, str))
    return h


def features(sexps):
    ops = collections.Counter()
    nonlinear = False

    def walk(node):
        nonlocal nonlinear
        if not isinstance(node, list) or not node:
            return
        h = head(node)
        if isinstance(h, str):
            ops[h] += 1
            args = node[1:]
            if h == '*' and sum(not numeral(a) for a in args) >= 2:
                nonlinear = True
            if h in ('div', 'mod') and len(args) == 2 and not numeral(args[1]):
                nonlinear = True
        for child in node[1:] if isinstance(node[0], str) else node:
            walk(child)

    asserts = 0
    decls = 0
    for s in sexps:
        if s and s[0] == 'assert':
            asserts += 1
            walk(s[1])
        elif s and s[0] in ('declare-fun', 'declare-const'):
            decls += 1
    return ops, nonlinear, asserts, decls


def pct(xs, p):
    if not xs:
        return 0.0
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(p / 100 * len(xs)))]


def main(out):
    asked = []  # (job, digest, site, answer, seconds)
    calls = collections.Counter()
    paths = {}
    for index in sorted(glob.glob(os.path.join(out, '*', 'index.tsv'))):
        job = os.path.basename(os.path.dirname(index))
        with open(index) as f:
            for line in f:
                digest, site, answer, seconds = line.rstrip('\n').split('\t')
                asked.append((job, digest, site, answer, float(seconds)))
                paths.setdefault(digest, os.path.join(out, job, digest + '.smt2'))
        callf = os.path.join(out, job, 'calls.tsv')
        if os.path.exists(callf):
            with open(callf) as f:
                for line in f:
                    what, site, n = line.rstrip('\n').split('\t')
                    calls[(what, site)] += int(n)

    jobs = {}
    with open(os.path.join(out, 'jobs.tsv')) as f:
        next(f)
        for line in f:
            job, cmd, lit, code, secs = line.rstrip('\n').split('\t')
            jobs[job] = (cmd, lit, int(code), float(secs))

    times = [a[4] for a in asked]
    print('# W1 corpus summary\n')
    failed = [j for j, v in jobs.items() if v[2] != 0]
    print(f'- runs: {len(jobs)}, of which {len(failed)} did not exit 0'
          + (f' ({", ".join(f"{jobs[j][1]} [{jobs[j][0]}]: {jobs[j][2]}" for j in failed)})'
             if failed else ''))
    print(f'- queries asked: {len(asked)}; distinct: {len(paths)}')
    print(f'- answers (asked): {dict(collections.Counter(a[3] for a in asked))}')
    if times:
        print(f'- seconds per query: median {statistics.median(times):.6f}, '
              f'p90 {pct(times, 90):.6f}, p99 {pct(times, 99):.6f}, '
              f'max {max(times):.6f}, total {sum(times):.1f}')

    print('\n## Callers\n\n| caller | asked | seconds | p90 |\n|---|--:|--:|--:|')
    by_site = collections.defaultdict(list)
    for a in asked:
        by_site[a[2]].append(a[4])
    for site, ts in sorted(by_site.items(), key=lambda kv: -sum(kv[1])):
        print(f'| `{site}` | {len(ts)} | {sum(ts):.2f} | {pct(ts, 90):.6f} |')

    print('\n## Runs with the most solver time\n\n| program | command | asked | seconds |\n|---|---|--:|--:|')
    by_job = collections.defaultdict(list)
    for a in asked:
        by_job[a[0]].append(a[4])
    for job, ts in sorted(by_job.items(), key=lambda kv: -sum(kv[1]))[:15]:
        cmd, lit = jobs[job][0], jobs[job][1]
        print(f'| {lit} | `{cmd}` | {len(ts)} | {sum(ts):.2f} |')

    weight = collections.Counter(a[1] for a in asked)
    ops_distinct = collections.Counter()
    ops_asked = collections.Counter()
    nonlinear = [0, 0]
    non_ascii = [0, 0]
    sizes = []
    for digest, path in paths.items():
        with open(path, encoding='utf-8') as f:
            text = f.read()
        ops, nl, asserts, decls = features(parse(text))
        sizes.append((asserts, decls))
        for op in ops:
            ops_distinct[op] += 1
            ops_asked[op] += weight[digest]
        if nl:
            nonlinear[0] += 1
            nonlinear[1] += weight[digest]
        if any(ord(c) > 127 for c in text):
            non_ascii[0] += 1
            non_ascii[1] += weight[digest]

    print('\n## Fragment\n')
    print(f'- non-linear: {nonlinear[0]} distinct, {nonlinear[1]} asked')
    print(f'- with non-ASCII symbols: {non_ascii[0]} distinct, {non_ascii[1]} asked')
    if sizes:
        print(f'- assertions per query: median {statistics.median(s[0] for s in sizes)}, '
              f'max {max(s[0] for s in sizes)}; '
              f'declared symbols: median {statistics.median(s[1] for s in sizes)}, '
              f'max {max(s[1] for s in sizes)}')
    print('\n| operator | distinct queries | asked |\n|---|--:|--:|')
    for op, n in ops_distinct.most_common():
        print(f'| `{op}` | {n} | {ops_asked[op]} |')

    print('\n## Scope pushes and model evaluations\n\n| | caller | calls |\n|---|---|--:|')
    for (what, site), n in sorted(calls.items(), key=lambda kv: (kv[0][0], -kv[1])):
        print(f'| {what} | `{site}` | {n} |')


if __name__ == '__main__':
    main(sys.argv[1])
