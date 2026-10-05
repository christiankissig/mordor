#!/usr/bin/env python3
"""Compare MoRDor's distributed consistency models with the oracle on random
programs.

Generates straight-line programs of two or three threads over x and y, each
store writing a value not written before at its location, and asks, for every
outcome, both MoRDor (one run, all ten models) and the oracle in
distributed_models.py whether each model allows it.

MoRDor can only be stricter than the definitions where its candidate
executions cannot express an outcome. Three such limits are known, and each
disagreement is attributed to one:

- own-future-read: a read takes a value only a later store of its own thread
  writes;
- skips-own-store: a read does not see its own thread's latest earlier store
  to the location;
- same-location load buffering: reads and stores to one location form a cycle
  through program order and reads-from (sMRD's ppo orders same-location
  accesses).

Any other disagreement, and any outcome MoRDor allows that the oracle forbids,
is reported as unexplained and fails the run.

Usage: compare_with_mordor.py SEED COUNT SCRATCH_DIR   (run from the
repository root, after dune build)
"""

import collections
import itertools
import os
import random
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import distributed_models as O  # noqa: E402

NAMES = {"local": "Local", "slow": "Slow", "pram": "PRAM", "causal": "Causal", "pc": "PC",
         "pocausal": "POCausal", "ryw": "RYW", "mr": "MR", "mw": "MW", "wfr": "WFR"}


def program(rng):
    nextval = {"x": 1, "y": 1}
    reg = 0
    threads = []
    for _ in range(rng.choice([2, 2, 3])):
        ops = []
        for _ in range(rng.choice([1, 2, 2, 3])):
            loc = rng.choice("xy")
            if rng.random() < 0.5:
                ops.append(f"{loc} := {nextval[loc]}")
                nextval[loc] += 1
            else:
                ops.append(f"r{reg} := {loc}")
                reg += 1
        threads.append(ops)
    body = "x := 0;\ny := 0;\n" + " ||| ".join("{\n  " + ";\n  ".join(t) + "\n}" for t in threads)
    return body, reg, nextval


def limits(initial, procs, outcome):
    """The known generator limits an outcome runs into."""
    found = set()
    for ops in procs:
        for i, r in enumerate(ops):
            if r.kind != "r":
                continue
            v = outcome[r.reg]
            srcs = [w for o in procs for w in o if w.kind == "w" and w.loc == r.loc and w.val == v]
            if v != initial.get(r.loc) and srcs and all(w.proc == r.proc and w.idx > i for w in srcs):
                found.add("own-future-read")
            earlier = [w for w in ops[:i] if w.kind == "w" and w.loc == r.loc]
            if earlier and earlier[-1].val != v:
                found.add("skips-own-store")
    # same-location load buffering: rf (by value) and same-location po cycle
    nodes = [op for ops in procs for op in ops]
    edges = {(a, b) for ops in procs for i, a in enumerate(ops) for b in ops[i + 1:] if a.loc == b.loc}
    for r in nodes:
        if r.kind == "r":
            for w in nodes:
                if w.kind == "w" and w.loc == r.loc and w.val == outcome[r.reg]:
                    edges.add((w, r))
    if any(a is b for (a, b) in O.closure(edges)):
        found.add("same-location load buffering")
    return found


def main(seed, count, scratch):
    rng = random.Random(seed)
    tally = collections.Counter()
    checked = unexplained = 0
    for k in range(count):
        body, nregs, nextval = program(rng)
        if nregs == 0 or nregs > 4:
            continue
        initial, procs = O.parse_program(body + "\n%%\n")
        reads = [op for ops in procs for op in ops if op.kind == "r"]
        for combo in itertools.product(*[[0] + list(range(1, nextval[r.loc])) for r in reads]):
            outcome = {r.reg: v for r, v in zip(reads, combo)}
            cond = " && ".join(f"{r} = {v}" for r, v in sorted(outcome.items()))
            path = os.path.join(scratch, f"p{k}.lit")
            with open(path, "w") as f:
                f.write(body + f"\n%%\nallow ({cond}) [" + ", ".join(NAMES.values()) + "]\n")
            out = subprocess.run(["./_build/default/cli/main.exe", "run", "--single", path],
                                 capture_output=True, text=True).stdout
            mordor = {m.group(2): m.group(1) == "holds"
                      for m in (re.match(r"\s*(holds|FAILS): allow .* \[([\w-]+)\]", l) for l in out.splitlines()) if m}
            for model in O.MODELS:
                checked += 1
                mine, theirs = O.allows(model, initial, procs, outcome), mordor.get(model)
                if mine == theirs:
                    continue
                why = limits(initial, procs, outcome) if (mine, theirs) == (True, False) else set()
                if why:
                    tally[(model, ",".join(sorted(why)))] += 1
                else:
                    unexplained += 1
                    print(f"UNEXPLAINED {model}: oracle {mine} mordor {theirs} outcome {outcome}\n{body}\n")
    for (model, why), n in sorted(tally.items()):
        print(f"{n:5} {model:9} {why}")
    print(f"checked {checked} verdicts; {sum(tally.values())} explained by generator limits, "
          f"{unexplained} unexplained")
    sys.exit(1 if unexplained else 0)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
