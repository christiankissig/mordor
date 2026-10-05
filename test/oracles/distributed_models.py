#!/usr/bin/env python3
"""An oracle for MoRDor's distributed consistency models.

MoRDor reads the Steinke--Nutt lattice, per-object causal consistency and the
session guarantees as predicates on its own candidate executions: a read reads
a write through ``rf``, initialising stores are writes ordered before every
thread, and the models are decided by searching for views (``Coherence.Views``)
or arbitration orders (``Coherence.Sessions``, ``Coherence.POCausal``).

This oracle decides the same models from their definitions over *histories*,
independently of MoRDor's executions: a history is each process's sequence of
operations with the values they read and wrote, initial values are a pre-state
rather than writes, and a read is matched to a write by its value. It answers,
for a straight-line litmus program and an outcome (one value per register),
which models allow the outcome.

- Local, Slow, PRAM, Causal, PC: Steinke and Nutt (JPDC 2004). Each process has
  a view, a legal serialisation of every write and its own operations, which
  respects its own program order and: nothing more (Local); each process's
  writes to a location in program order (Slow); each process's writes in
  program order (PRAM); the causal order, program order with writes-into,
  transitively closed (Causal); PRAM's order, with one order of each
  location's writes common to every view (PC).
- POCausal: Burckhardt et al. (POPL 2014) over a visibility and a per-object
  arbitration: hbo = ((so & ob) | vis)+ is acyclic and per object included in
  visibility (POCV) and arbitration (POCA), and a read returns the
  arbitration-latest visible write.
- RYW, MR, MW, WFR: Terry et al. (PDIS 1994) in Viotti and Vukolic's form,
  with one arbitration order per reader, as MoRDor reads them (see the comment
  on Coherence.Sessions for why).

Usage: distributed_models.py FILE.lit...   prints, for each file and each of
these models its assertions name, the oracle's verdict beside the asserted
one, and exits non-zero on any disagreement.
"""

import itertools
import re
import sys

MODELS = ["local", "slow", "pram", "causal", "pc", "pocausal", "ryw", "mr", "mw", "wfr"]


# ---------------------------------------------------------------------------
# Programs and histories

class Op:
    def __init__(self, proc, idx, kind, loc, val=None, reg=None):
        self.proc, self.idx, self.kind, self.loc, self.val, self.reg = proc, idx, kind, loc, val, reg

    def __repr__(self):
        v = self.val if self.kind == "w" else self.reg
        return f"{self.kind}{self.proc}.{self.idx}({self.loc},{v})"


def parse_program(text):
    """Initial values and per-process operations of a straight-line program."""
    text = re.sub(r"//[^\n]*", "", text)
    code = text.split("%%")[0]
    init, _, rest = code.partition("{")
    initial = {m.group(1): int(m.group(2)) for m in re.finditer(r"(\w+)\s*:=\s*(-?\d+)\s*;", init)}
    threads = [t.strip().strip("{}").strip() for t in ("{" + rest).split("|||")]
    procs = []
    for p, body in enumerate(threads):
        ops = []
        for stmt in [s.strip() for s in body.replace("}", "").replace("{", "").split(";") if s.strip()]:
            lhs, rhs = [x.strip() for x in stmt.split(":=")]
            if re.fullmatch(r"r\w*", lhs):
                ops.append(Op(p, len(ops), "r", rhs, reg=lhs))
            else:
                ops.append(Op(p, len(ops), "w", lhs, val=int(rhs)))
        procs.append(ops)
    return initial, procs


def parse_assertions(text):
    """(outcome, {model: allowed}) for each condition the file asserts."""
    tail = text.split("%%", 1)[1]
    tail = re.sub(r"\s+", " ", tail)
    found = {}
    for kw, cond, models in re.findall(r"(allow|forbid) \(([^)]*)\) \[([^\]]*)\]", tail):
        outcome = tuple(sorted((r.strip(), int(v)) for r, v in (c.split("=") for c in cond.split("&&"))))
        verdicts = found.setdefault(outcome, {})
        for m in models.split(","):
            verdicts[m.strip().lower()] = kw == "allow"
    return found


# ---------------------------------------------------------------------------
# Search helpers

def linearisations(nodes, before):
    """Linear orders of nodes in which a precedes b whenever (a, b) in before."""
    nodes = list(nodes)
    if not nodes:
        yield []
        return
    for i, x in enumerate(nodes):
        if any((y, x) in before for y in nodes if y is not x):
            continue
        rest = nodes[:i] + nodes[i + 1:]
        for tail in linearisations(rest, before):
            yield [x] + tail


def closure(pairs):
    pairs = set(pairs)
    while True:
        new = {(a, d) for (a, b) in pairs for (c, d) in pairs if b == c} - pairs
        if not new:
            return pairs
        pairs |= new


# ---------------------------------------------------------------------------
# Steinke--Nutt views

def view_ok(initial, view, outcome):
    latest = dict(initial)
    for op in view:
        if op.kind == "w":
            latest[op.loc] = op.val
        elif latest.get(op.loc) != outcome[op.reg]:
            return False
    return True


def views_allow(model, initial, procs, outcome):
    writes = [op for ops in procs for op in ops if op.kind == "w"]
    po = {(a, b) for ops in procs for i, a in enumerate(ops) for b in ops[i + 1:]}
    if model == "local":
        shared = set()
    elif model == "slow":
        shared = {(a, b) for (a, b) in po if a.kind == b.kind == "w" and a.loc == b.loc}
    elif model in ("pram", "pc"):
        shared = {(a, b) for (a, b) in po if a.kind == b.kind == "w"}
    elif model == "causal":
        # writes-into by value: a read of v at x follows every write of v to x
        into = {(w, r) for ops in procs for r in ops if r.kind == "r" for w in writes
                if w.loc == r.loc and w.val == outcome[r.reg]}
        shared = closure(po | into)
    def view_exists(p, extra):
        own = procs[p]
        nodes = writes + [op for op in own if op.kind == "r"]
        before = {(a, b) for (a, b) in po if a.proc == b.proc == p} | shared | extra
        return any(view_ok(initial, v, outcome) for v in linearisations(nodes, before))
    if model != "pc":
        return all(view_exists(p, set()) for p in range(len(procs)))
    # PC: one order of each location's writes, common to every view
    locs = sorted({w.loc for w in writes})
    per_loc = [list(linearisations([w for w in writes if w.loc == l], shared)) for l in locs]
    for choice in itertools.product(*per_loc):
        common = {(a, b) for order in choice for i, a in enumerate(order) for b in order[i + 1:]}
        if all(view_exists(p, common) for p in range(len(procs))):
            return True
    return False


# ---------------------------------------------------------------------------
# Visibility and arbitration: POCausal and the session guarantees

def sources(initial, procs, outcome):
    """Each read's possible source: a write of the value it read, or None for
    the initial value."""
    writes = [op for ops in procs for op in ops if op.kind == "w"]
    reads = [op for ops in procs for op in ops if op.kind == "r"]
    options = []
    for r in reads:
        v = outcome[r.reg]
        opts = [w for w in writes if w.loc == r.loc and w.val == v]
        if initial.get(r.loc) == v:
            opts.append(None)
        options.append(opts)
    for choice in itertools.product(*options):
        yield dict(zip(reads, choice))


def rval_ok(read, src, visible, ar):
    """The read returns the arbitration-latest visible write to its location,
    or the initial value when it sees none."""
    seen = [w for w in visible if w.loc == read.loc]
    if src is None:
        return not seen
    if src not in seen:
        return False
    return all(w is src or ar.index(w) < ar.index(src) for w in seen)


def sessions_allow(model, initial, procs, outcome):
    writes = [op for ops in procs for op in ops if op.kind == "w"]
    so = {(a, b) for ops in procs for i, a in enumerate(ops) for b in ops[i + 1:]}
    for src in sources(initial, procs, outcome):
        # least visibility the guarantee demands
        vis = {(w, r) for r, w in src.items() if w is not None}
        if model == "ryw":
            vis |= {(a, b) for (a, b) in so if a.kind == "w" and b.kind == "r"}
        if model == "mr":
            vis |= {(w, r2) for (w, r1) in vis for (a, r2) in so if a is r1 and r2.kind == "r"}
        arb = set()
        if model == "mw":
            arb |= {(a, b) for (a, b) in so if a.kind == b.kind == "w"}
        if model == "wfr":
            arb |= {(w, w2) for (w, r) in vis for (a, w2) in so if a is r and w2.kind == "w"}
        ok = True
        for p, ops in enumerate(procs):
            reads = [op for op in ops if op.kind == "r"]
            if not reads:
                continue
            if not any(all(rval_ok(r, src[r], [w for (w, rr) in vis if rr is r], ar) for r in reads)
                       for ar in linearisations(writes, arb)):
                ok = False
                break
        if ok:
            return True
    return False


def pocausal_allows(initial, procs, outcome):
    writes = [op for ops in procs for op in ops if op.kind == "w"]
    so = {(a, b) for ops in procs for i, a in enumerate(ops) for b in ops[i + 1:]}
    so_ob = {(a, b) for (a, b) in so if a.loc == b.loc}
    locs = sorted({w.loc for w in writes})
    for src in sources(initial, procs, outcome):
        vis = {(w, r) for r, w in src.items() if w is not None}
        # POCV: close visibility under hbo, per object
        while True:
            hbo = closure(so_ob | vis)
            more = {(a, b) for (a, b) in hbo if a.kind == "w" and b.kind == "r" and a.loc == b.loc} - vis
            if not more:
                break
            vis |= more
        if any(a is b for (a, b) in hbo):
            continue
        # POCA: one arbitration per object, including hbo between its writes
        arb_edges = {(a, b) for (a, b) in hbo if a.kind == b.kind == "w"}
        per_loc = [list(linearisations([w for w in writes if w.loc == l], arb_edges)) for l in locs]
        for choice in itertools.product(*per_loc):
            ar = [w for order in choice for w in order]
            if all(rval_ok(r, s, [w for (w, rr) in vis if rr is r], ar) for r, s in src.items()):
                return True
    return False


def allows(model, initial, procs, outcome):
    if model in ("local", "slow", "pram", "causal", "pc"):
        return views_allow(model, initial, procs, outcome)
    if model == "pocausal":
        return pocausal_allows(initial, procs, outcome)
    return sessions_allow(model, initial, procs, outcome)


def main(paths):
    bad = 0
    for path in paths:
        text = open(path).read()
        initial, procs = parse_program(text)
        for outcome, verdicts in parse_assertions(text).items():
            out = dict(outcome)
            for model in MODELS:
                if model not in verdicts:
                    continue
                mine = allows(model, initial, procs, out)
                agree = mine == verdicts[model]
                bad += not agree
                print(f"{'ok ' if agree else 'BAD'} {path}: {model:9} asserted "
                      f"{'allow ' if verdicts[model] else 'forbid'} oracle {'allow' if mine else 'forbid'}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv[1:])
