#!/usr/bin/env python3
"""S18: compare region decompositions of dumped read-from search spaces.

Input: JSON lines from MORDOR_S18_DUMP, one per justification combination:
{"events": [{"l", "t", "typ", "vol", "loc", "wval", "li", "elided", ...}],
 "po": [[a, b], ...], "alts": {"r": [w, ...]}}

For each decomposition (a region per event), per combination:
  - share of each read's candidate writes inside its own region;
  - crossing candidate edges;
  - per region: reads with a candidate outside (open reads), and writes that
    are candidates of reads outside (exported writes);
  - log10 of the choice product, and the part a merge would have to resolve:
    per read, its outside choices plus one for "some inside write" if any;
  - recurrence: regions with the same shape (types, locations, values in
    order), i.e. anything a bottom-up construction could reuse.
"""
import json
import math
import statistics
import sys
from collections import defaultdict


def load(path):
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                yield json.loads(line)


def thread_of(ev):
    t = ev.get("t")
    return "init" if t is None else t


def order_in_thread(combo):
    """Events of each thread in program order (a path is a chain per thread)."""
    evs = {e["l"]: e for e in combo["events"]}
    before = defaultdict(set)
    for a, b in combo["po"]:
        before[b].add(a)
    by_thread = defaultdict(list)
    for l, e in evs.items():
        by_thread[thread_of(e)].append(l)
    for t in by_thread:
        by_thread[t].sort(key=lambda l: (len(before[l]), l))
    return evs, by_thread


def split_at(combo, is_cut):
    """Region = (thread, number of cut events strictly before in the thread)."""
    evs, by_thread = order_in_thread(combo)
    region = {}
    for t, ls in by_thread.items():
        k = 0
        for l in ls:
            region[l] = (t, k)
            if is_cut(evs[l]):
                k += 1
    return region


def decompositions(combo):
    evs, _ = order_in_thread(combo)
    d = {}
    d["thread"] = {l: (thread_of(e),) for l, e in evs.items()}
    # Paths carry no branch events (conditions live in restrict), so a
    # straight-line segment is cut where the loop indices change.
    evs_, by_thread = order_in_thread(combo)
    seg = {}
    for t, ls in by_thread.items():
        k, prev = 0, None
        for l in ls:
            li = tuple(evs_[l]["li"])
            if prev is not None and li != prev:
                k += 1
            seg[l] = (t, k)
            prev = li
    d["segment"] = seg
    d["rcu-section"] = split_at(combo, lambda e: e["vol"])
    if any(e["li"] for e in evs.values()):
        d["loop-iteration"] = {
            l: (thread_of(e), tuple(e["li"])) for l, e in evs.items()
        }
    d["event"] = {l: (l,) for l in evs}  # finest possible: every choice crosses
    return d


def shape(evs, members):
    return tuple(
        (evs[l]["typ"], evs[l]["loc"], evs[l]["wval"], evs[l]["vol"])
        for l in sorted(members)
    )


def measure(combo, region):
    evs = {e["l"]: e for e in combo["events"]}
    alts = {int(r): ws for r, ws in combo["alts"].items()}
    inside_share, total_log, merge_log = [], 0.0, 0.0
    edges_in = edges_out = 0
    open_reads = defaultdict(int)
    exported = defaultdict(set)
    for r, ws in alts.items():
        if not ws:
            continue
        rr = region.get(r)
        inside = [w for w in ws if w != 0 and region.get(w) == rr]
        outside = [w for w in ws if w not in inside]
        inside_share.append(len(inside) / len(ws))
        edges_in += len(inside)
        edges_out += len(outside)
        total_log += math.log10(len(ws))
        # The merge chooses among the outside writes, plus one option standing
        # for "an inside write", resolved within the region, if there is one.
        merge_log += math.log10(len(outside) + (1 if inside else 0)) if outside else 0.0
        if outside:
            open_reads[rr] += 1
        for w in outside:
            if w != 0:
                exported[region.get(w)].add(w)
    members = defaultdict(list)
    for l, reg in region.items():
        members[reg].append(l)
    regions = len(members)
    shapes = len({shape(evs, m) for m in members.values()})
    return {
        "inside_share": statistics.mean(inside_share) if inside_share else 1.0,
        "cross_edges": edges_out / max(1, edges_in + edges_out),
        "open_reads_per_region": sum(open_reads.values()) / regions,
        "exported_per_region": sum(len(v) for v in exported.values()) / regions,
        "log_total": total_log,
        "log_merge": merge_log,
        "regions": regions,
        "distinct_shapes": shapes,
    }


def main(paths):
    for path in paths:
        rows = defaultdict(list)
        n = 0
        for combo in load(path):
            n += 1
            for name, region in decompositions(combo).items():
                rows[name].append(measure(combo, region))
        print(f"== {path}: {n} combinations")
        print(
            f"  {'decomposition':16s} {'inside':>7s} {'crossing':>9s} "
            f"{'open/reg':>9s} {'export/reg':>10s} {'log10 all':>10s} "
            f"{'log10 merge':>12s} {'regions':>8s} {'shapes':>7s}"
        )
        for name, ms in rows.items():
            med = lambda k: statistics.median(m[k] for m in ms)
            print(
                f"  {name:16s} {med('inside_share'):7.2f} {med('cross_edges'):9.2f} "
                f"{med('open_reads_per_region'):9.2f} {med('exported_per_region'):10.2f} "
                f"{med('log_total'):10.2f} {med('log_merge'):12.2f} "
                f"{med('regions'):8.0f} {med('distinct_shapes'):7.0f}"
            )


if __name__ == "__main__":
    main(sys.argv[1:])
