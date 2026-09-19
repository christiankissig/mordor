#!/usr/bin/env python3
"""Summarise the [S10] and [S4] lines of one run's stderr.

    analyze_s10.py RUN.err
"""
import re
import statistics
import sys
from collections import Counter, defaultdict

lines = open(sys.argv[1], encoding="utf-8", errors="replace").read().splitlines()

alts, keys, sampled, coh, s4 = [], defaultdict(list), [], [], {}
for line in lines:
    if m := re.match(r"S10 alts reads=(\d+) log10=([\d.]+) local_log10=([\d.]+) \[(.*)\]", line):
        reads = []
        for item in m[4].split():
            r, rest = item.split("@")
            t, counts = rest.split(":")
            s, o, x = map(int, counts.split("/"))
            reads.append((int(r), t, s, o, x))
        alts.append((int(m[1]), float(m[2]), float(m[3]), reads))
    elif m := re.match(r"S10 key thread=(\d+) alts=(\w+) alts\+p=(\w+)", line):
        keys[int(m[1])].append((m[2], m[3]))
    elif m := re.match(r"S10 sampled distinct=(\d+) of (\d+) tries, (\d+) complete, (\d+) over budget", line):
        sampled.append(tuple(map(int, m.groups())))
    elif m := re.match(r"S10 coherence id=(\d+) events=(\d+) rf=(\d+) admitted=(\w+) ms=(\d+)", line):
        coh.append((int(m[2]), int(m[3]), m[4] == "true", int(m[5])))
    elif m := re.search(r"\[S4\] (.*): (\d+)$", line):
        s4[m[1]] = int(m[2])
    elif m := re.match(r"S10 combos=(\d+) frozen=(\d+)", line):
        s4["S10 combos"], s4["S10 frozen"] = int(m[1]), int(m[2])


def pct(a, b):
    return f"{100 * a / b:.1f}%" if b else "-"


print("## Pipeline counts\n")
for k, v in s4.items():
    print(f"- {k}: {v}")

print("\n## Read-from alternatives per combination\n")
if alts:
    whole = [a[1] for a in alts]
    local = [a[2] for a in alts]
    print(f"- combinations: {len(alts)}; reads per combination: "
          f"{min(a[0] for a in alts)}-{max(a[0] for a in alts)}")
    print(f"- log10 of the product: median {statistics.median(whole):.1f}, "
          f"max {max(whole):.1f}")
    print(f"- log10 of the product over same-thread and outside writes only: "
          f"median {statistics.median(local):.1f}, max {max(local):.1f}")
    tot = Counter()
    per_read = defaultdict(lambda: Counter())
    for _, _, _, reads in alts:
        for r, t, s, o, x in reads:
            tot.update(same=s, other=o, outside=x)
            per_read[(r, t)].update(n=1, same=s, other=o, outside=x)
    n = sum(tot.values())
    print(f"- alternatives, summed over reads and combinations: {n}; "
          f"same thread {pct(tot['same'], n)}, other thread {pct(tot['other'], n)}, "
          f"outside every thread {pct(tot['outside'], n)}")
    print("\n| read | thread | combinations | mean same | mean other | mean outside |")
    print("|--:|--:|--:|--:|--:|--:|")
    for (r, t), c in sorted(per_read.items(), key=lambda kv: -(kv[1]["same"] + kv[1]["other"] + kv[1]["outside"]) / kv[1]["n"])[:25]:
        k = c["n"]
        print(f"| {r} | {t} | {k} | {c['same']/k:.1f} | {c['other']/k:.1f} | {c['outside']/k:.1f} |")

print("\n## Reuse of a thread's enumeration across combinations\n")
print("| thread | combinations | distinct alternatives | distinct alternatives + predicates |")
print("|--:|--:|--:|--:|")
for t, ks in sorted(keys.items()):
    print(f"| {t} | {len(ks)} | {len(set(a for a, _ in ks))} | {len(set(p for _, p in ks))} |")

print("\n## Sampling\n")
if sampled:
    print(f"- combinations sampled: {len(sampled)}; tries: {sum(x[1] for x in sampled)}, "
          f"over budget: {sum(x[3] for x in sampled)}")
    print(f"- distinct valid relations found: {sum(s[0] for s in sampled)}; "
          f"combinations with none: {sum(1 for s in sampled if s[0] == 0)}")
    print(f"- complete relations tried: {sum(s[2] for s in sampled)}")

print("\n## Coherence (smrd)\n")
if coh:
    adm = sum(1 for c in coh if c[2])
    ms = [c[3] for c in coh]
    print(f"- executions checked: {len(coh)}; admitted: {adm} ({pct(adm, len(coh))})")
    print(f"- ms per check: median {statistics.median(ms):.0f}, p90 "
          f"{sorted(ms)[int(0.9 * (len(ms) - 1))]}, max {max(ms)}")
    print(f"- events: {min(c[0] for c in coh)}-{max(c[0] for c in coh)}; "
          f"rf edges: {min(c[1] for c in coh)}-{max(c[1] for c in coh)}")

stages = []
for line in lines:
    if m := re.match(r"S10 coherence-stages id=(\d+) model=(\S+) setup_ms=(\d+)\s+thin_air=(\w+) "
                     r"thin_air_ms=(\d+) search_ms=(\d+) admitted=(\w+)", line):
        stages.append((m[2], int(m[3]), m[4] == "true", int(m[5]), int(m[6]), m[7] == "true"))
if stages:
    print("\n## Coherence stages\n")
    for model in sorted(set(s[0] for s in stages)):
        ss = [s for s in stages if s[0] == model]
        ta_rej = sum(1 for s in ss if not s[2])
        co_rej = sum(1 for s in ss if s[2] and not s[5])
        adm = sum(1 for s in ss if s[5])
        med = lambda xs: statistics.median(xs) if xs else 0
        print(f"- {model}: {len(ss)} checked; admitted {adm}; rejected by thin-air {ta_rej}, "
              f"by the co search {co_rej}")
        print(f"  - median ms: setup (location equality, restriction, cache) "
              f"{med([s[1] for s in ss]):.0f}, thin-air {med([s[3] for s in ss]):.0f}, "
              f"co search {med([s[4] for s in ss if s[2]]):.0f}")

local = []
for line in lines:
    if m := re.match(r"S10 coherence-local id=(\d+) empty_ok=(\w+) locations=(\d+)\s+"
                     r"rejecting=(\d+) leaves=(\d+) \[(.*)\]", line):
        local.append((m[2] == "true", int(m[3]), int(m[4]), int(m[5]), m[6]))
if local:
    print("\n## Is the rejection local?\n")
    print(f"- executions: {len(local)}")
    print(f"- rejected with every location unordered (co = ∅): "
          f"{sum(1 for l in local if not l[0])}")
    print(f"- rejected by one location on its own: "
          f"{sum(1 for l in local if l[0] and l[2] > 0)}")
    print(f"- neither (needs orders at several locations together): "
          f"{sum(1 for l in local if l[0] and l[2] == 0)}")
    print(f"- co search leaves per execution: median "
          f"{statistics.median([l[3] for l in local]):.0f}, max {max(l[3] for l in local)}")
    print(f"- rejecting locations per locally rejected execution: "
          f"{Counter(l[2] for l in local if l[0] and l[2] > 0).most_common()}")

loc = []
for line in lines:
    if m := re.match(r"S10 local model=(\S+) reads=(\d+) full=(\w+) d_rf=(\S+) d_p=(\S+) "
                     r"cut_rf=(\S+) cut_p=(\S+)\s+total=([\d.]+) calls=(\d+) ms_per_call=(\d+)", line):
        opt = lambda x, f: None if x == "-" else f(x)
        loc.append(dict(reads=int(m[2]), full=m[3] == "true", d_rf=opt(m[4], int),
                        d_p=opt(m[5], int), cut_rf=opt(m[6], float), cut_p=opt(m[7], float),
                        total=float(m[8]), ms=int(m[10])))
if loc:
    print("\n## A per-location check during enumeration\n")
    n = len(loc)
    print(f"- sampled relations: {n}; rejected by one location, whole: "
          f"{sum(1 for l in loc if l['full'])}")
    for key, cut, label in (("d_rf", "cut_rf", "with the edges' predicates"),
                            ("d_p", "cut_p", "with the combination's predicates only")):
        hit = [l for l in loc if l[key] is not None]
        print(f"- {label}: rejected {len(hit)} of {n}")
        if hit:
            frac = [l[key] / l["reads"] for l in hit]
            print(f"  - rejected after a median {statistics.median([l[key] for l in hit]):.0f} "
                  f"of {statistics.median([l['reads'] for l in hit]):.0f} reads "
                  f"(median fraction {statistics.median(frac):.2f}, max {max(frac):.2f})")
            print(f"  - log10 of the choices below that point: median "
                  f"{statistics.median([l[cut] for l in hit]):.1f}, of a median total "
                  f"{statistics.median([l['total'] for l in hit]):.1f}")
    print(f"- ms per check: median {statistics.median([l['ms'] for l in loc]):.0f}, "
          f"max {max(l['ms'] for l in loc)}")

sound = Counter()
for line in lines:
    if m := re.match(r"S10 soundness model=(\S+) admitted=(\w+) local=(\w+)", line):
        sound[(m[1], m[2], m[3])] += 1
if sound:
    print("\n## Soundness: the per-location check against coherence\n")
    print("| model | admitted, not local | rejected, local | rejected, not local | **admitted, local** |")
    print("|---|--:|--:|--:|--:|")
    for model in sorted(set(k[0] for k in sound)):
        g = lambda a, l: sound[(model, a, l)]
        print(f"| {model} | {g('true','false')} | {g('false','true')} | {g('false','false')} | "
              f"**{g('true','true')}** |")
