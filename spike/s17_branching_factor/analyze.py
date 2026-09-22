#!/usr/bin/env python3
"""S17: survivors per depth from 'S17 combo' lines, and the rejection reasons.

Each 'S17 combo' line carries survivors_log10=v0,v1,...,vn: log10 of Knuth's
estimate of the partial relations of d reads that pass every check ('-' when
no probe reached depth d). Reports, over combinations, the median estimate per
depth, the per-depth branching factor (ratio of consecutive medians), where the
estimate peaks, and the reasons table.
"""
import re
import statistics
import sys
from collections import defaultdict


def main(path):
    per_depth = defaultdict(list)
    peaks, leaves, products, secs = [], [], [], []
    reasons = []
    for line in open(path):
        if "S17 combo" in line:
            m = re.search(r"survivors_log10=(\S+)", line)
            vals = [None if v == "-" else float(v) for v in m.group(1).split(",")]
            for d, v in enumerate(vals):
                per_depth[d].append(v)
            reached = [(v, d) for d, v in enumerate(vals) if v is not None]
            peaks.append(max(reached)[1] if reached else 0)
            lv = re.search(r"log10_leaves=(\S+)", line).group(1)
            leaves.append(None if lv in ("-inf", "inf") else float(lv))
            products.append(float(re.search(r"log10_product=(\S+)", line).group(1)))
            secs.append(float(re.search(r"secs=(\S+)", line).group(1)))
        elif "S17 reason" in line or "S17 rejections" in line:
            reasons.append(line.split("S17 ", 1)[1].strip())
    n = len(products)
    print(f"combinations: {n}")
    if not n:
        return
    print(f"log10 choice product, median: {statistics.median(products):.2f}")
    got = [x for x in leaves if x is not None]
    print(
        f"probes reaching a valid leaf: {len(got)} of {n} combinations; "
        f"log10 valid leaves, median where reached: "
        f"{statistics.median(got) if got else float('nan'):.2f}"
    )
    print(f"depth of the peak estimate, median: {statistics.median(peaks)}")
    print(f"secs per combination, median: {statistics.median(secs):.1f}")
    print("depth  reached  median log10 survivors  (with dead as -inf: share alive)  branching")
    prev = None
    for d in sorted(per_depth):
        vs = per_depth[d]
        alive = [v for v in vs if v is not None]
        med = statistics.median(alive) if alive else None
        b = "" if prev is None or med is None else f"{10 ** (med - prev):7.2f}"
        print(
            f"{d:5d}  {len(alive):7d}  "
            f"{'' if med is None else f'{med:22.2f}'}  {len(alive) / len(vs):9.2f}  {b}"
        )
        prev = med
    print("\nrejections:")
    for r in reasons:
        print("  " + r)


if __name__ == "__main__":
    main(sys.argv[1])
