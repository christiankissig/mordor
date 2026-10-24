#!/usr/bin/env bash
# The browser build's download (W6, #182): each file of wasm/dist.sh's DIST,
# raw and gzipped, as a Markdown table, and a check against a budget set from
# W4's measurements (#180): the files a page loads, gzipped, at most
# BUDGET_KB (default 6500; W4 measured about 5,300 KB: z3.wasm 5,100, the
# rest 200).
#
#   wasm/test/size.sh DIST [BUDGET_KB]
set -euo pipefail
DIST=$1 BUDGET_KB=${2:-6500}
total=0
echo '| file | bytes | gzipped |'
echo '|---|---:|---:|'
for f in "$DIST"/*; do
  raw=$(wc -c < "$f")
  gz=$(gzip -9 -c "$f" | wc -c)
  total=$((total + gz))
  echo "| $(basename "$f") | $raw | $gz |"
done
echo "| **total** | | **$total** |"
echo
if [ $((total / 1024)) -gt "$BUDGET_KB" ]; then
  echo "Over budget: $((total / 1024)) KB gzipped, budget $BUDGET_KB KB." | tee /dev/stderr
  exit 1
fi
echo "Within budget: $((total / 1024)) KB gzipped, budget $BUDGET_KB KB."
