#!/bin/bash
# S15 on rcu-2: one run per ordering. Args: step counter, budget secs, orderings...
cd "$(git rev-parse --show-toplevel)"
sc=$1; secs=$2; shift 2
out=${S15_OUT:-/tmp}
for order in "$@"; do
  f=$out/rcu2-sc$sc-$order
  MORDOR_S15=1 MORDOR_S15_ORDER=$order MORDOR_S15_SECS=$secs \
    /usr/bin/time -v ./_build/default/cli/main.exe futures --threads 16 \
      --step-counter-per-loop $sc --single programs/rcu-2.lit --no-progress \
      > $f.out 2> $f.err
  echo "$order rc=$? $(grep 'S15 summary' $f.err) wall=$(grep 'Elapsed (wall' $f.err | awk '{print $NF}') maxrss_kb=$(grep 'Maximum resident' $f.err | awk '{print $NF}')"
done
