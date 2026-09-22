#!/bin/bash
# One file: the S19 summary line (per-combination lines kept in a side file).
cd "$(git rev-parse --show-toplevel)"
B=${S19_BIN:-./_build/default/cli/main.exe}
f="$1"; side="$2"
out=$(MORDOR_S19=1 MORDOR_S19_COMPARE=1 timeout 600 $B futures --single "$f" --no-progress --allow-unknown-model 2>&1)
rc=$?
printf '%s\n' "$out" | grep "^S19 combo" | sed "s|^|$f\t|" >> "$side.$$"
line=$(printf '%s\n' "$out" | grep "^S19 summary")
if [ -n "$line" ]; then echo -e "$f\t$line"; else echo -e "$f\tNONE rc=$rc"; fi
