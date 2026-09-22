#!/bin/bash
# One file: the S14 lines, prefixed with the file, or a status if none came out.
cd "$(git rev-parse --show-toplevel)"
f="$1"
out=$(MORDOR_S14=1 timeout 300 ./_build/default/cli/main.exe futures --single "$f" --no-progress $S14_EXTRA 2>&1)
rc=$?
lines=$(printf '%s\n' "$out" | grep "^S14")
if [ -n "$lines" ]; then printf '%s\n' "$lines" | sed "s|^|$f\t|"; else echo -e "$f\tNONE rc=$rc"; fi
